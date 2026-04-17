import Again.FPM_Phase4_Examples
import Mathlib
-- Phase 5 Compiler
open Lean
open Lean.Meta
open Lean.Elab
open Lean.Elab.Tactic

/-!
  # Phase 5: Compiler Interface

  This is the final phase of the FPM rewrite engine.

  Phase 4 provided:
  - a registry of transport rules,
  - context-weakening and bridge lemmas,
  - an explicit prototype tactic.

  Phase 5 begins the actual compiler-facing layer:
  it inspects the goal, identifies the rewrite shape,
  and then dispatches to the appropriate Phase 4 machinery.
-/

/-
  ========================================================================
  SECTION 1: GOAL RECOGNITION
  We begin with the most conservative compiler task:
  detect whether the target is an `FPM_Eq` goal and extract its data.
  ========================================================================
-/

/-- Parsed view of an FPM equality goal. -/
structure FPMEqGoalView where
  ctx : Expr
  lhs : Expr
  rhs : Expr
  deriving Inhabited

/-- Try to read a target of the form `FPM_Eq ctx lhs rhs`. -/
def viewFPMEqTarget? (target : Expr) : MetaM (Option FPMEqGoalView) := do
  if target.getAppFn.isConstOf ``FPM_Eq then
    let args := target.getAppArgs
    if h : args.size = 3 then
      let ctx := args[0]
      let lhs := args[1]
      let rhs := args[2]
      return some { ctx := ctx, lhs := lhs, rhs := rhs }
    else
      return none
  else
    return none

/-- Read the main goal and parse it as an `FPM_Eq` target if possible. -/
def getFPMEqGoalView : TacticM FPMEqGoalView := do
  let target ← getMainTarget
  let some v ← liftMetaM <| viewFPMEqTarget? target
    | throwError
        "fpm compiler: target is not of the form `FPM_Eq ctx lhs rhs`"
  return v

/-
  ========================================================================
  SANITY CHECK TACTICS
  These are temporary diagnostics for early compiler development.
  ========================================================================
-/

elab "fpm_goal_check" : tactic => do
  let v ← getFPMEqGoalView
  logInfo m!"[fpm] recognized FPM_Eq goal"
  logInfo m!"[fpm] ctx := {v.ctx}"
  logInfo m!"[fpm] lhs := {v.lhs}"
  logInfo m!"[fpm] rhs := {v.rhs}"

/-
  ========================================================================
  SANITY CHECKS
  ========================================================================
-/

example : ∀ (ctx : _root_.Context) (a b : FPM_Real), FPM_Eq ctx a b → FPM_Eq ctx a b := by
  intro ctx a b h
  fpm_goal_check
  exact h

/-
  ========================================================================
  SECTION 2: OPERATOR CLASSIFICATION
  We classify the outer shape of the left-hand and right-hand sides of an
  `FPM_Eq` goal before attempting any rewrite dispatch.
  ========================================================================
-/

def getNarySumArgs? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  let e ← instantiateMVars e
  let e := e.consumeMData
  let fn := e.getAppFn
  let args := e.getAppArgs
  if fn.isConstOf ``FPM_sum_nary then
    if h : args.size = 2 then
      return some (args[0]!, args[1]!)
    else
      return none
  else
    return none

def isNarySumExpr (e : Expr) : MetaM Bool := do
  match ← getNarySumArgs? e with
  | some _ => pure true
  | none   => pure false


inductive FPMGoalShape where
  | neg
  | unary
  | add
  | mul
  | inv
  | naryAdd
  | unknown
  deriving Repr, Inhabited

def classifyFPMExprPair (lhs rhs : Expr) : MetaM FPMGoalShape := do
  let lhsFn := lhs.getAppFn
  let rhsFn := rhs.getAppFn
  if lhsFn.isConstOf ``Neg.neg && rhsFn.isConstOf ``Neg.neg then
    return .neg
  if lhsFn.isConstOf ``FPM_UnaryApply && rhsFn.isConstOf ``FPM_UnaryApply then
    return .unary
  if lhsFn.isConstOf ``HAdd.hAdd && rhsFn.isConstOf ``HAdd.hAdd then
    return .add
  if lhsFn.isConstOf ``HMul.hMul && rhsFn.isConstOf ``HMul.hMul then
    return .mul
  if lhsFn.isConstOf ``Inv.inv && rhsFn.isConstOf ``Inv.inv then
    return .inv
  if (← isNarySumExpr lhs) && (← isNarySumExpr rhs) then
    return .naryAdd
  return .unknown

def getFPMGoalShape : TacticM FPMGoalShape := withMainContext do
  let v ← getFPMEqGoalView
  classifyFPMExprPair v.lhs v.rhs

elab "fpm_classify_goal" : tactic => do
  let sh ← getFPMGoalShape
  logInfo m!"[fpm] goal shape := {repr sh}"

example (ctx : _root_.Context) (a₁ a₂ : FPM_Real)
    (h : FPM_Eq ctx (-a₁) (-a₂)) :
    FPM_Eq ctx (-a₁) (-a₂) := by
  fpm_classify_goal
  exact h

example (ctx : _root_.Context) (a₁ a₂ b₁ b₂ : FPM_Real)
    (h : FPM_Eq ctx (a₁ + b₁) (a₂ + b₂)) :
    FPM_Eq ctx (a₁ + b₁) (a₂ + b₂) := by
  fpm_classify_goal
  exact h

example (ctx : _root_.Context) (a₁ a₂ b₁ b₂ : FPM_Real)
    (h : FPM_Eq ctx (a₁ * b₁) (a₂ * b₂)) :
    FPM_Eq ctx (a₁ * b₁) (a₂ * b₂) := by
  fpm_classify_goal
  exact h

example (ctx : _root_.Context) (a₁ a₂ : FPM_Real)
    (h : FPM_Eq ctx (a₁⁻¹) (a₂⁻¹)) :
    FPM_Eq ctx (a₁⁻¹) (a₂⁻¹) := by
  fpm_classify_goal
  exact h

example (ctx : _root_.Context) (n : ℕ+) (v w : Fin n.val → FPM_Real)
    (h : FPM_Eq ctx (FPM_sum_nary v) (FPM_sum_nary w)) :
    FPM_Eq ctx (FPM_sum_nary v) (FPM_sum_nary w) := by
  fpm_classify_goal
  exact h
/-
  ========================================================================
  SECTION 3: LOCAL HYPOTHESIS SCANNING
  We scan the local context for hypotheses of the form

      FPM_Eq ctx lhs rhs

  and record their user names plus the three arguments.
  ========================================================================
-/

open Lean Meta Elab Tactic

structure FPMEqHypView where
  fvarId : FVarId
  userName : Name
  idxType  : Expr
  ctx      : Expr
  lhs      : Expr
  rhs      : Expr
  deriving Inhabited

def matchFPMEqTypeCore? (ty : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  if ty.getAppFn.isConstOf ``FPM_Eq then
    let args := ty.getAppArgs
    if h : args.size = 3 then
      return some (args[0]!, args[1]!, args[2]!)
    else
      return none
  else
    return none

def matchFPMEqType? (ty : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  let ty ← instantiateMVars ty
  match ← matchFPMEqTypeCore? ty with
  | some v => return some v
  | none =>
      let ty' ← whnf ty
      matchFPMEqTypeCore? ty'

def matchFPMEqFamilyTypeCore? (ty : Expr) : MetaM (Option (Expr × Expr × Expr × Expr)) := do
  forallTelescope ty fun xs body => do
    if h : xs.size = 1 then
      let i := xs[0]!
      match ← matchFPMEqType? body with
      | some (ctx, lhs, rhs) =>
          let lhs ← mkLambdaFVars #[i] lhs
          let rhs ← mkLambdaFVars #[i] rhs
          let idxTy  ← inferType i
          return some (idxTy, ctx, lhs, rhs)
      | none =>
          return none
    else
      return none



def getLocalFPMEqHyps : TacticM (Array FPMEqHypView) := withMainContext do
  let lctx ← getLCtx
  let mut out : Array FPMEqHypView := #[]
  for decl in lctx do
    if decl.isImplementationDetail then
      continue
    match ← matchFPMEqFamilyTypeCore? decl.type with
    | some (idxType, ctx, lhs, rhs) =>
        out := out.push
          { fvarId   := decl.fvarId
            userName := decl.userName
            idxType  := idxType
            ctx      := ctx
            lhs      := lhs
            rhs      := rhs }
    | none =>
        match ← matchFPMEqType? decl.type with
        | some (ctx, lhs, rhs) =>
            out := out.push
              { fvarId   := decl.fvarId
                userName := decl.userName
                idxType  := mkConst ``PUnit
                ctx      := ctx
                lhs      := lhs
                rhs      := rhs }
        | none =>
            pure ()
  return out

elab "fpm_scan_hyps" : tactic => do
  let hyps ← getLocalFPMEqHyps
  if hyps.isEmpty then
    logInfo "[fpm] no local FPM_Eq hypotheses found"
  else
    for h in hyps do
      logInfo m!"[fpm] hyp := {h.userName}"
      logInfo m!"fpm idxType {h.idxType}"
      logInfo m!"[fpm]   ctx := {h.ctx}"
      logInfo m!"[fpm]   lhs := {h.lhs}"
      logInfo m!"[fpm]   rhs := {h.rhs}"

/-- Diagnostic example: demonstrates `fpm_scan_hyps` scanning.
    The hypotheses are at `ctx` (not at the required shifted context),
    so the goal cannot be closed by transport. The `sorry` is intentional
    — this example only tests the scanning infrastructure. -/
example (ctx : _root_.Context)
    (a₁ a₂ b₁ b₂ : FPM_Real)
    (h1 : FPM_Eq ctx a₁ a₂)
    (h2 : FPM_Eq ctx b₁ b₂) :
    FPM_Eq ctx (a₁ + b₁) (a₂ + b₂) := by
  fpm_scan_hyps
  exact by
    sorry

/-
  ========================================================================
  SECTION 4: DIAGNOSTIC MATCHING
  We try to match the current FPM_Eq goal against local FPM_Eq hypotheses.

  For now this is intentionally conservative:
  - same context only
  - direct orientation only
  - no theorem application yet
  ========================================================================
-/

open Lean Meta Elab Tactic

def exprDefEq (e₁ e₂ : Expr) : MetaM Bool := do
  let e₁ ← instantiateMVars e₁
  let e₂ ← instantiateMVars e₂
  withNewMCtxDepth <| isDefEq e₁ e₂

def getUnaryArgIf (head : Name) (e : Expr) : MetaM (Option Expr) := do
  let e ← instantiateMVars e
  let e := e.consumeMData
  let fn := e.getAppFn
  let args := e.getAppArgs
  if fn.isConstOf head && args.size > 0 then
    return some (args[args.size - 1]!)
  else
    return none

def getBinaryArgsIf (head : Name) (e : Expr) : MetaM (Option (Expr × Expr)) := do
  let e ← instantiateMVars e
  let e := e.consumeMData
  let fn := e.getAppFn
  let args := e.getAppArgs
  if fn.isConstOf head && args.size >= 2 then
    return some (args[args.size - 2]!, args[args.size - 1]!)
  else
    return none

def findUnarySupport
    (head : Name) (gctx lhs rhs : Expr) (hyps : Array FPMEqHypView) :
    MetaM (Option FPMEqHypView) := do
  let some lhsArg ← getUnaryArgIf head lhs | return none
  let some rhsArg ← getUnaryArgIf head rhs | return none
  for h in hyps do
    if ← exprDefEq h.ctx gctx then
      if ← exprDefEq h.lhs lhsArg then
        if ← exprDefEq h.rhs rhsArg then
          return some h
  return none

def findBinarySupport
    (head : Name) (gctx lhs rhs : Expr) (hyps : Array FPMEqHypView) :
    MetaM (Option (FPMEqHypView × FPMEqHypView)) := do
  let some (lhs₁, lhs₂) ← getBinaryArgsIf head lhs | return none
  let some (rhs₁, rhs₂) ← getBinaryArgsIf head rhs | return none
  for h1 in hyps do
    for h2 in hyps do
      if h1.fvarId != h2.fvarId then
        if ← exprDefEq h1.ctx gctx then
          if ← exprDefEq h2.ctx gctx then
            if ← exprDefEq h1.lhs lhs₁ then
              if ← exprDefEq h1.rhs rhs₁ then
                if ← exprDefEq h2.lhs lhs₂ then
                  if ← exprDefEq h2.rhs rhs₂ then
                    return some (h1, h2)
  return none

--nary
def mkPNatVal (n : Expr) : MetaM Expr := do
  mkAppM ``PNat.val #[n]

def mkNaryAddOp (n : Expr) : MetaM Expr := do
  let nNat ← mkPNatVal n
  mkAppM ``FPM_AddNary #[nNat]

def mkNaryAddShiftCtx (ctx n : Expr) : MetaM Expr := do
  let F ← mkNaryAddOp n
  mkAppM ``shift_context_nary #[ctx, n, F]
def mkFinTypeFromPNat (n : Expr) : MetaM Expr := do
  let nNat ← mkPNatVal n
  mkAppM ``Fin #[nNat]

def mkEtaFamilyAt (idxTy f : Expr) : MetaM Expr := do
  withLocalDeclD `i idxTy fun i => do
    mkLambdaFVars #[i] (mkAppN f #[i])

def mkEtaFamily (n fam : Expr) : MetaM Expr := do
  let finTy ← mkFinTypeFromPNat n
  withLocalDeclD `i finTy fun i => do
    mkLambdaFVars #[i] (mkAppN fam #[i])

def getNaryFamilyArgs? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  let some (n, fam) ← getNarySumArgs? e | return none
  let famEta ← mkEtaFamily n fam
  return some (n, famEta)

def findNaryAddSupportSameCtx
    (gctx lhs rhs : Expr)
    (hyps : Array FPMEqHypView) :
    MetaM (Option FPMEqHypView) := do
  let some (nL, v) ← getNarySumArgs? lhs | return none
  let some (nR, w) ← getNarySumArgs? rhs | return none
  if !(← exprDefEq nL nR) then
    return none
  for h in hyps do
    if ← exprDefEq h.ctx gctx then
      let etaV ← mkEtaFamilyAt h.idxType v
      let etaW ← mkEtaFamilyAt h.idxType w
      if ← exprDefEq h.lhs etaV then
        if ← exprDefEq h.rhs etaW then
          return some h
  return none

elab "fpm_match_goal" : tactic => do
  let g ← getFPMEqGoalView
  let sh ← getFPMGoalShape
  let hyps ← getLocalFPMEqHyps
  match sh with
  | .neg =>
      match ← findUnarySupport ``Neg.neg g.ctx g.lhs g.rhs hyps with
      | some h =>
          logInfo m!"[fpm] matched neg with hypothesis {h.userName}"
      | none =>
          logInfo "[fpm] no matching neg hypothesis found"
  | .inv =>
      match ← findUnarySupport ``Inv.inv g.ctx g.lhs g.rhs hyps with
      | some h =>
          logInfo m!"[fpm] matched inv with hypothesis {h.userName}"
      | none =>
          logInfo "[fpm] no matching inv hypothesis found"
  | .add =>
      match ← findBinarySupport ``HAdd.hAdd g.ctx g.lhs g.rhs hyps with
      | some (h1, h2) =>
          logInfo m!"[fpm] matched add with hypotheses {h1.userName} and {h2.userName}"
      | none =>
          logInfo "[fpm] no matching add hypotheses found"
  | .mul =>
      match ← findBinarySupport ``HMul.hMul g.ctx g.lhs g.rhs hyps with
      | some (h1, h2) =>
          logInfo m!"[fpm] matched mul with hypotheses {h1.userName} and {h2.userName}"
      | none =>
          logInfo "[fpm] no matching mul hypotheses found"
  | .unary =>
      logInfo "[fpm] unary goal detected, but unary matcher is not implemented yet"
  | .naryAdd =>
      match ← findNaryAddSupportSameCtx g.ctx g.lhs g.rhs hyps with
      | some h =>
          logInfo m!"[fpm] matched naryAdd with hypothesis {h.userName}"
      | none =>
          logInfo "[fpm] no matching naryAdd hypothesis found"
  | .unknown =>
      logInfo "[fpm] goal shape is unknown, so no matcher was attempted"

/-- Diagnostic example: demonstrates `fpm_match_goal` matching.
    The hypotheses are at `ctx` (not at the required shifted context),
    so the goal cannot be closed by transport. The `sorry` is intentional
    — this example only tests the matching infrastructure. -/
example (ctx : _root_.Context)
    (a₁ a₂ b₁ b₂ : FPM_Real)
    (h1 : FPM_Eq ctx a₁ a₂)
    (h2 : FPM_Eq ctx b₁ b₂) :
    FPM_Eq ctx (a₁ + b₁) (a₂ + b₂) := by
  fpm_match_goal
  exact by
    sorry

/-
  ========================================================================
  SECTION 5: THEOREM DISPATCH
  Compiler-facing dispatchers for exact shifted-context rules, weakened
  rules, and guarded direct rules.
  ========================================================================
-/

/-!
  Layout:
  1. Shared expression readers
  2. Direct dispatch support + proof builders
  3. Main exact dispatcher
  4. Weakened-context dispatchers
  5. Guarded direct dispatchers
  6. Examples
-/

/- ========================================================================
   5.1 Shared expression readers
   Small utilities used by several dispatchers.
   ======================================================================== -/

/-- Read an expression of the form `FPM_UnaryApply F a`. -/
def getFPMUnaryApplyArgs? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  let e ← instantiateMVars e
  let e := e.consumeMData
  let fn := e.getAppFn
  let args := e.getAppArgs
  if fn.isConstOf ``FPM_UnaryApply && args.size == 2 then
    return some (args[0]!, args[1]!)
  else
    return none


/- ========================================================================
   5.2 Direct dispatch: exact shifted-context rules
   These are the core matchers used by `fpm_dispatch`.
   ======================================================================== -/

/- -- Addition ------------------------------------------------------------ -/

/-- The exact shifted context required by direct addition transport. -/
def mkAddShiftCtx (ctx : Expr) : MetaM Expr := do
  mkAppM ``shift_context_bin #[ctx, mkConst ``FPM_Add]

/-- Match an addition goal against two local hypotheses at the exact
    shifted addition context. -/
def findAddSupportDirect
    (gctx lhs rhs : Expr) (hyps : Array FPMEqHypView) :
    MetaM (Option (FPMEqHypView × FPMEqHypView)) := do
  let some (lhs₁, lhs₂) ← getBinaryArgsIf ``HAdd.hAdd lhs | return none
  let some (rhs₁, rhs₂) ← getBinaryArgsIf ``HAdd.hAdd rhs | return none
  let wantCtx ← mkAddShiftCtx gctx
  for h1 in hyps do
    for h2 in hyps do
      if h1.fvarId != h2.fvarId then
        if ← exprDefEq h1.ctx wantCtx then
          if ← exprDefEq h2.ctx wantCtx then
            if ← exprDefEq h1.lhs lhs₁ then
              if ← exprDefEq h1.rhs rhs₁ then
                if ← exprDefEq h2.lhs lhs₂ then
                  if ← exprDefEq h2.rhs rhs₂ then
                    return some (h1, h2)
  return none

/-- Build the proof term for direct addition transport. -/
def mkAddDispatchProof
    (g : FPMEqGoalView)
    (h1 h2 : FPMEqHypView) : TacticM Expr := withMainContext do
  let lhsArgs := g.lhs.getAppArgs
  let rhsArgs := g.rhs.getAppArgs
  if lhsArgs.size < 2 || rhsArgs.size < 2 then
    throwError "[fpm] add goal did not expose two arguments"
  mkAppM ``FPM_Add_Substitution
    #[g.ctx,
      lhsArgs[lhsArgs.size - 2]!,
      rhsArgs[rhsArgs.size - 2]!,
      lhsArgs[lhsArgs.size - 1]!,
      rhsArgs[rhsArgs.size - 1]!,
      mkFVar h1.fvarId,
      mkFVar h2.fvarId]

/- -- Negation ------------------------------------------------------------ -/

/-- The exact shifted context required by direct negation transport. -/
def mkNegShiftCtx (ctx : Expr) : MetaM Expr := do
  mkAppM ``shift_context_unary #[ctx, mkConst ``FPM_Neg]

/-- Match a negation goal against one local hypothesis at the exact
    shifted negation context. -/
def findNegSupportDirect
    (gctx lhs rhs : Expr) (hyps : Array FPMEqHypView) :
    MetaM (Option FPMEqHypView) := do
  let some lhsArg ← getUnaryArgIf ``Neg.neg lhs | return none
  let some rhsArg ← getUnaryArgIf ``Neg.neg rhs | return none
  let wantCtx ← mkNegShiftCtx gctx
  for h in hyps do
    if ← exprDefEq h.ctx wantCtx then
      if ← exprDefEq h.lhs lhsArg then
        if ← exprDefEq h.rhs rhsArg then
          return some h
  return none

/-- Build the proof term for direct negation transport. -/
def mkNegDispatchProof
    (g : FPMEqGoalView)
    (h : FPMEqHypView) : TacticM Expr := withMainContext do
  let lhsArgs := g.lhs.getAppArgs
  let rhsArgs := g.rhs.getAppArgs
  if lhsArgs.isEmpty || rhsArgs.isEmpty then
    throwError "[fpm] neg goal did not expose one argument"
  mkAppM ``FPM_Unary_Substitution
    #[g.ctx,
      mkConst ``FPM_Neg,
      lhsArgs[lhsArgs.size - 1]!,
      rhsArgs[rhsArgs.size - 1]!,
      mkFVar h.fvarId]

/- -- Generic unary ------------------------------------------------------- -/

/-- The exact shifted context required by direct unary transport. -/
def mkUnaryShiftCtx (ctx F : Expr) : MetaM Expr := do
  mkAppM ``shift_context_unary #[ctx, F]

/-- Match a generic unary goal against one local hypothesis at the exact
    shifted unary context. Returns the operator and the supporting proof. -/
def findUnarySupportDirect
    (gctx lhs rhs : Expr) (hyps : Array FPMEqHypView) :
    MetaM (Option (Expr × FPMEqHypView)) := do
  let some (F₁, lhsArg) ← getFPMUnaryApplyArgs? lhs | return none
  let some (F₂, rhsArg) ← getFPMUnaryApplyArgs? rhs | return none
  if !(← exprDefEq F₁ F₂) then
    return none
  let wantCtx ← mkUnaryShiftCtx gctx F₁
  for h in hyps do
    if ← exprDefEq h.ctx wantCtx then
      if ← exprDefEq h.lhs lhsArg then
        if ← exprDefEq h.rhs rhsArg then
          return some (F₁, h)
  return none

/-- Build the proof term for direct unary transport. -/
def mkUnaryDispatchProof
    (g : FPMEqGoalView)
    (F : Expr)
    (h : FPMEqHypView) : TacticM Expr := withMainContext do
  let some (_, lhsArg) ← getFPMUnaryApplyArgs? g.lhs
    | throwError "[fpm] unary lhs is not of the form `FPM_UnaryApply F a`"
  let some (_, rhsArg) ← getFPMUnaryApplyArgs? g.rhs
    | throwError "[fpm] unary rhs is not of the form `FPM_UnaryApply F a`"
  mkAppM ``FPM_Unary_Substitution
    #[g.ctx, F, lhsArg, rhsArg, mkFVar h.fvarId]


/- -- Nary ------------------------------------------------------------ -/

def findNaryAddSupportDirect
    (gctx lhs rhs : Expr)
    (hyps : Array FPMEqHypView) :
    MetaM (Option FPMEqHypView) := do
  let some (nL, v) ← getNarySumArgs? lhs | return none
  let some (nR, w) ← getNarySumArgs? rhs | return none
  if !(← exprDefEq nL nR) then
    return none
  let wantCtx ← mkNaryAddShiftCtx gctx nL
  for h in hyps do
    if ← exprDefEq h.ctx wantCtx then
      let etaV ← mkEtaFamilyAt h.idxType v
      let etaW ← mkEtaFamilyAt h.idxType w
      if ← exprDefEq h.lhs etaV then
        if ← exprDefEq h.rhs etaW then
          return some h
  return none

def mkNaryAddDispatchProof
    (g : FPMEqGoalView)
    (h : FPMEqHypView) :
    TacticM Expr := withMainContext do
  let some (nL, v) ← getNarySumArgs? g.lhs
    | throwError "fpm naryAdd lhs is not of the form FPM_sum_nary v"
  let some (nR, w) ← getNarySumArgs? g.rhs
    | throwError "fpm naryAdd rhs is not of the form FPM_sum_nary w"
  unless ← exprDefEq nL nR do
    throwError "fpm naryAdd goal has mismatched index objects on lhs/rhs"
  mkAppM ``FPM_NaryAdd_Substitution #[g.ctx, v, w, mkFVar h.fvarId]

/- ========================================================================
   5.3 Main exact dispatcher
   This handles the exact shifted-context rules only.
   ======================================================================== -/

elab "fpm_dispatch" : tactic => withMainContext do
  let g ← getFPMEqGoalView
  let sh ← getFPMGoalShape
  let hyps ← getLocalFPMEqHyps
  match sh with
  | .add =>
      match ← findAddSupportDirect g.ctx g.lhs g.rhs hyps with
      | some (h1, h2) =>
          let pf ← mkAddDispatchProof g h1 h2
          closeMainGoal `fpm_dispatch pf
      | none =>
          throwError
            "[fpm] no matching add hypotheses at shifted addition context found"
  | .neg =>
      match ← findNegSupportDirect g.ctx g.lhs g.rhs hyps with
      | some h =>
          let pf ← mkNegDispatchProof g h
          closeMainGoal `fpm_dispatch pf
      | none =>
          throwError
            "[fpm] no matching neg hypothesis at shifted negation context found"
  | .unary =>
      match ← findUnarySupportDirect g.ctx g.lhs g.rhs hyps with
      | some (F, h) =>
          let pf ← mkUnaryDispatchProof g F h
          closeMainGoal `fpm_dispatch pf
      | none =>
          throwError
            "[fpm] no matching unary hypothesis at shifted unary context found"
  | .naryAdd =>
      match ← findNaryAddSupportDirect g.ctx g.lhs g.rhs hyps with
      | some h =>
          let pf ← mkNaryAddDispatchProof g h
          closeMainGoal `fpm_dispatch pf
      | none =>
          throwError "fpm no matching nary-add family hypothesis at shifted nary context found"
  | .mul =>
      throwError "[fpm] mul dispatch not implemented in `fpm_dispatch`; use `fpm_dispatch_mul`"
  | .inv =>
      throwError "[fpm] inv dispatch not implemented in `fpm_dispatch`; use `fpm_dispatch_inv`"
  | .unknown =>
      throwError "[fpm] goal shape is unknown"

/- ========================================================================
   5.4 Weakened-context dispatchers
   These match the goal shape first, then use user-supplied comparison
   proofs to feed the `_of_weaker` theorems.
   ======================================================================== -/

/- -- Addition from stronger hypotheses ---------------------------------- -/

/-- Match an addition goal against two local hypotheses, ignoring context.
    The context comparison is supplied separately by the user. -/
def findAddSupportFrom
    (lhs rhs : Expr) (hyps : Array FPMEqHypView) :
    MetaM (Option (FPMEqHypView × FPMEqHypView)) := do
  let some (lhs₁, lhs₂) ← getBinaryArgsIf ``HAdd.hAdd lhs | return none
  let some (rhs₁, rhs₂) ← getBinaryArgsIf ``HAdd.hAdd rhs | return none
  for h1 in hyps do
    for h2 in hyps do
      if h1.fvarId != h2.fvarId then
        if ← exprDefEq h1.lhs lhs₁ then
          if ← exprDefEq h1.rhs rhs₁ then
            if ← exprDefEq h2.lhs lhs₂ then
              if ← exprDefEq h2.rhs rhs₂ then
                return some (h1, h2)
  return none

syntax "fpm_dispatch_add_from"
  "(" ident "," ident "," ident "," ident ")" : tactic

elab_rules : tactic
  | `(tactic| fpm_dispatch_add_from($hMA:ident, $hNA:ident, $hMB:ident, $hNB:ident)) => withMainContext do
      let g ← getFPMEqGoalView
      let sh ← getFPMGoalShape
      let hyps ← getLocalFPMEqHyps
      match sh with
      | .add =>
          match ← findAddSupportFrom g.lhs g.rhs hyps with
          | some (h1, h2) =>
              Lean.Elab.Tactic.evalTactic (← `(tactic|
                exact FPM_Add_Substitution_of_weaker
                  _ _ _ _ _ _ _
                  $hMA $hNA $hMB $hNB
                  $(mkIdent h1.userName) $(mkIdent h2.userName)
              ))
          | none =>
              throwError "[fpm] no matching add hypotheses found for add_from"
      | _ =>
          throwError "[fpm] add_from only applies to addition goals"

/- -- Generic unary from stronger hypotheses ------------------------------ -/

/-- Match a generic unary goal against one local hypothesis, ignoring context.
    The context comparison is supplied separately by the user. -/
def findUnarySupportFrom
    (lhs rhs : Expr) (hyps : Array FPMEqHypView) :
    MetaM (Option (Expr × FPMEqHypView)) := do
  let some (F₁, lhsArg) ← getFPMUnaryApplyArgs? lhs | return none
  let some (F₂, rhsArg) ← getFPMUnaryApplyArgs? rhs | return none
  if !(← exprDefEq F₁ F₂) then
    return none
  for h in hyps do
    if ← exprDefEq h.lhs lhsArg then
      if ← exprDefEq h.rhs rhsArg then
        return some (F₁, h)
  return none

/-- Build the proof term for weakened generic unary transport. -/
def mkUnaryFromDispatchProof
    (g : FPMEqGoalView)
    (F : Expr)
    (h : FPMEqHypView)
    (hM hN : Expr) : TacticM Expr := withMainContext do
  let some (_, lhsArg) ← getFPMUnaryApplyArgs? g.lhs
    | throwError "[fpm] unary lhs is not of the form `FPM_UnaryApply F a`"
  let some (_, rhsArg) ← getFPMUnaryApplyArgs? g.rhs
    | throwError "[fpm] unary rhs is not of the form `FPM_UnaryApply F a`"
  mkAppM ``FPM_Unary_Substitution_of_weaker
    #[g.ctx,
      F,
      h.ctx,
      lhsArg,
      rhsArg,
      hM,
      hN,
      mkFVar h.fvarId]

syntax "fpm_dispatch_unary_from"
  "(" ident "," ident ")" : tactic

elab_rules : tactic
  | `(tactic| fpm_dispatch_unary_from($hM:ident, $hN:ident)) => withMainContext do
      let g ← getFPMEqGoalView
      let sh ← getFPMGoalShape
      let hyps ← getLocalFPMEqHyps
      match sh with
      | .unary =>
          match ← findUnarySupportFrom g.lhs g.rhs hyps with
          | some (F, h) =>
              let pf ← mkUnaryFromDispatchProof
                g F h (mkFVar (← getFVarId hM)) (mkFVar (← getFVarId hN))
              closeMainGoal `fpm_dispatch_unary_from pf
          | none =>
              throwError "[fpm] no matching unary hypothesis found for unary_from"
      | _ =>
          throwError "[fpm] unary_from only applies to generic unary goals"

/- -- Generic nary from stronger hypotheses ------------------------------ -/
def findNaryAddSupportFrom
    (lhs rhs : Expr)
    (hyps : Array FPMEqHypView) :
    MetaM (Option FPMEqHypView) := do
  let some (nL, v) ← getNarySumArgs? lhs | return none
  let some (nR, w) ← getNarySumArgs? rhs | return none
  if !(← exprDefEq nL nR) then
    return none
  for h in hyps do
    let etaV ← mkEtaFamilyAt h.idxType v
    let etaW ← mkEtaFamilyAt h.idxType w
    if ← exprDefEq h.lhs etaV then
      if ← exprDefEq h.rhs etaW then
        return some h
  return none

def mkNaryAddFromDispatchProof
    (g : FPMEqGoalView)
    (h : FPMEqHypView)
    (hM hN : Expr) :
    TacticM Expr := withMainContext do
  let some (nL, v) ← getNaryFamilyArgs? g.lhs
    | throwError "fpm naryAdd lhs is not of the form FPM_sum_nary v"
  let some (nR, w) ← getNaryFamilyArgs? g.rhs
    | throwError "fpm naryAdd rhs is not of the form FPM_sum_nary w"
  unless ← exprDefEq nL nR do
    throwError "fpm naryAdd goal has mismatched index objects on lhs/rhs"
  mkAppM ``FPM_NaryAdd_Substitution_of_weaker
    #[g.ctx, h.ctx, nL, v, w, hM, hN, mkFVar h.fvarId]

syntax "fpmdispatchnaryfrom "
  "(" ident "," ident ")" : tactic

elab_rules : tactic
| `(tactic| fpmdispatchnaryfrom($hM:ident, $hN:ident)) => withMainContext do
    let g ← getFPMEqGoalView
    let sh ← getFPMGoalShape
    let hyps ← getLocalFPMEqHyps
    match sh with
    | .naryAdd =>
        match ← findNaryAddSupportFrom g.lhs g.rhs hyps with
        | some h =>
            let pf ← mkNaryAddFromDispatchProof
              g h
              (mkFVar (← getFVarId hM))
              (mkFVar (← getFVarId hN))
            closeMainGoal `fpmdispatchnaryfrom pf
        | none =>
            throwError "fpm no matching nary-add family hypothesis found for naryfrom"
    | _ =>
        throwError "fpm naryfrom only applies to nary-add goals"

/- ========================================================================
   5.5 Guarded direct dispatchers
   These require extra side data in addition to matched support proofs.
   ======================================================================== -/

/- -- Multiplication direct ---------------------------------------------- -/

/-- The exact shifted context required by direct multiplication transport. -/
def mkMulShiftCtx (ctx C : Expr) : MetaM Expr := do
  mkAppM ``shift_context_mul #[ctx, C]

/-- Match a multiplication goal against two local hypotheses at the exact
    shifted multiplication context. -/
def findMulSupportDirect
    (gctx C lhs rhs : Expr) (hyps : Array FPMEqHypView) :
    MetaM (Option (FPMEqHypView × FPMEqHypView)) := do
  let some (lhs₁, lhs₂) ← getBinaryArgsIf ``HMul.hMul lhs | return none
  let some (rhs₁, rhs₂) ← getBinaryArgsIf ``HMul.hMul rhs | return none
  let wantCtx ← mkMulShiftCtx gctx C
  for h1 in hyps do
    for h2 in hyps do
      if h1.fvarId != h2.fvarId then
        if ← exprDefEq h1.ctx wantCtx then
          if ← exprDefEq h2.ctx wantCtx then
            if ← exprDefEq h1.lhs lhs₁ then
              if ← exprDefEq h1.rhs rhs₁ then
                if ← exprDefEq h2.lhs lhs₂ then
                  if ← exprDefEq h2.rhs rhs₂ then
                    return some (h1, h2)
  return none

/-- Build the proof term for direct multiplication transport. -/
def mkMulDispatchProof
    (g : FPMEqGoalView)
    (C ha₁ hb₂ : Expr)
    (h1 h2 : FPMEqHypView) : TacticM Expr := withMainContext do
  let lhsArgs := g.lhs.getAppArgs
  let rhsArgs := g.rhs.getAppArgs
  if lhsArgs.size < 2 || rhsArgs.size < 2 then
    throwError "[fpm] mul goal did not expose two arguments"
  mkAppM ``FPM_Mul_Substitution
    #[g.ctx,
      C,
      lhsArgs[lhsArgs.size - 2]!,
      rhsArgs[rhsArgs.size - 2]!,
      lhsArgs[lhsArgs.size - 1]!,
      rhsArgs[rhsArgs.size - 1]!,
      ha₁,
      hb₂,
      mkFVar h1.fvarId,
      mkFVar h2.fvarId]

syntax "fpm_dispatch_mul"
  "(" term "," ident "," ident ")" : tactic

elab_rules : tactic
  | `(tactic| fpm_dispatch_mul($C, $ha₁:ident, $hb₂:ident)) => withMainContext do
      let g ← getFPMEqGoalView
      let sh ← getFPMGoalShape
      let hyps ← getLocalFPMEqHyps
      let CExpr ← elabTerm C none
      match sh with
      | .mul =>
          match ← findMulSupportDirect g.ctx CExpr g.lhs g.rhs hyps with
          | some (h1, h2) =>
              let pf ← mkMulDispatchProof
                g
                CExpr
                (mkFVar (← getFVarId ha₁))
                (mkFVar (← getFVarId hb₂))
                h1 h2
              closeMainGoal `fpm_dispatch_mul pf
          | none =>
              throwError
                "[fpm] no matching mul hypotheses at shifted multiplication context found"
      | _ =>
          throwError "[fpm] mul_direct only applies to multiplication goals"

/- -- Inversion direct --------------------------------------------------- -/

/-- The exact shifted context required by direct inversion transport. -/
def mkInvShiftCtx (ctx L N_safe : Expr) : MetaM Expr := do
  mkAppM ``shift_context_inv_subst #[ctx, L, N_safe]

/-- Match an inversion goal against one local hypothesis at the exact
    shifted inversion context, using the explicit base context. -/
def findInvSupportDirect
    (baseCtx L N_safe lhs rhs : Expr) (hyps : Array FPMEqHypView) :
    MetaM (Option FPMEqHypView) := do
  let some lhsArg ← getUnaryArgIf ``Inv.inv lhs | return none
  let some rhsArg ← getUnaryArgIf ``Inv.inv rhs | return none
  let wantCtx ← mkInvShiftCtx baseCtx L N_safe
  for h in hyps do
    if ← exprDefEq h.ctx wantCtx then
      if ← exprDefEq h.lhs lhsArg then
        if ← exprDefEq h.rhs rhsArg then
          return some h
  return none

/-- Build the proof term for direct inversion transport. -/
def mkInvDispatchProof
    (baseCtx : Expr)
    (g : FPMEqGoalView)
    (L N_safe ha₁ ha₂ : Expr)
    (h : FPMEqHypView) : TacticM Expr := withMainContext do
  let lhsArgs := g.lhs.getAppArgs
  let rhsArgs := g.rhs.getAppArgs
  if lhsArgs.isEmpty || rhsArgs.isEmpty then
    throwError "[fpm] inv goal did not expose one argument"
  mkAppM ``FPM_Inv_Substitution
    #[baseCtx,
      L,
      N_safe,
      lhsArgs[lhsArgs.size - 1]!,
      rhsArgs[rhsArgs.size - 1]!,
      ha₁,
      ha₂,
      mkFVar h.fvarId]

syntax "fpm_dispatch_inv"
  "(" term "," term "," term "," ident "," ident ")" : tactic

elab_rules : tactic
  | `(tactic| fpm_dispatch_inv($ctx, $L, $Nsafe, $ha₁:ident, $ha₂:ident)) => withMainContext do
      let g ← getFPMEqGoalView
      let sh ← getFPMGoalShape
      let hyps ← getLocalFPMEqHyps
      let ctxExpr ← elabTerm ctx none
      let LExpr ← elabTerm L none
      let NsafeExpr ← elabTerm Nsafe none
      match sh with
      | .inv =>
          match ← findInvSupportDirect ctxExpr LExpr NsafeExpr g.lhs g.rhs hyps with
          | some h =>
              let pf ← mkInvDispatchProof
                ctxExpr
                g
                LExpr
                NsafeExpr
                (mkFVar (← getFVarId ha₁))
                (mkFVar (← getFVarId ha₂))
                h
              closeMainGoal `fpm_dispatch_inv pf
          | none =>
              throwError
                "[fpm] no matching inv hypothesis at shifted inversion context found"
      | _ =>
          throwError "[fpm] inv_direct only applies to inversion goals"

/- ========================================================================
   5.6 Examples
   Smoke tests for each dispatcher currently implemented.
   ======================================================================== -/

example (ctx : _root_.Context)
    (a₁ a₂ b₁ b₂ : FPM_Real)
    (h1 : FPM_Eq (shift_context_bin ctx FPM_Add) a₁ a₂)
    (h2 : FPM_Eq (shift_context_bin ctx FPM_Add) b₁ b₂) :
    FPM_Eq ctx (a₁ + b₁) (a₂ + b₂) := by
  exact FPM_Add_Substitution ctx a₁ a₂ b₁ b₂ h1 h2

example (ctx : _root_.Context)
    (a₁ a₂ b₁ b₂ : FPM_Real)
    (h1 : FPM_Eq (shift_context_bin ctx FPM_Add) a₁ a₂)
    (h2 : FPM_Eq (shift_context_bin ctx FPM_Add) b₁ b₂) :
    FPM_Eq ctx (a₁ + b₁) (a₂ + b₂) := by
  fpm_dispatch

example (ctx : _root_.Context)
    (a₁ a₂ : FPM_Real)
    (h : FPM_Eq (shift_context_unary ctx FPM_Neg) a₁ a₂) :
    FPM_Eq ctx (-a₁) (-a₂) := by
  fpm_dispatch

example (ctx : _root_.Context) (F : FPM_Fun) (a₁ a₂ : FPM_Real)
    (h : FPM_Eq (shift_context_unary ctx F) a₁ a₂) :
    FPM_Eq ctx (FPM_UnaryApply F a₁) (FPM_UnaryApply F a₂) := by
  fpm_dispatch

example (ctx ctxHA ctxHB : _root_.Context)
    (a₁ a₂ b₁ b₂ : FPM_Real)
    (hMA : (shift_context_bin ctx FPM_Add).M ≤ ctxHA.M)
    (hNA : ctxHA.N ≤ (shift_context_bin ctx FPM_Add).N)
    (hMB : (shift_context_bin ctx FPM_Add).M ≤ ctxHB.M)
    (hNB : ctxHB.N ≤ (shift_context_bin ctx FPM_Add).N)
    (h1 : FPM_Eq ctxHA a₁ a₂)
    (h2 : FPM_Eq ctxHB b₁ b₂) :
    FPM_Eq ctx (a₁ + b₁) (a₂ + b₂) := by
  fpm_dispatch_add_from(hMA, hNA, hMB, hNB)

example (ctx ctxH : _root_.Context) (F : FPM_Fun) (a₁ a₂ : FPM_Real)
    (hM : (shift_context_unary ctx F).M ≤ ctxH.M)
    (hN : ctxH.N ≤ (shift_context_unary ctx F).N)
    (h : FPM_Eq ctxH a₁ a₂) :
    FPM_Eq ctx (FPM_UnaryApply F a₁) (FPM_UnaryApply F a₂) := by
  fpm_dispatch_unary_from(hM, hN)

example (ctx : _root_.Context) (C : ℕ+) (a₁ a₂ b₁ b₂ : FPM_Real)
    (ha₁ : FPM_Bounded a₁ C)
    (hb₂ : FPM_Bounded b₂ C)
    (h1 : FPM_Eq (shift_context_mul ctx C) a₁ a₂)
    (h2 : FPM_Eq (shift_context_mul ctx C) b₁ b₂) :
    FPM_Eq ctx (a₁ * b₁) (a₂ * b₂) := by
  fpm_dispatch_mul(C, ha₁, hb₂)

example (ctx : _root_.Context) (L N_safe : ℕ+) (a₁ a₂ : FPM_Real)
    (ha₁ : FPM_EventuallyApart a₁ L N_safe)
    (ha₂ : FPM_EventuallyApart a₂ L N_safe)
    (h : FPM_Eq (shift_context_inv_subst ctx L N_safe) a₁ a₂) :
    FPM_Eq { M := ctx.M, N := max ctx.N N_safe } (a₁⁻¹) (a₂⁻¹) := by
  fpm_dispatch_inv(ctx, L, N_safe, ha₁, ha₂)

/- -- Multiplication from stronger hypotheses ----------------------------- -/

/-- Match a multiplication goal against two local hypotheses, ignoring
    context. The context comparison is supplied separately by the user. -/
def findMulSupportFrom
    (lhs rhs : Expr) (hyps : Array FPMEqHypView) :
    MetaM (Option (FPMEqHypView × FPMEqHypView)) := do
  let some (lhs₁, lhs₂) ← getBinaryArgsIf ``HMul.hMul lhs | return none
  let some (rhs₁, rhs₂) ← getBinaryArgsIf ``HMul.hMul rhs | return none
  for h1 in hyps do
    for h2 in hyps do
      if h1.fvarId != h2.fvarId then
        if ← exprDefEq h1.lhs lhs₁ then
          if ← exprDefEq h1.rhs rhs₁ then
            if ← exprDefEq h2.lhs lhs₂ then
              if ← exprDefEq h2.rhs rhs₂ then
                return some (h1, h2)
  return none

/-- Build the proof term for weakened multiplication transport. -/
def mkMulFromDispatchProof
    (g : FPMEqGoalView)
    (C : Expr)
    (ha₁ hb₂ : Expr)
    (hMA hNA hMB hNB : Expr)
    (h1 h2 : FPMEqHypView) : TacticM Expr := withMainContext do
  let lhsArgs := g.lhs.getAppArgs
  let rhsArgs := g.rhs.getAppArgs
  if lhsArgs.size < 2 || rhsArgs.size < 2 then
    throwError "[fpm] mul goal did not expose two arguments"
  mkAppM ``FPM_Mul_Substitution_of_weaker
    #[g.ctx,
      C,
      h1.ctx,
      h2.ctx,
      lhsArgs[lhsArgs.size - 2]!,
      rhsArgs[rhsArgs.size - 2]!,
      lhsArgs[lhsArgs.size - 1]!,
      rhsArgs[rhsArgs.size - 1]!,
      ha₁,
      hb₂,
      hMA,
      hNA,
      hMB,
      hNB,
      mkFVar h1.fvarId,
      mkFVar h2.fvarId]

syntax "fpm_dispatch_mul_from"
  "(" term "," ident "," ident "," ident "," ident "," ident "," ident ")" : tactic

elab_rules : tactic
  | `(tactic|
      fpm_dispatch_mul_from($C, $hMA:ident, $hNA:ident, $hMB:ident, $hNB:ident, $ha₁:ident, $hb₂:ident)
    ) => withMainContext do
      let g ← getFPMEqGoalView
      let sh ← getFPMGoalShape
      let hyps ← getLocalFPMEqHyps
      let CExpr ← elabTerm C none
      match sh with
      | .mul =>
          match ← findMulSupportFrom g.lhs g.rhs hyps with
          | some (h1, h2) =>
              let pf ← mkMulFromDispatchProof
                g
                CExpr
                (mkFVar (← getFVarId ha₁))
                (mkFVar (← getFVarId hb₂))
                (mkFVar (← getFVarId hMA))
                (mkFVar (← getFVarId hNA))
                (mkFVar (← getFVarId hMB))
                (mkFVar (← getFVarId hNB))
                h1 h2
              closeMainGoal `fpm_dispatch_mul_from pf
          | none =>
              throwError "[fpm] no matching mul hypotheses found for mul_from"
      | _ =>
          throwError "[fpm] mul_from only applies to multiplication goals"

example (ctx ctxHA ctxHB : _root_.Context) (C : ℕ+)
    (a₁ a₂ b₁ b₂ : FPM_Real)
    (hMA : (shift_context_mul ctx C).M ≤ ctxHA.M)
    (hNA : ctxHA.N ≤ (shift_context_mul ctx C).N)
    (hMB : (shift_context_mul ctx C).M ≤ ctxHB.M)
    (hNB : ctxHB.N ≤ (shift_context_mul ctx C).N)
    (ha₁ : FPM_Bounded a₁ C)
    (hb₂ : FPM_Bounded b₂ C)
    (h1 : FPM_Eq ctxHA a₁ a₂)
    (h2 : FPM_Eq ctxHB b₁ b₂) :
    FPM_Eq ctx (a₁ * b₁) (a₂ * b₂) := by
  fpm_dispatch_mul_from(C, hMA, hNA, hMB, hNB, ha₁, hb₂)

/- -- Inversion from stronger hypotheses ---------------------------------- -/

/-- Match an inversion goal against one local hypothesis, ignoring context.
    The context comparison is supplied separately by the user. -/
def findInvSupportFrom
    (lhs rhs : Expr) (hyps : Array FPMEqHypView) :
    MetaM (Option FPMEqHypView) := do
  let some lhsArg ← getUnaryArgIf ``Inv.inv lhs | return none
  let some rhsArg ← getUnaryArgIf ``Inv.inv rhs | return none
  for h in hyps do
    if ← exprDefEq h.lhs lhsArg then
      if ← exprDefEq h.rhs rhsArg then
        return some h
  return none

/-- Build the proof term for weakened inversion transport. -/
def mkInvFromDispatchProof
    (baseCtx : Expr)
    (g : FPMEqGoalView)
    (L N_safe : Expr)
    (ha₁ ha₂ : Expr)
    (hM hN : Expr)
    (h : FPMEqHypView) : TacticM Expr := withMainContext do
  let lhsArgs := g.lhs.getAppArgs
  let rhsArgs := g.rhs.getAppArgs
  if lhsArgs.isEmpty || rhsArgs.isEmpty then
    throwError "[fpm] inv goal did not expose one argument"
  mkAppM ``FPM_Inv_Substitution_of_weaker
    #[baseCtx,
      L,
      N_safe,
      h.ctx,
      lhsArgs[lhsArgs.size - 1]!,
      rhsArgs[rhsArgs.size - 1]!,
      ha₁,
      ha₂,
      hM,
      hN,
      mkFVar h.fvarId]

syntax "fpm_dispatch_inv_from"
  "(" term "," term "," term "," ident "," ident "," ident "," ident ")" : tactic

elab_rules : tactic
  | `(tactic|
      fpm_dispatch_inv_from($ctx, $L, $Nsafe, $hM:ident, $hN:ident, $ha₁:ident, $ha₂:ident)
    ) => withMainContext do
      let g ← getFPMEqGoalView
      let sh ← getFPMGoalShape
      let hyps ← getLocalFPMEqHyps
      let ctxExpr ← elabTerm ctx none
      let LExpr ← elabTerm L none
      let NsafeExpr ← elabTerm Nsafe none
      match sh with
      | .inv =>
          match ← findInvSupportFrom g.lhs g.rhs hyps with
          | some h =>
              let pf ← mkInvFromDispatchProof
                ctxExpr
                g
                LExpr
                NsafeExpr
                (mkFVar (← getFVarId ha₁))
                (mkFVar (← getFVarId ha₂))
                (mkFVar (← getFVarId hM))
                (mkFVar (← getFVarId hN))
                h
              closeMainGoal `fpm_dispatch_inv_from pf
          | none =>
              throwError "[fpm] no matching inv hypothesis found for inv_from"
      | _ =>
          throwError "[fpm] inv_from only applies to inversion goals"

example (ctx ctxH : _root_.Context) (L N_safe : ℕ+) (a₁ a₂ : FPM_Real)
    (hM : (shift_context_inv_subst ctx L N_safe).M ≤ ctxH.M)
    (hN : ctxH.N ≤ (shift_context_inv_subst ctx L N_safe).N)
    (ha₁ : FPM_EventuallyApart a₁ L N_safe)
    (ha₂ : FPM_EventuallyApart a₂ L N_safe)
    (h : FPM_Eq ctxH a₁ a₂) :
    FPM_Eq { M := ctx.M, N := max ctx.N N_safe } (a₁⁻¹) (a₂⁻¹) := by
  fpm_dispatch_inv_from(ctx, L, N_safe, hM, hN, ha₁, ha₂)

-- nary examples
example (ctx : _root_.Context) (n : ℕ+) (v w : Fin n.val → FPM_Real)
    (h : ∀ i : Fin n.val,
      FPM_Eq (shift_context_nary ctx n (FPM_AddNary n.val)) (v i) (w i)) :
    FPM_Eq ctx (FPM_sum_nary v) (FPM_sum_nary w) := by
  fpm_dispatch

example (ctx ctxH : _root_.Context) (n : ℕ+) (v w : Fin n.val → FPM_Real)
    (hM : (shift_context_nary ctx n (FPM_AddNary n.val)).M ≤ ctxH.M)
    (hN : ctxH.N ≤ (shift_context_nary ctx n (FPM_AddNary n.val)).N)
    (h : ∀ i : Fin n.val, FPM_Eq ctxH (v i) (w i)) :
    FPM_Eq ctx (FPM_sum_nary v) (FPM_sum_nary w) := by
  fpmdispatchnaryfrom(hM, hN)
/-
  ========================================================================
  SECTION 5.7: PUBLIC FRONT-END TACTICS
  Thin user-facing wrappers over the internal dispatchers.
  ========================================================================
-/

/-- Public exact dispatcher.
    Uses the exact shifted-context rule when no extra side data is needed. -/
elab "fpm" : tactic => withMainContext do
  Lean.Elab.Tactic.evalTactic (← `(tactic| fpm_dispatch))

/-- Public exact dispatcher for guarded multiplication. -/
syntax (name := fpmExactMulStx)
  "fpm" "(" term "," ident "," ident ")" : tactic

elab_rules (kind := fpmExactMulStx) : tactic
  | `(tactic| fpm($C, $ha₁:ident, $hb₂:ident)) => withMainContext do
      let sh ← getFPMGoalShape
      match sh with
      | .mul =>
          Lean.Elab.Tactic.evalTactic
            (← `(tactic| fpm_dispatch_mul($C, $ha₁, $hb₂)))
      | _ =>
          throwError "[fpm] this 3-argument form only applies to multiplication goals"

/-- Public exact dispatcher for guarded inversion. -/
syntax (name := fpmExactInvStx)
  "fpm" "(" term "," term "," term "," ident "," ident ")" : tactic

elab_rules (kind := fpmExactInvStx) : tactic
  | `(tactic| fpm($ctx, $L, $Nsafe, $ha₁:ident, $ha₂:ident)) => withMainContext do
      let sh ← getFPMGoalShape
      match sh with
      | .inv =>
          Lean.Elab.Tactic.evalTactic
            (← `(tactic| fpm_dispatch_inv($ctx, $L, $Nsafe, $ha₁, $ha₂)))
      | _ =>
          throwError "[fpm] this 5-argument form only applies to inversion goals"


/-- Public weakened dispatcher for unary and n-ary-add goals. -/
syntax (name := fpmFrom2Stx)
  "fpm_from" "(" ident "," ident ")" : tactic

elab_rules (kind := fpmFrom2Stx) : tactic
  | `(tactic| fpm_from($hM:ident, $hN:ident)) => withMainContext do
      let sh ← getFPMGoalShape
      match sh with
      | .unary =>
          Lean.Elab.Tactic.evalTactic
            (← `(tactic| fpm_dispatch_unary_from($hM, $hN)))
      | .naryAdd =>
          Lean.Elab.Tactic.evalTactic
            (← `(tactic| fpmdispatchnaryfrom($hM, $hN)))
      | _ =>
          throwError
            "[fpm] this 2-argument form only applies to unary or n-ary-add goals"

/-- Public weakened dispatcher for addition. -/
syntax (name := fpmFromAddStx)
  "fpm_from" "(" ident "," ident "," ident "," ident ")" : tactic

elab_rules (kind := fpmFromAddStx) : tactic
  | `(tactic| fpm_from($hMA:ident, $hNA:ident, $hMB:ident, $hNB:ident)) => withMainContext do
      let sh ← getFPMGoalShape
      match sh with
      | .add =>
          Lean.Elab.Tactic.evalTactic
            (← `(tactic| fpm_dispatch_add_from($hMA, $hNA, $hMB, $hNB)))
      | _ =>
          throwError "[fpm] this 4-argument form only applies to addition goals"

/-- Public weakened dispatcher for guarded multiplication. -/
syntax (name := fpmFromMulStx)
  "fpm_from_mul"
  "(" term "," ident "," ident "," ident "," ident "," ident "," ident ")" : tactic

elab_rules (kind := fpmFromMulStx) : tactic
  | `(tactic|
      fpm_from_mul($C, $hMA:ident, $hNA:ident, $hMB:ident, $hNB:ident, $ha₁:ident, $hb₂:ident)
    ) => withMainContext do
      let sh ← getFPMGoalShape
      match sh with
      | .mul =>
          Lean.Elab.Tactic.evalTactic
            (← `(tactic|
              fpm_dispatch_mul_from($C, $hMA, $hNA, $hMB, $hNB, $ha₁, $hb₂)
            ))
      | _ =>
          throwError "[fpm] fpm_from_mul only applies to multiplication goals"

/-- Public weakened dispatcher for guarded inversion. -/
syntax (name := fpmFromInvStx)
  "fpm_from_inv"
  "(" term "," term "," term "," ident "," ident "," ident "," ident ")" : tactic

elab_rules (kind := fpmFromInvStx) : tactic
  | `(tactic|
      fpm_from_inv($ctx, $L, $Nsafe, $hM:ident, $hN:ident, $ha₁:ident, $ha₂:ident)
    ) => withMainContext do
      let sh ← getFPMGoalShape
      match sh with
      | .inv =>
          Lean.Elab.Tactic.evalTactic
            (← `(tactic|
              fpm_dispatch_inv_from($ctx, $L, $Nsafe, $hM, $hN, $ha₁, $ha₂)
            ))
      | _ =>
          throwError "[fpm] fpm_from_inv only applies to inversion goals"
