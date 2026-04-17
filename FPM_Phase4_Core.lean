import Again.FPM_Phase3
import Mathlib

open Lean

/-!
  # Phase 4 Core: Rewrite Registry

  Rewritten to use the new Phase 1 axioms.
  Uses `FPM_Fun` from Phase 1 New instead of the old `FPM_UnaryFun`.
-/

/-
  ========================================================================
  TRANSPORT THEOREM SHAPES
  ========================================================================
-/

/-- A generic unary transport theorem. -/
abbrev FPM_UnaryTransportTheorem (F : FPM_Fun) : Prop :=
  ∀ (ctx : Context) (a₁ a₂ : FPM_Real),
    FPM_Eq (shift_context_unary ctx F) a₁ a₂ →
    FPM_Eq ctx (FPM_UnaryApply F a₁) (FPM_UnaryApply F a₂)

/-- Addition transport theorem shape. -/
abbrev FPM_AddTransportTheorem : Prop :=
  ∀ (ctx : Context) (a₁ a₂ b₁ b₂ : FPM_Real),
    FPM_Eq (shift_context_bin ctx FPM_Add) a₁ a₂ →
    FPM_Eq (shift_context_bin ctx FPM_Add) b₁ b₂ →
    FPM_Eq ctx (a₁ + b₁) (a₂ + b₂)

/-- Multiplication transport theorem shape. -/
abbrev FPM_MulTransportTheorem : Prop :=
  ∀ (ctx : Context) (C : ℕ+) (a₁ a₂ b₁ b₂ : FPM_Real),
    FPM_Bounded a₁ C →
    FPM_Bounded b₂ C →
    FPM_Eq (shift_context_mul ctx C) a₁ a₂ →
    FPM_Eq (shift_context_mul ctx C) b₁ b₂ →
    FPM_Eq ctx (a₁ * b₁) (a₂ * b₂)

/-- Reciprocal transport theorem shape. -/
abbrev FPM_InvTransportTheorem : Prop :=
  ∀ (ctx : Context) (L N_safe : ℕ+) (a₁ a₂ : FPM_Real),
    FPM_EventuallyApart a₁ L N_safe →
    FPM_EventuallyApart a₂ L N_safe →
    FPM_Eq (shift_context_inv_subst ctx L N_safe) a₁ a₂ →
    FPM_Eq { M := ctx.M, N := max ctx.N N_safe } (a₁⁻¹) (a₂⁻¹)

/-- N-ary addition transport theorem shape. -/
abbrev FPM_NaryAddTransportTheorem (n : ℕ+) : Prop :=
  ∀ (ctx : Context) (v w : Fin n.val → FPM_Real),
    (∀ i, FPM_Eq (shift_context_nary ctx n (FPM_AddNary n.val)) (v i) (w i)) →
    FPM_Eq ctx (FPM_sum_nary v) (FPM_sum_nary w)
/-
  ========================================================================
  REGISTRY-FRIENDLY WRAPPERS
  ========================================================================
-/

theorem FPM_Unary_Transport (F : FPM_Fun) :
    FPM_UnaryTransportTheorem F :=
  fun ctx a₁ a₂ hA => FPM_Unary_Substitution ctx F a₁ a₂ hA

theorem FPM_Neg_Transport :
    FPM_UnaryTransportTheorem FPM_Neg :=
  fun ctx a₁ a₂ hA => FPM_Unary_Substitution ctx FPM_Neg a₁ a₂ hA

theorem FPM_Add_Transport :
    FPM_AddTransportTheorem :=
  fun ctx a₁ a₂ b₁ b₂ hA hB => FPM_Add_Substitution ctx a₁ a₂ b₁ b₂ hA hB

theorem FPM_Mul_Transport :
    FPM_MulTransportTheorem :=
  fun ctx C a₁ a₂ b₁ b₂ ha₁ hb₂ hA hB =>
    FPM_Mul_Substitution ctx C a₁ a₂ b₁ b₂ ha₁ hb₂ hA hB

theorem FPM_Inv_Transport :
    FPM_InvTransportTheorem :=
  fun ctx L N_safe a₁ a₂ ha₁ ha₂ hA =>
    FPM_Inv_Substitution ctx L N_safe a₁ a₂ ha₁ ha₂ hA

-- Registry-friendly wrapper.
theorem FPM_NaryAdd_Transport (n : ℕ+) : FPM_NaryAddTransportTheorem n :=
by
  intro ctx v w h
  exact FPM_NaryAdd_Substitution ctx v w h
/-
  ========================================================================
  RULE DESCRIPTORS
  ========================================================================
-/

inductive FPM_RuleShape where
  | unary
  | add
  | mul
  | inv
  | naryAdd
  deriving DecidableEq, Repr

structure FPM_RuleDesc where
  key : Name
  theoremName : Name
  shape : FPM_RuleShape
  deriving Repr

def FPM_negRule : FPM_RuleDesc :=
  { key := `fpm.neg
    theoremName := `FPM_Neg_Transport
    shape := .unary }

def FPM_addRule : FPM_RuleDesc :=
  { key := `fpm.add
    theoremName := `FPM_Add_Transport
    shape := .add }

def FPM_mulRule : FPM_RuleDesc :=
  { key := `fpm.mul
    theoremName := `FPM_Mul_Transport
    shape := .mul }

def FPM_invRule : FPM_RuleDesc :=
  { key := `fpm.inv
    theoremName := `FPM_Inv_Transport
    shape := .inv }

def FPM_naryAddRule : FPM_RuleDesc :=
  { key := `fpm.naryadd, theoremName := ``FPM_NaryAdd_Transport, shape := .naryAdd }

def FPM_CoreRules : List FPM_RuleDesc :=
  [FPM_negRule, FPM_addRule, FPM_mulRule, FPM_invRule, FPM_naryAddRule]

def FPM_findRuleByKey? (key : Name) : Option FPM_RuleDesc :=
  FPM_CoreRules.find? (fun r => r.key == key)

def FPM_findRuleByTheorem? (thm : Name) : Option FPM_RuleDesc :=
  FPM_CoreRules.find? (fun r => r.theoremName == thm)

#eval FPM_findRuleByKey? `fpm.neg
#eval FPM_findRuleByKey? `fpm.add
#eval FPM_findRuleByTheorem? `FPM_Inv_Transport
#eval FPM_findRuleByKey? `fpm.naryadd
#eval FPM_findRuleByTheorem? ``FPM_NaryAdd_Transport
