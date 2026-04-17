import Again.FPM_Phase4_Context
import Mathlib

open Lean Elab

/-!
  # Phase 4 Rewrite

  written to use the Phase 1 axioms.
  Uses `FPM_Fun`.
-/

/-
  ========================================================================
  SYNTAX
  ========================================================================
-/

syntax "fpm_rw" "[" ident "]" "using" "neg" : tactic
syntax "fpm_rw" "[" ident "]" "using" "unary" "(" term ")" : tactic
syntax "fpm_rw" "[" ident "," ident "]" "using" "add" : tactic
syntax "fpm_rw" "[" ident "," ident "]" "using" "mul" "(" term "," ident "," ident ")" : tactic
syntax "fpm_rw" "[" ident "]" "using" "inv" "(" term "," term "," ident "," ident ")" : tactic
syntax "fpm_rw" "[" ident "]" "using" "naryadd" : tactic

syntax "fpm_rw" "[" ident "]" "using" "neg_from" "(" ident "," ident ")" : tactic
syntax "fpm_rw" "[" ident "]" "using" "unary_from" "(" term "," ident "," ident ")" : tactic
syntax "fpm_rw" "[" ident "," ident "]" "using" "add_from" "(" ident "," ident "," ident "," ident ")" : tactic
syntax "fpm_rw" "[" ident "," ident "]" "using" "mul_from"
  "(" term "," ident "," ident "," ident "," ident "," ident "," ident ")" : tactic
syntax "fpm_rw" "[" ident "]" "using" "inv_from"
  "(" term "," term "," ident "," ident "," ident "," ident ")" : tactic
syntax "fpm_rw" "[" ident "]" "using" "naryadd_from" "(" ident "," ident ")" : tactic
/-
  ========================================================================
  ELABORATION RULES
  ========================================================================
-/

elab_rules : tactic
  | `(tactic| fpm_rw [$h:ident] using neg) => do
      Lean.Elab.Tactic.evalTactic (← `(tactic|
        exact FPM_Unary_Substitution_of_weaker
          _ FPM_Neg (shift_context_unary _ FPM_Neg) _ _ le_rfl le_rfl $h
      ))
  | `(tactic| fpm_rw [$h:ident] using unary($F)) => do
      Lean.Elab.Tactic.evalTactic (← `(tactic|
        exact FPM_Unary_Substitution_of_weaker
          _ $F (shift_context_unary _ $F) _ _ le_rfl le_rfl $h
      ))
  | `(tactic| fpm_rw [$h₁:ident, $h₂:ident] using add) => do
      Lean.Elab.Tactic.evalTactic (← `(tactic|
        exact FPM_Add_Substitution_of_weaker
          _ (shift_context_bin _ FPM_Add) (shift_context_bin _ FPM_Add)
          _ _ _ _ le_rfl le_rfl le_rfl le_rfl $h₁ $h₂
      ))
  | `(tactic| fpm_rw [$h₁:ident, $h₂:ident] using mul($C, $ha₁:ident, $hb₂:ident)) => do
      Lean.Elab.Tactic.evalTactic (← `(tactic|
        exact FPM_Mul_Substitution_of_weaker
          _ $C (shift_context_mul _ $C) (shift_context_mul _ $C)
          _ _ _ _ $ha₁ $hb₂
          le_rfl le_rfl le_rfl le_rfl
          $h₁ $h₂
      ))
  | `(tactic| fpm_rw [$h:ident] using inv($L, $Nsafe, $ha₁:ident, $ha₂:ident)) => do
      Lean.Elab.Tactic.evalTactic (← `(tactic|
        exact FPM_Inv_Substitution_of_weaker
          _ $L $Nsafe (shift_context_inv_subst _ $L $Nsafe)
          _ _ $ha₁ $ha₂
          le_rfl le_rfl
          $h
      ))
  | `(tactic| fpm_rw [$h:ident] using neg_from($hM:ident, $hN:ident)) => do
      Lean.Elab.Tactic.evalTactic (← `(tactic|
        exact FPM_Unary_Substitution_of_weaker
          _ FPM_Neg _ _ _ $hM $hN $h
      ))
  | `(tactic| fpm_rw [$h:ident] using unary_from($F, $hM:ident, $hN:ident)) => do
      Lean.Elab.Tactic.evalTactic (← `(tactic|
        exact FPM_Unary_Substitution_of_weaker
          _ $F _ _ _ $hM $hN $h
      ))
  | `(tactic| fpm_rw [$h₁:ident, $h₂:ident] using add_from($hMA:ident, $hNA:ident, $hMB:ident, $hNB:ident)) => do
      Lean.Elab.Tactic.evalTactic (← `(tactic|
        exact FPM_Add_Substitution_of_weaker
          _ _ _ _ _ _ _
          $hMA $hNA $hMB $hNB
          $h₁ $h₂
      ))
  | `(tactic| fpm_rw [$h₁:ident, $h₂:ident] using mul_from($C, $ha₁:ident, $hb₂:ident, $hMA:ident, $hNA:ident, $hMB:ident, $hNB:ident)) => do
      Lean.Elab.Tactic.evalTactic (← `(tactic|
        exact FPM_Mul_Substitution_of_weaker
          _ $C _ _ _ _ _ _
          $ha₁ $hb₂
          $hMA $hNA $hMB $hNB
          $h₁ $h₂
      ))
  | `(tactic| fpm_rw [$h:ident] using inv_from($L, $Nsafe, $ha₁:ident, $ha₂:ident, $hM:ident, $hN:ident)) => do
      Lean.Elab.Tactic.evalTactic (← `(tactic|
        exact FPM_Inv_Substitution_of_weaker
          _ $L $Nsafe _ _ _
          $ha₁ $ha₂
          $hM $hN
          $h
      ))

elab_rules : tactic
| `(tactic| fpm_rw [$h:ident] using naryadd) => do
    Lean.Elab.Tactic.evalTactic (← `(tactic|
      exact FPM_NaryAdd_Substitution_of_weaker
        _
        (hM := le_rfl)
        (hN := le_rfl)
        (h := $h)))
| `(tactic| fpm_rw [$hident] using naryadd_from ($hMident, $hNident)) => do
    Lean.Elab.Tactic.evalTactic (← `(tactic|
      exact FPM_NaryAdd_Substitution_of_weaker
        _
        (hM := $hMident)
        (hN := $hNident)
        (h := $hident)))
/-
  ========================================================================
  SANITY CHECKS
  ========================================================================
-/

example (ctx : _root_.Context) (a₁ a₂ : FPM_Real)
    (hA : FPM_Eq (shift_context_unary ctx FPM_Neg) a₁ a₂) :
    FPM_Eq ctx (-a₁) (-a₂) := by
  fpm_rw [hA] using neg

example (ctx : _root_.Context) (F : FPM_Fun) (a₁ a₂ : FPM_Real)
    (hA : FPM_Eq (shift_context_unary ctx F) a₁ a₂) :
    FPM_Eq ctx (FPM_UnaryApply F a₁) (FPM_UnaryApply F a₂) := by
  fpm_rw [hA] using unary(F)

example (ctx : _root_.Context) (a₁ a₂ b₁ b₂ : FPM_Real)
    (hA : FPM_Eq (shift_context_bin ctx FPM_Add) a₁ a₂)
    (hB : FPM_Eq (shift_context_bin ctx FPM_Add) b₁ b₂) :
    FPM_Eq ctx (a₁ + b₁) (a₂ + b₂) := by
  fpm_rw [hA, hB] using add

example (ctx : _root_.Context) (C : ℕ+) (a₁ a₂ b₁ b₂ : FPM_Real)
    (ha₁ : FPM_Bounded a₁ C)
    (hb₂ : FPM_Bounded b₂ C)
    (hA : FPM_Eq (shift_context_mul ctx C) a₁ a₂)
    (hB : FPM_Eq (shift_context_mul ctx C) b₁ b₂) :
    FPM_Eq ctx (a₁ * b₁) (a₂ * b₂) := by
  fpm_rw [hA, hB] using mul(C, ha₁, hb₂)

example (ctx : _root_.Context) (L N_safe : ℕ+) (a₁ a₂ : FPM_Real)
    (ha₁ : FPM_EventuallyApart a₁ L N_safe)
    (ha₂ : FPM_EventuallyApart a₂ L N_safe)
    (hA : FPM_Eq (shift_context_inv_subst ctx L N_safe) a₁ a₂) :
    FPM_Eq { M := ctx.M, N := max ctx.N N_safe } (a₁⁻¹) (a₂⁻¹) := by
  fpm_rw [hA] using inv(L, N_safe, ha₁, ha₂)

example (ctx ctxH : _root_.Context) (F : FPM_Fun) (a₁ a₂ : FPM_Real)
    (hM : (shift_context_unary ctx F).M ≤ ctxH.M)
    (hN : ctxH.N ≤ (shift_context_unary ctx F).N)
    (hA : FPM_Eq ctxH a₁ a₂) :
    FPM_Eq ctx (FPM_UnaryApply F a₁) (FPM_UnaryApply F a₂) := by
  fpm_rw [hA] using unary_from(F, hM, hN)

example (ctx ctxHA ctxHB : _root_.Context) (a₁ a₂ b₁ b₂ : FPM_Real)
    (hMA : (shift_context_bin ctx FPM_Add).M ≤ ctxHA.M)
    (hNA : ctxHA.N ≤ (shift_context_bin ctx FPM_Add).N)
    (hMB : (shift_context_bin ctx FPM_Add).M ≤ ctxHB.M)
    (hNB : ctxHB.N ≤ (shift_context_bin ctx FPM_Add).N)
    (hA : FPM_Eq ctxHA a₁ a₂)
    (hB : FPM_Eq ctxHB b₁ b₂) :
    FPM_Eq ctx (a₁ + b₁) (a₂ + b₂) := by
  fpm_rw [hA, hB] using add_from(hMA, hNA, hMB, hNB)
