import Again.FPM_Phase5_Compiler
import Mathlib

/-!
  # Phase 5 Execution

  This file demonstrates the public Phase 5 interface.
  The internal compiler machinery lives in `FPM_Phase5_Compiler`;
  here we use only `fpm` and `fpm_from`.
-/

/- ========================================================================
   5E.1 Exact dispatch
   These examples use exact shifted-context hypotheses.
   ======================================================================== -/

example (ctx : _root_.Context)
    (a₁ a₂ b₁ b₂ : FPM_Real)
    (h1 : FPM_Eq (shift_context_bin ctx FPM_Add) a₁ a₂)
    (h2 : FPM_Eq (shift_context_bin ctx FPM_Add) b₁ b₂) :
    FPM_Eq ctx (a₁ + b₁) (a₂ + b₂) := by
  fpm

example (ctx : _root_.Context)
    (a₁ a₂ : FPM_Real)
    (h : FPM_Eq (shift_context_unary ctx FPM_Neg) a₁ a₂) :
    FPM_Eq ctx (-a₁) (-a₂) := by
  fpm

example (ctx : _root_.Context)
    (F : FPM_Fun)
    (a₁ a₂ : FPM_Real)
    (h : FPM_Eq (shift_context_unary ctx F) a₁ a₂) :
    FPM_Eq ctx (FPM_UnaryApply F a₁) (FPM_UnaryApply F a₂) := by
  fpm

example (ctx : _root_.Context) (C : ℕ+)
    (a₁ a₂ b₁ b₂ : FPM_Real)
    (ha₁ : FPM_Bounded a₁ C)
    (hb₂ : FPM_Bounded b₂ C)
    (h1 : FPM_Eq (shift_context_mul ctx C) a₁ a₂)
    (h2 : FPM_Eq (shift_context_mul ctx C) b₁ b₂) :
    FPM_Eq ctx (a₁ * b₁) (a₂ * b₂) := by
  fpm(C, ha₁, hb₂)

example (ctx : _root_.Context) (L N_safe : ℕ+)
    (a₁ a₂ : FPM_Real)
    (ha₁ : FPM_EventuallyApart a₁ L N_safe)
    (ha₂ : FPM_EventuallyApart a₂ L N_safe)
    (h : FPM_Eq (shift_context_inv_subst ctx L N_safe) a₁ a₂) :
    FPM_Eq { M := ctx.M, N := max ctx.N N_safe } (a₁⁻¹) (a₂⁻¹) := by
  fpm(ctx, L, N_safe, ha₁, ha₂)

/- ========================================================================
   5E.2 Weakened dispatch
   These examples use stronger hypotheses plus comparison proofs.
   ======================================================================== -/

example (ctx ctxHA ctxHB : _root_.Context)
    (a₁ a₂ b₁ b₂ : FPM_Real)
    (hMA : (shift_context_bin ctx FPM_Add).M ≤ ctxHA.M)
    (hNA : ctxHA.N ≤ (shift_context_bin ctx FPM_Add).N)
    (hMB : (shift_context_bin ctx FPM_Add).M ≤ ctxHB.M)
    (hNB : ctxHB.N ≤ (shift_context_bin ctx FPM_Add).N)
    (h1 : FPM_Eq ctxHA a₁ a₂)
    (h2 : FPM_Eq ctxHB b₁ b₂) :
    FPM_Eq ctx (a₁ + b₁) (a₂ + b₂) := by
  fpm_from(hMA, hNA, hMB, hNB)

example (ctx ctxH : _root_.Context)
    (F : FPM_Fun)
    (a₁ a₂ : FPM_Real)
    (hM : (shift_context_unary ctx F).M ≤ ctxH.M)
    (hN : ctxH.N ≤ (shift_context_unary ctx F).N)
    (h : FPM_Eq ctxH a₁ a₂) :
    FPM_Eq ctx (FPM_UnaryApply F a₁) (FPM_UnaryApply F a₂) := by
  fpm_from(hM, hN)

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
  fpm_from_mul(C, hMA, hNA, hMB, hNB, ha₁, hb₂)

example (ctx ctxH : _root_.Context) (L N_safe : ℕ+)
    (a₁ a₂ : FPM_Real)
    (hM : (shift_context_inv_subst ctx L N_safe).M ≤ ctxH.M)
    (hN : ctxH.N ≤ (shift_context_inv_subst ctx L N_safe).N)
    (ha₁ : FPM_EventuallyApart a₁ L N_safe)
    (ha₂ : FPM_EventuallyApart a₂ L N_safe)
    (h : FPM_Eq ctxH a₁ a₂) :
    FPM_Eq { M := ctx.M, N := max ctx.N N_safe } (a₁⁻¹) (a₂⁻¹) := by
  fpm_from_inv(ctx, L, N_safe, hM, hN, ha₁, ha₂)

/- ========================================================================
   5E.3 Small compositions
   These show the public interface in slightly less isolated settings.
   ======================================================================== -/

example (ctx : _root_.Context)
    (a₁ a₂ b₁ b₂ : FPM_Real)
    (hA : FPM_Eq (shift_context_unary (shift_context_bin ctx FPM_Add) FPM_Neg) a₁ a₂)
    (hB : FPM_Eq (shift_context_unary (shift_context_bin ctx FPM_Add) FPM_Neg) b₁ b₂) :
    FPM_Eq ctx ((-a₁) + (-b₁)) ((-a₂) + (-b₂)) := by
  have hA' : FPM_Eq (shift_context_bin ctx FPM_Add) (-a₁) (-a₂) := by
    exact FPM_Unary_Substitution (shift_context_bin ctx FPM_Add) FPM_Neg a₁ a₂ hA
  have hB' : FPM_Eq (shift_context_bin ctx FPM_Add) (-b₁) (-b₂) := by
    exact FPM_Unary_Substitution (shift_context_bin ctx FPM_Add) FPM_Neg b₁ b₂ hB
  exact FPM_Add_Substitution ctx (-a₁) (-a₂) (-b₁) (-b₂) hA' hB'

example (ctx : _root_.Context)
    (F : FPM_Fun)
    (a₁ a₂ : FPM_Real)
    (h : FPM_Eq (shift_context_unary ctx F) a₁ a₂) :
    FPM_Eq ctx (FPM_UnaryApply F a₁) (FPM_UnaryApply F a₂) := by
  fpm

example (ctx : _root_.Context) (C : ℕ+)
    (a₁ a₂ b₁ b₂ : FPM_Real)
    (ha₁ : FPM_Bounded a₁ C)
    (hb₂ : FPM_Bounded b₂ C)
    (h1 : FPM_Eq (shift_context_mul ctx C) a₁ a₂)
    (h2 : FPM_Eq (shift_context_mul ctx C) b₁ b₂) :
    FPM_Eq ctx ((a₁ * b₁)) ((a₂ * b₂)) := by
  fpm(C, ha₁, hb₂)
