import Again.FPM_Phase4_Rewrite
import Mathlib

/-!
  # Phase 4 Examples

  written to use the Phase 1 axioms.
-/

section FPM_Phase4_Examples

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

example (ctx : Context) (n : ℕ+) (v w : Fin n.val → FPM_Real)
    (h : ∀ i : Fin n.val,
      FPM_Eq (shift_context_nary ctx n (FPM_AddNary n.val)) (v i) (w i)) :
    FPM_Eq ctx (FPM_sum_nary v) (FPM_sum_nary w) := by
  fpm_rw [h] using naryadd

example (ctx ctxH : Context) (n : ℕ+) (v w : Fin n.val → FPM_Real)
    (hM : (shift_context_nary ctx n (FPM_AddNary n.val)).M ≤ ctxH.M)
    (hN : ctxH.N ≤ (shift_context_nary ctx n (FPM_AddNary n.val)).N)
    (h : ∀ i : Fin n.val, FPM_Eq ctxH (v i) (w i)) :
    FPM_Eq ctx (FPM_sum_nary v) (FPM_sum_nary w) := by
  fpm_rw [h] using naryadd_from(hM, hN)

end FPM_Phase4_Examples
