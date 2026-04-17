import Again.FPM_Phase2
import Mathlib

/-!
  NOTE ON INVERSION IN THIS PHASE

  The canonical inverse theory is now the apart-certified one:
  inversion is mathematically justified only under `FPM_EventuallyApart`.
  Accordingly, the real correctness content in Phase 3 comes from the
  guarded inverse machinery and theorems proved on the safe tail
  `max ctx.N N_safe`.

  The user-facing notation `a⁻¹` is retained only as a convenience wrapper
  for compatibility and minimal code churn. So when comments below speak
  informally about `a⁻¹` as the inverse witness, what is actually happening
  is that the proof is using the apart-certified reciprocal behavior of the
  sequence, valid under the explicit apartness hypotheses.
-/

/-!
  # Phase 3: The Classical Bridge

  Rewritten to use the new Phase 1 axioms.

  THE APART-CERTIFIED RECIPROCAL SUBSTITUTION THEOREM
  This is the canonical transport theorem for inversion.
  If two FPM reals overlap at the inversion-shifted context, and both are
  eventually apart from zero, then their certified reciprocals overlap at the
  target context with tail `max(ctx.N, N_safe)`.

  The public theorem `FPM_Inv_Substitution` is a compatibility wrapper around
  this guarded result, so existing code can continue to use inverse notation
  while the actual correctness proof remains certified and apart-aware.
-/

/-
Extract an overlap witness `q` from the shifted context. Use the certified
reciprocal value at step `n` (equivalently, the pointwise reciprocal sequence
value) as the output witness. One interval goal is immediate from the chosen
center. For the other, apply the localized inversion Lipschitz bound under the
apartness hypotheses, bound the underlying sequence difference by passing
through `q` with the triangle inequality, and close the budget arithmetic with
`FPM_Inv_Budget`.
-/

theorem FPM_Inv_Substitution_Apart
    (ctx : Context) (L : ℕ+) (N_safe : ℕ+)
    (a₁ a₂ : FPM_Real)
    (ha₁ : FPM_EventuallyApart a₁ L N_safe)
    (ha₂ : FPM_EventuallyApart a₂ L N_safe)
    (hA : FPM_Eq (shift_context_inv_subst ctx L N_safe) a₁ a₂) :
    FPM_Eq { M := ctx.M, N := max ctx.N N_safe }
      (FPM_Real_Inv_Apart a₁ L N_safe ha₁)
      (FPM_Real_Inv_Apart a₂ L N_safe ha₂) := by
  intro n hn
  have hNsafe : N_safe ≤ n := by
    exact le_trans (le_max_right _ _) hn
  obtain ⟨q, hq⟩ :
      ∃ q, q ∈ FPM_Interval (shift_context_inv_subst ctx L N_safe) a₁ n ∧
           q ∈ FPM_Interval (shift_context_inv_subst ctx L N_safe) a₂ n := by
    unfold FPM_Eq at hA
    specialize hA n (by simpa [shift_context_inv_subst] using hn)
    aesop
  use (a₁.seq n)⁻¹
  constructor
  · simp [FPM_Interval, FPM_Real_Inv_Apart]
  · simp [FPM_Interval, FPM_Real_Inv_Apart]
    have h_lip :
        abs ((a₁.seq n)⁻¹ - (a₂.seq n)⁻¹) ≤
          (L : ℚ)^2 * abs (a₁.seq n - a₂.seq n) := by
      exact inv_lipschitz_bounded _ _ L (ha₁ n hNsafe) (ha₂ n hNsafe)
    have h_triangle :
        abs (a₁.seq n - a₂.seq n) ≤
          (1 : ℚ) / (2 * ((shift_context_inv_subst ctx L N_safe).M : ℚ)) +
          (1 : ℚ) / (2 * ((shift_context_inv_subst ctx L N_safe).M : ℚ)) := by
      calc
        abs (a₁.seq n - a₂.seq n)
            = abs ((a₁.seq n - q) + (q - a₂.seq n)) := by ring_nf
        _ ≤ abs (a₁.seq n - q) + abs (q - a₂.seq n) := abs_add_le _ _
        _ ≤ (1 : ℚ) / (2 * ((shift_context_inv_subst ctx L N_safe).M : ℚ)) +
             (1 : ℚ) / (2 * ((shift_context_inv_subst ctx L N_safe).M : ℚ)) := by
             gcongr
             · simp only [FPM_Interval] at hq
               rw [abs_sub_comm]
               exact hq.1
             · exact hq.2
    have h_budget :
        (L : ℚ)^2 *
          ((1 : ℚ) / (2 * ((shift_context_inv_subst ctx L N_safe).M : ℚ)) +
           (1 : ℚ) / (2 * ((shift_context_inv_subst ctx L N_safe).M : ℚ)))
          ≤
        (1 : ℚ) / (2 * (ctx.M : ℚ)) := by
      simpa [shift_context_inv_subst, mul_add, add_comm, add_left_comm, add_assoc,
        mul_assoc, mul_comm, mul_left_comm] using FPM_Inv_Budget_le ctx L N_safe
    have h_target :
        (L : ℚ)^2 * abs (a₁.seq n - a₂.seq n) ≤
          (1 : ℚ) / (2 * (ctx.M : ℚ)) := by
      simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
        (le_trans
          (mul_le_mul_of_nonneg_left h_triangle (by positivity))
          h_budget)
    have h_target' : (L : ℚ)^2 * abs (a₁.seq n - a₂.seq n) ≤ (↑↑ctx.M)⁻¹ * 2⁻¹ := by
      convert h_target using 1
      field_simp
    exact le_trans h_lip h_target'


theorem FPM_Inv_Substitution
    (ctx : Context) (L : ℕ+) (N_safe : ℕ+)
    (a₁ a₂ : FPM_Real)
    (ha₁ : FPM_EventuallyApart a₁ L N_safe)
    (ha₂ : FPM_EventuallyApart a₂ L N_safe)
    (hA : FPM_Eq (shift_context_inv_subst ctx L N_safe) a₁ a₂) :
    FPM_Eq { M := ctx.M, N := max ctx.N N_safe }
      (a₁⁻¹) (a₂⁻¹) := by
  intro n hn
  simpa [FPM_Interval,
    FPM_Inv_seq_eq_certified_of_apart a₁ L N_safe ha₁ n,
    FPM_Inv_seq_eq_certified_of_apart a₂ L N_safe ha₂ n] using
    (FPM_Inv_Substitution_Apart ctx L N_safe a₁ a₂ ha₁ ha₂ hA n hn)

/-!
  # The Classical Bridge

  This phase translates ZFC Π₂⁰ theorems (`∀ X, ∃ Y`) into FPM, inspired by JCM.
  Classical existence is replaced by explicit constructive generators, and
  classical equality is replaced by `FPM_Eq` evaluated at a deterministically
  compiled precision budget.
-/

/-
========================================================================
  BRIDGE THEOREM: MULTIPLICATIVE INVERSE

  Classical ZFC: ∀ x ∈ ℝ, x ≠ 0 → ∃ y ∈ ℝ, x * y = 1

  FPM :
  - `∀ x` -> `(a : FPM_Real)`
  - `x ≠ 0` -> `FPM_EventuallyApart a L N_safe`
  - `∃ y` -> witnessed in the public API by `a⁻¹`
  - `x * y = 1` -> `FPM_Eq { M := ctx.M, N := max ctx.N N_safe } (a * a⁻¹) FPM_One`
========================================================================

Historical note:
an earlier total-inverse presentation hid the real mathematical issue behind
a non-certified inverse definition. In the current design, the canonical
inverse theory is the apart-certified one, and this bridge theorem uses the
public inverse notation together with the guarded sequence bridge that is valid
under eventual apartness.

The tail index must be `max ctx.N N_safe`, since the inverse argument is only
justified once the sequence is inside the apart-safe tail.

PROVIDED SOLUTION
Fix `n ≥ max ctx.N N_safe`. Then `n ≥ N_safe`, so `a.seq n ≠ 0` by
`FPM_EventuallyApart_nonzero`. Under the apartness hypothesis, the public
inverse satisfies `(a⁻¹).seq n = (a.seq n)⁻¹`, hence
`(a * a⁻¹).seq n = a.seq n * (a.seq n)⁻¹ = 1 = FPM_One.seq n`.
Use `1` as the overlap witness; both intervals are centered at `1`, so the
distance is `0` and therefore within the target radius.
-/

theorem ZFC_Inverse_Bridge
    (ctx : Context)
    (C L N_safe : ℕ+)
    (a : FPM_Real)
    (ha_bound : FPM_Bounded a C)
    (ha_apart : FPM_EventuallyApart a L N_safe) :
    FPM_Eq { M := ctx.M, N := max ctx.N N_safe } (a * a⁻¹) FPM_One := by
  intro n hn
  use 1
  constructor
  ·
    have hNsafe : N_safe ≤ n := by
      exact le_trans (le_max_right _ _) hn
    have hseq : (a⁻¹).seq n = (a.seq n)⁻¹ :=
      FPM_Inv_seq_of_apart a L N_safe ha_apart n
    have hne : a.seq n ≠ 0 :=
      FPM_EventuallyApart_nonzero a L N_safe n ha_apart hNsafe
    simp [FPM_Interval, hseq, hne]
  ·
    simp [FPM_Interval, FPM_One]


/-
========================================================================
  BRIDGE THEOREM: ADDITIVE IDENTITY

  Classical ZFC: ∀ x ∈ ℝ, ∃ y ∈ ℝ, x + y = x  (where y is 0)
  ========================================================================

PROVIDED SOLUTION
For any n ≥ ctx.N, we need a witness in the overlap of intervals
for (a + FPM_Zero) and a. Since (a + FPM_Zero).seq n = a.seq n + 0 = a.seq n, we
use a.seq n as witness. Both intervals have center a.seq n, so the distance
is 0 which is ≤ radius.
-/
theorem ZFC_Add_Identity_Bridge
    (ctx : Context)
    (a : FPM_Real) :
    FPM_Eq ctx (a + FPM_Zero) a := by
  -- For any n ≥ ctx.N, we can choose q = a.seq n as the witness.
  intro n hn
  use a.seq n
  simp [FPM_Interval];
  norm_num [ FPM_Zero ]

open Lean
#check ZFC_Inverse_Bridge
#check ZFC_Add_Identity_Bridge
