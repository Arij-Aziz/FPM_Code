import Again.FPM_Phase4_Core
import Mathlib

/-!
  # Phase 4 Context: Context Weakening

  written to use the Phase 1 axioms.
-/

/-
  ========================================================================
  CONTEXT WEAKENING
  ========================================================================
-/

lemma FPM_Interval_weaken
    {ctx₁ ctx₂ : Context} {a : FPM_Real} {n : ℕ+} {q : ℚ}
    (hM : ctx₁.M ≤ ctx₂.M)
    (hq : q ∈ FPM_Interval ctx₂ a n) :
    q ∈ FPM_Interval ctx₁ a n := by
  simp only [FPM_Interval, Set.mem_setOf_eq] at hq ⊢
  have hM' : (ctx₁.M : ℚ) ≤ (ctx₂.M : ℚ) := by exact_mod_cast hM
  have h2M : (2 : ℚ) * (ctx₁.M : ℚ) ≤ (2 : ℚ) * (ctx₂.M : ℚ) := by linarith
  have hpos : (0 : ℚ) < (2 : ℚ) * (ctx₁.M : ℚ) := by positivity
  have hrad : (1 : ℚ) / ((2 : ℚ) * (ctx₂.M : ℚ)) ≤ (1 : ℚ) / ((2 : ℚ) * (ctx₁.M : ℚ)) :=
    one_div_le_one_div_of_le hpos h2M
  exact le_trans hq hrad

theorem FPM_Eq_weaken
    {ctx₁ ctx₂ : Context} {a b : FPM_Real}
    (hM : ctx₁.M ≤ ctx₂.M)
    (hN : ctx₂.N ≤ ctx₁.N)
    (h : FPM_Eq ctx₂ a b) :
    FPM_Eq ctx₁ a b := by
  intro n hn
  rcases h n (le_trans hN hn) with ⟨q, hq⟩
  exact ⟨q, FPM_Interval_weaken hM hq.1, FPM_Interval_weaken hM hq.2⟩

/-
  ========================================================================
  SHIFT-CONTEXT HELPER LEMMAS
  ========================================================================
-/

lemma shift_context_unary_N (ctx : Context) (F : FPM_Fun) :
    (shift_context_unary ctx F).N = ctx.N := rfl

lemma shift_context_unary_M_ge (ctx : Context) (F : FPM_Fun) :
    ctx.M ≤ (shift_context_unary ctx F).M := by
  change ((ctx.M : ℕ) ≤ (ctx.M : ℕ) * (F.K : ℕ))
  exact Nat.le_mul_of_pos_right _ F.K.pos

lemma shift_context_bin_N (ctx : Context) (F : FPM_BinFun) :
    (shift_context_bin ctx F).N = ctx.N := rfl

lemma shift_context_bin_M_ge (ctx : Context) (F : FPM_BinFun) :
    ctx.M ≤ (shift_context_bin ctx F).M := by
  rw [shift_context_bin]
  exact_mod_cast
    (show (ctx.M : ℕ) ≤ (ctx.M : ℕ) * (F.K : ℕ) * 2 from by
      calc
        (ctx.M : ℕ) ≤ (ctx.M : ℕ) * (F.K : ℕ) :=
          Nat.le_mul_of_pos_right _ F.K.pos
        _ ≤ (ctx.M : ℕ) * (F.K : ℕ) * 2 :=
          Nat.le_mul_of_pos_right _ (by decide : 0 < (2 : ℕ)))

lemma shift_context_mul_N (ctx : Context) (C : ℕ+) :
    (shift_context_mul ctx C).N = ctx.N := rfl

lemma shift_context_inv_subst_N (ctx : Context) (L N_safe : ℕ+) :
    (shift_context_inv_subst ctx L N_safe).N = max ctx.N N_safe := rfl

lemma shift_context_nary_N (ctx : Context) (n : ℕ+) :
    (shift_context_nary ctx n (FPM_AddNary n.val)).N = ctx.N := rfl

lemma shift_context_nary_M_ge (ctx : Context) (n : ℕ+) :
    ctx.M ≤ (shift_context_nary ctx n (FPM_AddNary n.val)).M := by
  simp [shift_context_nary, FPM_AddNary]
/-
  ========================================================================
  BRIDGE LEMMAS
  ========================================================================
-/

theorem FPM_Unary_Substitution_of_weaker
    (ctx : Context) (F : FPM_Fun)
    (ctxH : Context)
    (a₁ a₂ : FPM_Real)
    (hM : (shift_context_unary ctx F).M ≤ ctxH.M)
    (hN : ctxH.N ≤ (shift_context_unary ctx F).N)
    (hA : FPM_Eq ctxH a₁ a₂) :
    FPM_Eq ctx (FPM_UnaryApply F a₁) (FPM_UnaryApply F a₂) :=
  FPM_Unary_Substitution ctx F a₁ a₂ (FPM_Eq_weaken hM hN hA)

theorem FPM_Add_Substitution_of_weaker
    (ctx : Context)
    (ctxHA ctxHB : Context)
    (a₁ a₂ b₁ b₂ : FPM_Real)
    (hMA : (shift_context_bin ctx FPM_Add).M ≤ ctxHA.M)
    (hNA : ctxHA.N ≤ (shift_context_bin ctx FPM_Add).N)
    (hMB : (shift_context_bin ctx FPM_Add).M ≤ ctxHB.M)
    (hNB : ctxHB.N ≤ (shift_context_bin ctx FPM_Add).N)
    (hA : FPM_Eq ctxHA a₁ a₂)
    (hB : FPM_Eq ctxHB b₁ b₂) :
    FPM_Eq ctx (a₁ + b₁) (a₂ + b₂) :=
  FPM_Add_Substitution ctx a₁ a₂ b₁ b₂ (FPM_Eq_weaken hMA hNA hA) (FPM_Eq_weaken hMB hNB hB)

theorem FPM_Mul_Substitution_of_weaker
    (ctx : Context) (C : ℕ+)
    (ctxHA ctxHB : Context)
    (a₁ a₂ b₁ b₂ : FPM_Real)
    (ha₁ : FPM_Bounded a₁ C)
    (hb₂ : FPM_Bounded b₂ C)
    (hMA : (shift_context_mul ctx C).M ≤ ctxHA.M)
    (hNA : ctxHA.N ≤ (shift_context_mul ctx C).N)
    (hMB : (shift_context_mul ctx C).M ≤ ctxHB.M)
    (hNB : ctxHB.N ≤ (shift_context_mul ctx C).N)
    (hA : FPM_Eq ctxHA a₁ a₂)
    (hB : FPM_Eq ctxHB b₁ b₂) :
    FPM_Eq ctx (a₁ * b₁) (a₂ * b₂) :=
  FPM_Mul_Substitution ctx C a₁ a₂ b₁ b₂ ha₁ hb₂ (FPM_Eq_weaken hMA hNA hA) (FPM_Eq_weaken hMB hNB hB)

theorem FPM_Inv_Substitution_of_weaker
    (ctx : Context) (L N_safe : ℕ+)
    (ctxH : Context)
    (a₁ a₂ : FPM_Real)
    (ha₁ : FPM_EventuallyApart a₁ L N_safe)
    (ha₂ : FPM_EventuallyApart a₂ L N_safe)
    (hM : (shift_context_inv_subst ctx L N_safe).M ≤ ctxH.M)
    (hN : ctxH.N ≤ (shift_context_inv_subst ctx L N_safe).N)
    (hA : FPM_Eq ctxH a₁ a₂) :
    FPM_Eq { M := ctx.M, N := max ctx.N N_safe } (a₁⁻¹) (a₂⁻¹) :=
  FPM_Inv_Substitution ctx L N_safe a₁ a₂ ha₁ ha₂ (FPM_Eq_weaken hM hN hA)

theorem FPM_NaryAdd_Substitution_of_weaker
    (ctx ctxH : Context) (n : ℕ+)
    (v w : Fin n.val → FPM_Real)
    (hM : (shift_context_nary ctx n (FPM_AddNary n.val)).M ≤ ctxH.M)
    (hN : ctxH.N ≤ (shift_context_nary ctx n (FPM_AddNary n.val)).N)
    (h : ∀ i : Fin n.val, FPM_Eq ctxH (v i) (w i)) :
    FPM_Eq ctx (FPM_sum_nary v) (FPM_sum_nary w) := by
  apply FPM_NaryAdd_Substitution
  intro i
  exact FPM_Eq_weaken hM hN (h i)

#eval FPM_findRuleByKey? `fpm.neg
#eval FPM_findRuleByKey? `fpm.add
#eval FPM_findRuleByTheorem? `FPM_Inv_Transport
#eval FPM_findRuleByKey? `fpm.naryadd
#eval FPM_findRuleByTheorem? ``FPM_NaryAdd_Transport
