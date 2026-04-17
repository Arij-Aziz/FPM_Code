import Again.FPM_Phase5_Execution
import Mathlib

noncomputable section
/-!
  # Phase 6: Complex Numbers

  This file builds complex numbers on top of the existing FPM real engine.

  - We begin with a purely structural and transport-oriented file.
  - Compiler support for complex goals can come later; Phase 5 currently
    recognizes only `FPM_Eq` goals on the real layer.
-/

/- ========================================================================
   SECTION 1: BASIC OBJECT
   ======================================================================== -/

structure FPM_Complex where
  re : FPM_Real
  im : FPM_Real

/-- Componentwise contextual equality for complex numbers. -/
def FPM_Complex_Eq (ctx : _root_.Context) (z w : FPM_Complex) : Prop :=
  FPM_Eq ctx z.re w.re ∧ FPM_Eq ctx z.im w.im

/-- Componentwise boundedness. -/
def FPM_Complex_Bounded (z : FPM_Complex) (C : ℕ+) : Prop :=
  FPM_Bounded z.re C ∧ FPM_Bounded z.im C

/-- Complex invertibility will be guarded through the norm-square denominator. -/
def FPM_Complex_EventuallyApartNormSq
    (z : FPM_Complex) (L N_safe : ℕ+) : Prop :=
  FPM_EventuallyApart (((z.re * z.re) + (z.im * z.im))) L N_safe

@[simp] theorem FPM_Complex_Eq_re
    {ctx : _root_.Context} {z w : FPM_Complex}
    (h : FPM_Complex_Eq ctx z w) :
    FPM_Eq ctx z.re w.re :=
  h.1

@[simp] theorem FPM_Complex_Eq_im
    {ctx : _root_.Context} {z w : FPM_Complex}
    (h : FPM_Complex_Eq ctx z w) :
    FPM_Eq ctx z.im w.im :=
  h.2

theorem FPM_Complex_Eq_mk
    {ctx : _root_.Context}
    {a₁ a₂ b₁ b₂ : FPM_Real}
    (hre : FPM_Eq ctx a₁ a₂)
    (him : FPM_Eq ctx b₁ b₂) :
    FPM_Complex_Eq ctx ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ := by
  exact ⟨hre, him⟩

/- ========================================================================
   SECTION 2: OPERATIONS
   ======================================================================== -/

instance : Neg FPM_Complex :=
  ⟨fun z => { re := -z.re, im := -z.im }⟩

instance : Add FPM_Complex :=
  ⟨fun z w => { re := z.re + w.re, im := z.im + w.im }⟩

instance : Sub FPM_Complex :=
  ⟨fun z w => z + (-w)⟩

instance : Mul FPM_Complex :=
  ⟨fun z w =>
    { re := (z.re * w.re) + (-(z.im * w.im))
      im := (z.re * w.im) + (z.im * w.re) }⟩

/-- Complex conjugation. -/
def FPM_Complex_conj (z : FPM_Complex) : FPM_Complex :=
  { re := z.re
    im := -z.im }

/-- Norm square `a^2 + b^2`. -/
def FPM_Complex_normSq (z : FPM_Complex) : FPM_Real :=
  (z.re * z.re) + (z.im * z.im)

/-- Formal inverse built from conjugation and the inverse of the norm square. -/
instance : Inv FPM_Complex :=
  ⟨fun z =>
    { re := z.re * (FPM_Complex_normSq z)⁻¹
      im := -(z.im * (FPM_Complex_normSq z)⁻¹) }⟩

@[simp] theorem FPM_Complex_neg_re (z : FPM_Complex) :
    (-z).re = -z.re := rfl

@[simp] theorem FPM_Complex_neg_im (z : FPM_Complex) :
    (-z).im = -z.im := rfl

@[simp] theorem FPM_Complex_add_re (z w : FPM_Complex) :
    (z + w).re = z.re + w.re := rfl

@[simp] theorem FPM_Complex_add_im (z w : FPM_Complex) :
    (z + w).im = z.im + w.im := rfl

@[simp] theorem FPM_Complex_sub_re (z w : FPM_Complex) :
    (z - w).re = z.re + (-w.re) := rfl

@[simp] theorem FPM_Complex_sub_im (z w : FPM_Complex) :
    (z - w).im = z.im + (-w.im) := rfl

@[simp] theorem FPM_Complex_mul_re (z w : FPM_Complex) :
    (z * w).re = (z.re * w.re) + (-(z.im * w.im)) := rfl

@[simp] theorem FPM_Complex_mul_im (z w : FPM_Complex) :
    (z * w).im = (z.re * w.im) + (z.im * w.re) := rfl

@[simp] theorem FPM_Complex_conj_re (z : FPM_Complex) :
    (FPM_Complex_conj z).re = z.re := rfl

@[simp] theorem FPM_Complex_conj_im (z : FPM_Complex) :
    (FPM_Complex_conj z).im = -z.im := rfl

@[simp] theorem FPM_Complex_normSq_def (z : FPM_Complex) :
    FPM_Complex_normSq z = (z.re * z.re) + (z.im * z.im) := rfl

@[simp] theorem FPM_Complex_inv_re (z : FPM_Complex) :
    (z⁻¹).re = z.re * (FPM_Complex_normSq z)⁻¹ := rfl

@[simp] theorem FPM_Complex_inv_im (z : FPM_Complex) :
    (z⁻¹).im = -(z.im * (FPM_Complex_normSq z)⁻¹) := rfl

/-
  ========================================================================
  SECTION 3: BASIC TRANSPORT
  These are the componentwise lifts that are immediately justified by the
  visible Phase 5 real substitution interface.
  ========================================================================
-/

/-- Exact shifted-context transport for complex negation. -/
theorem FPM_Complex_Neg_Substitution
    (ctx : _root_.Context)
    (z₁ z₂ : FPM_Complex)
    (h : FPM_Complex_Eq (shift_context_unary ctx FPM_Neg) z₁ z₂) :
    FPM_Complex_Eq ctx (-z₁) (-z₂) := by
  constructor
  · exact FPM_Unary_Substitution ctx FPM_Neg z₁.re z₂.re h.1
  · exact FPM_Unary_Substitution ctx FPM_Neg z₁.im z₂.im h.2

/-- Exact shifted-context transport for complex addition. -/
theorem FPM_Complex_Add_Substitution
    (ctx : _root_.Context)
    (z₁ z₂ w₁ w₂ : FPM_Complex)
    (hz : FPM_Complex_Eq (shift_context_bin ctx FPM_Add) z₁ z₂)
    (hw : FPM_Complex_Eq (shift_context_bin ctx FPM_Add) w₁ w₂) :
    FPM_Complex_Eq ctx (z₁ + w₁) (z₂ + w₂) := by
  constructor
  · exact FPM_Add_Substitution ctx z₁.re z₂.re w₁.re w₂.re hz.1 hw.1
  · exact FPM_Add_Substitution ctx z₁.im z₂.im w₁.im w₂.im hz.2 hw.2

/-- Exact shifted-context transport for complex subtraction. -/
theorem FPM_Complex_Sub_Substitution
    (ctx : _root_.Context)
    (z₁ z₂ w₁ w₂ : FPM_Complex)
    (hz : FPM_Complex_Eq (shift_context_bin ctx FPM_Add) z₁ z₂)
    (hw : FPM_Complex_Eq (shift_context_bin ctx FPM_Add) (-w₁) (-w₂)) :
    FPM_Complex_Eq ctx (z₁ - w₁) (z₂ - w₂) := by
  simpa [Sub.sub] using FPM_Complex_Add_Substitution ctx z₁ z₂ (-w₁) (-w₂) hz hw

/-- Conjugation transport from split hypotheses. -/
theorem FPM_Complex_Conj_Substitution
    (ctx : _root_.Context)
    (z₁ z₂ : FPM_Complex)
    (hre : FPM_Eq ctx z₁.re z₂.re)
    (him : FPM_Eq (shift_context_unary ctx FPM_Neg) z₁.im z₂.im) :
    FPM_Complex_Eq ctx (FPM_Complex_conj z₁) (FPM_Complex_conj z₂) := by
  constructor
  · simpa [FPM_Complex_conj]
  · simpa [FPM_Complex_conj] using
      (FPM_Unary_Substitution ctx FPM_Neg z₁.im z₂.im him)

/- ========================================================================
   SECTION 4: BOUNDEDNESS HELPERS
   ======================================================================== -/

@[simp] theorem FPM_Complex_Bounded_re
    {z : FPM_Complex} {C : ℕ+}
    (h : FPM_Complex_Bounded z C) :
    FPM_Bounded z.re C :=
  h.1

@[simp] theorem FPM_Complex_Bounded_im
    {z : FPM_Complex} {C : ℕ+}
    (h : FPM_Complex_Bounded z C) :
    FPM_Bounded z.im C :=
  h.2

theorem FPM_Complex_Bounded_neg
    {z : FPM_Complex} {C : ℕ+}
    (h : FPM_Complex_Bounded z C) :
    FPM_Complex_Bounded (-z) C := by
  constructor
  · simpa using (FPM_Bounded_neg (a := z.re) (C := C) h.1)
  · simpa using (FPM_Bounded_neg (a := z.im) (C := C) h.2)

theorem FPM_Complex_Bounded_conj
    {z : FPM_Complex} {C : ℕ+}
    (h : FPM_Complex_Bounded z C) :
    FPM_Complex_Bounded (FPM_Complex_conj z) C := by
  constructor
  · simpa [FPM_Complex_conj] using h.1
  · simpa [FPM_Complex_conj] using
      (FPM_Bounded_neg (a := z.im) (C := C) h.2)

/-
  ========================================================================
  SECTION 5: SMOKE TESTS
  These intentionally test only the part that Phase 5 already supports
  directly at the real level.
  ========================================================================
-/

example (ctx : _root_.Context)
    (z₁ z₂ : FPM_Complex)
    (h : FPM_Complex_Eq (shift_context_unary ctx FPM_Neg) z₁ z₂) :
    FPM_Complex_Eq ctx (-z₁) (-z₂) := by
  exact FPM_Complex_Neg_Substitution ctx z₁ z₂ h

example (ctx : _root_.Context)
    (z₁ z₂ w₁ w₂ : FPM_Complex)
    (hz : FPM_Complex_Eq (shift_context_bin ctx FPM_Add) z₁ z₂)
    (hw : FPM_Complex_Eq (shift_context_bin ctx FPM_Add) w₁ w₂) :
    FPM_Complex_Eq ctx (z₁ + w₁) (z₂ + w₂) := by
  exact FPM_Complex_Add_Substitution ctx z₁ z₂ w₁ w₂ hz hw

/- ========================================================================
   SECTION 6: COMPLEX MULTIPLICATION
   We stay fully faithful to the real engine:
   - multiplication is guarded,
   - support hypotheses live at exact shifted contexts,
   - no hidden weakening is used here.
   ======================================================================== -/

/-- Support context for product terms that will later be added at `ctx`. -/
def shift_context_complex_mul_add
    (ctx : _root_.Context) (C : ℕ+) : _root_.Context :=
  shift_context_mul (shift_context_bin ctx FPM_Add) C

/-- Support context for product terms that will later be negated and then
    added at `ctx`. -/
def shift_context_complex_mul_neg_add
    (ctx : _root_.Context) (C : ℕ+) : _root_.Context :=
  shift_context_mul (shift_context_unary (shift_context_bin ctx FPM_Add) FPM_Neg) C

/-- Real-part transport for complex multiplication.

    This theorem is intentionally explicit: the positive product
    `z.re * w.re` lives over the addition-support context, while the
    negative product `-(z.im * w.im)` is built by first transporting
    the product at the negation-support context and then applying
    unary transport. -/
theorem FPM_Complex_Mul_Substitution_re
    (ctx : _root_.Context) (C : ℕ+)
    (z₁ z₂ w₁ w₂ : FPM_Complex)
    (hzr : FPM_Eq (shift_context_complex_mul_add ctx C) z₁.re z₂.re)
    (hwr : FPM_Eq (shift_context_complex_mul_add ctx C) w₁.re w₂.re)
    (hzi : FPM_Eq (shift_context_complex_mul_neg_add ctx C) z₁.im z₂.im)
    (hwi : FPM_Eq (shift_context_complex_mul_neg_add ctx C) w₁.im w₂.im)
    (hzr_bd : FPM_Bounded z₁.re C)
    (hwr_bd : FPM_Bounded w₂.re C)
    (hzi_bd : FPM_Bounded z₁.im C)
    (hwi_bd : FPM_Bounded w₂.im C) :
    FPM_Eq ctx (z₁ * w₁).re (z₂ * w₂).re := by
  have hrr :
      FPM_Eq (shift_context_bin ctx FPM_Add)
        (z₁.re * w₁.re) (z₂.re * w₂.re) := by
    exact FPM_Mul_Substitution
      (shift_context_bin ctx FPM_Add)
      C
      z₁.re z₂.re w₁.re w₂.re
      hzr_bd hwr_bd
      hzr hwr
  have hii :
      FPM_Eq (shift_context_unary (shift_context_bin ctx FPM_Add) FPM_Neg)
        (z₁.im * w₁.im) (z₂.im * w₂.im) := by
    exact FPM_Mul_Substitution
      (shift_context_unary (shift_context_bin ctx FPM_Add) FPM_Neg)
      C
      z₁.im z₂.im w₁.im w₂.im
      hzi_bd hwi_bd
      hzi hwi
  have hneg :
      FPM_Eq (shift_context_bin ctx FPM_Add)
        (-(z₁.im * w₁.im)) (-(z₂.im * w₂.im)) := by
    exact FPM_Unary_Substitution
      (shift_context_bin ctx FPM_Add)
      FPM_Neg
      (z₁.im * w₁.im) (z₂.im * w₂.im)
      hii
  simpa [FPM_Complex_mul_re] using
    (FPM_Add_Substitution
      ctx
      (z₁.re * w₁.re) (z₂.re * w₂.re)
      (-(z₁.im * w₁.im)) (-(z₂.im * w₂.im))
      hrr hneg)

/-- Imaginary-part transport for complex multiplication.

    Both summands are positive products, so both are transported at the
    addition-support context and then combined with addition transport. -/
theorem FPM_Complex_Mul_Substitution_im
    (ctx : _root_.Context) (C : ℕ+)
    (z₁ z₂ w₁ w₂ : FPM_Complex)
    (hzr : FPM_Eq (shift_context_complex_mul_add ctx C) z₁.re z₂.re)
    (hwi : FPM_Eq (shift_context_complex_mul_add ctx C) w₁.im w₂.im)
    (hzi : FPM_Eq (shift_context_complex_mul_add ctx C) z₁.im z₂.im)
    (hwr : FPM_Eq (shift_context_complex_mul_add ctx C) w₁.re w₂.re)
    (hzr_bd : FPM_Bounded z₁.re C)
    (hwi_bd : FPM_Bounded w₂.im C)
    (hzi_bd : FPM_Bounded z₁.im C)
    (hwr_bd : FPM_Bounded w₂.re C) :
    FPM_Eq ctx (z₁ * w₁).im (z₂ * w₂).im := by
  have hri :
      FPM_Eq (shift_context_bin ctx FPM_Add)
        (z₁.re * w₁.im) (z₂.re * w₂.im) := by
    exact FPM_Mul_Substitution
      (shift_context_bin ctx FPM_Add)
      C
      z₁.re z₂.re w₁.im w₂.im
      hzr_bd hwi_bd
      hzr hwi
  have hir :
      FPM_Eq (shift_context_bin ctx FPM_Add)
        (z₁.im * w₁.re) (z₂.im * w₂.re) := by
    exact FPM_Mul_Substitution
      (shift_context_bin ctx FPM_Add)
      C
      z₁.im z₂.im w₁.re w₂.re
      hzi_bd hwr_bd
      hzi hwr
  simpa [FPM_Complex_mul_im] using
    (FPM_Add_Substitution
      ctx
      (z₁.re * w₁.im) (z₂.re * w₂.im)
      (z₁.im * w₁.re) (z₂.im * w₂.re)
      hri hir)

/-- Exact complex multiplication transport.

    The theorem is verbose by design because the current engine is built
    from exact shifted-context real rules rather than a normalization
    procedure over composite expressions. -/
theorem FPM_Complex_Mul_Substitution
    (ctx : _root_.Context) (C : ℕ+)
    (z₁ z₂ w₁ w₂ : FPM_Complex)
    (hzr_add : FPM_Eq (shift_context_complex_mul_add ctx C) z₁.re z₂.re)
    (hzi_add : FPM_Eq (shift_context_complex_mul_add ctx C) z₁.im z₂.im)
    (hwr_add : FPM_Eq (shift_context_complex_mul_add ctx C) w₁.re w₂.re)
    (hwi_add : FPM_Eq (shift_context_complex_mul_add ctx C) w₁.im w₂.im)
    (hzi_neg : FPM_Eq (shift_context_complex_mul_neg_add ctx C) z₁.im z₂.im)
    (hwi_neg : FPM_Eq (shift_context_complex_mul_neg_add ctx C) w₁.im w₂.im)
    (hzr_bd : FPM_Bounded z₁.re C)
    (hzi_bd : FPM_Bounded z₁.im C)
    (hwr_bd : FPM_Bounded w₂.re C)
    (hwi_bd : FPM_Bounded w₂.im C) :
    FPM_Complex_Eq ctx (z₁ * w₁) (z₂ * w₂) := by
  constructor
  · exact FPM_Complex_Mul_Substitution_re
      ctx C z₁ z₂ w₁ w₂
      hzr_add hwr_add hzi_neg hwi_neg
      hzr_bd hwr_bd hzi_bd hwi_bd
  · exact FPM_Complex_Mul_Substitution_im
      ctx C z₁ z₂ w₁ w₂
      hzr_add hwi_add hzi_add hwr_add
      hzr_bd hwi_bd hzi_bd hwr_bd

/-
  ========================================================================
  SECTION 7: SMOKE TEST
  ========================================================================
-/

example (ctx : _root_.Context) (C : ℕ+)
    (z₁ z₂ w₁ w₂ : FPM_Complex)
    (hzr_add : FPM_Eq (shift_context_complex_mul_add ctx C) z₁.re z₂.re)
    (hzi_add : FPM_Eq (shift_context_complex_mul_add ctx C) z₁.im z₂.im)
    (hwr_add : FPM_Eq (shift_context_complex_mul_add ctx C) w₁.re w₂.re)
    (hwi_add : FPM_Eq (shift_context_complex_mul_add ctx C) w₁.im w₂.im)
    (hzi_neg : FPM_Eq (shift_context_complex_mul_neg_add ctx C) z₁.im z₂.im)
    (hwi_neg : FPM_Eq (shift_context_complex_mul_neg_add ctx C) w₁.im w₂.im)
    (hzr_bd : FPM_Bounded z₁.re C)
    (hzi_bd : FPM_Bounded z₁.im C)
    (hwr_bd : FPM_Bounded w₂.re C)
    (hwi_bd : FPM_Bounded w₂.im C) :
    FPM_Complex_Eq ctx (z₁ * w₁) (z₂ * w₂) := by
  exact FPM_Complex_Mul_Substitution
    ctx C z₁ z₂ w₁ w₂
    hzr_add hzi_add hwr_add hwi_add
    hzi_neg hwi_neg
    hzr_bd hzi_bd hwr_bd hwi_bd

/- ========================================================================
   SECTION 8: NORM-SQUARE AND DENOMINATOR TRANSPORT
   ======================================================================== -/

/-- The target context produced by real inversion over base context `ctx`. -/
def FPM_Complex_InvTarget
    (ctx : _root_.Context) (N_safe : ℕ+) : _root_.Context :=
  { M := ctx.M, N := max ctx.N N_safe }

/-- Support context for each square appearing in
    `normSq z = z.re*z.re + z.im*z.im`. -/
def shift_context_complex_normSq
    (ctx : _root_.Context) (C : ℕ+) : _root_.Context :=
  shift_context_mul (shift_context_bin ctx FPM_Add) C

/-- Support context for the real product inside complex inversion:
    `z.re * (normSq z)⁻¹`. -/
def shift_context_complex_inv_re
    (ctx : _root_.Context) (N_safe : ℕ+) (C : ℕ+) : _root_.Context :=
  shift_context_mul (FPM_Complex_InvTarget ctx N_safe) C

/-- Support context for the imaginary product before outer negation:
    `z.im * (normSq z)⁻¹`, viewed under the neg-shifted target. -/
def shift_context_complex_inv_im
    (ctx : _root_.Context) (N_safe : ℕ+) (C : ℕ+) : _root_.Context :=
  shift_context_mul (shift_context_unary (FPM_Complex_InvTarget ctx N_safe) FPM_Neg) C

/-- Exact transport for `normSq z = z.re*z.re + z.im*z.im`. -/
theorem FPM_Complex_NormSq_Substitution
    (ctx : _root_.Context) (C : ℕ+)
    (z₁ z₂ : FPM_Complex)
    (hre : FPM_Eq (shift_context_complex_normSq ctx C) z₁.re z₂.re)
    (him : FPM_Eq (shift_context_complex_normSq ctx C) z₁.im z₂.im)
    (hre_bd₁ : FPM_Bounded z₁.re C)
    (hre_bd₂ : FPM_Bounded z₂.re C)
    (him_bd₁ : FPM_Bounded z₁.im C)
    (him_bd₂ : FPM_Bounded z₂.im C) :
    FPM_Eq ctx (FPM_Complex_normSq z₁) (FPM_Complex_normSq z₂) := by
  have hrr :
      FPM_Eq (shift_context_bin ctx FPM_Add)
        (z₁.re * z₁.re) (z₂.re * z₂.re) := by
    exact FPM_Sq_Substitution
      (shift_context_bin ctx FPM_Add)
      C
      z₁.re z₂.re
      hre_bd₁ hre_bd₂
      hre
  have hii :
      FPM_Eq (shift_context_bin ctx FPM_Add)
        (z₁.im * z₁.im) (z₂.im * z₂.im) := by
    exact FPM_Sq_Substitution
      (shift_context_bin ctx FPM_Add)
      C
      z₁.im z₂.im
      him_bd₁ him_bd₂
      him
  simpa [FPM_Complex_normSq] using
    (FPM_Add_Substitution
      ctx
      (z₁.re * z₁.re) (z₂.re * z₂.re)
      (z₁.im * z₁.im) (z₂.im * z₂.im)
      hrr hii)

/-- Real inversion transport applied to the complex denominator `normSq z`. -/
theorem FPM_Complex_NormSq_Inv_Substitution
    (ctx : _root_.Context) (L N_safe : ℕ+)
    (z₁ z₂ : FPM_Complex)
    (ha₁ : FPM_EventuallyApart (FPM_Complex_normSq z₁) L N_safe)
    (ha₂ : FPM_EventuallyApart (FPM_Complex_normSq z₂) L N_safe)
    (h : FPM_Eq (shift_context_inv_subst ctx L N_safe)
          (FPM_Complex_normSq z₁) (FPM_Complex_normSq z₂)) :
    FPM_Eq (FPM_Complex_InvTarget ctx N_safe)
      ((FPM_Complex_normSq z₁)⁻¹)
      ((FPM_Complex_normSq z₂)⁻¹) := by
  simpa [FPM_Complex_InvTarget] using
    (FPM_Inv_Substitution
      ctx
      L
      N_safe
      (FPM_Complex_normSq z₁)
      (FPM_Complex_normSq z₂)
      ha₁
      ha₂
      h)

/- ========================================================================
   SECTION 9: SPLIT-FORM COMPLEX INVERSE TRANSPORT
   We keep the real and imaginary parts separate. This avoids hiding
   context bookkeeping and makes each guarded use explicit.
   ======================================================================== -/

/-- Real-part transport for complex inversion:
    `z.re * (normSq z)⁻¹`. -/
theorem FPM_Complex_Inv_Re_Substitution
    (ctx : _root_.Context) (N_safe C : ℕ+)
    (z₁ z₂ : FPM_Complex)
    (hre :
      FPM_Eq (shift_context_complex_inv_re ctx N_safe C)
        z₁.re z₂.re)
    (hden :
      FPM_Eq (shift_context_complex_inv_re ctx N_safe C)
        ((FPM_Complex_normSq z₁)⁻¹)
        ((FPM_Complex_normSq z₂)⁻¹))
    (hre_bd₁ : FPM_Bounded z₁.re C)
    (hden_bd₂ : FPM_Bounded ((FPM_Complex_normSq z₂)⁻¹) C) :
    FPM_Eq (FPM_Complex_InvTarget ctx N_safe)
      (z₁.re * ((FPM_Complex_normSq z₁)⁻¹))
      (z₂.re * ((FPM_Complex_normSq z₂)⁻¹)) := by
  simpa [shift_context_complex_inv_re] using
    (FPM_Mul_Substitution
      (FPM_Complex_InvTarget ctx N_safe)
      C
      z₁.re z₂.re
      ((FPM_Complex_normSq z₁)⁻¹)
      ((FPM_Complex_normSq z₂)⁻¹)
      hre_bd₁
      hden_bd₂
      hre
      hden)

/-- Imaginary product transport before outer negation:
    `z.im * (normSq z)⁻¹`. -/
theorem FPM_Complex_Inv_Im_Core_Substitution
    (ctx : _root_.Context) (N_safe C : ℕ+)
    (z₁ z₂ : FPM_Complex)
    (him :
      FPM_Eq (shift_context_complex_inv_im ctx N_safe C)
        z₁.im z₂.im)
    (hden :
      FPM_Eq (shift_context_complex_inv_im ctx N_safe C)
        ((FPM_Complex_normSq z₁)⁻¹)
        ((FPM_Complex_normSq z₂)⁻¹))
    (him_bd₁ : FPM_Bounded z₁.im C)
    (hden_bd₂ : FPM_Bounded ((FPM_Complex_normSq z₂)⁻¹) C) :
    FPM_Eq (shift_context_unary (FPM_Complex_InvTarget ctx N_safe) FPM_Neg)
      (z₁.im * ((FPM_Complex_normSq z₁)⁻¹))
      (z₂.im * ((FPM_Complex_normSq z₂)⁻¹)) := by
  simpa [shift_context_complex_inv_im] using
    (FPM_Mul_Substitution
      (shift_context_unary (FPM_Complex_InvTarget ctx N_safe) FPM_Neg)
      C
      z₁.im z₂.im
      ((FPM_Complex_normSq z₁)⁻¹)
      ((FPM_Complex_normSq z₂)⁻¹)
      him_bd₁
      hden_bd₂
      him
      hden)

/-- Imaginary-part transport for complex inversion:
    `-(z.im * (normSq z)⁻¹)`. -/
theorem FPM_Complex_Inv_Im_Substitution
    (ctx : _root_.Context) (N_safe C : ℕ+)
    (z₁ z₂ : FPM_Complex)
    (him :
      FPM_Eq (shift_context_complex_inv_im ctx N_safe C)
        z₁.im z₂.im)
    (hden :
      FPM_Eq (shift_context_complex_inv_im ctx N_safe C)
        ((FPM_Complex_normSq z₁)⁻¹)
        ((FPM_Complex_normSq z₂)⁻¹))
    (him_bd₁ : FPM_Bounded z₁.im C)
    (hden_bd₂ : FPM_Bounded ((FPM_Complex_normSq z₂)⁻¹) C) :
    FPM_Eq (FPM_Complex_InvTarget ctx N_safe)
      (-(z₁.im * ((FPM_Complex_normSq z₁)⁻¹)))
      (-(z₂.im * ((FPM_Complex_normSq z₂)⁻¹))) := by
  have hcore :
      FPM_Eq (shift_context_unary (FPM_Complex_InvTarget ctx N_safe) FPM_Neg)
        (z₁.im * ((FPM_Complex_normSq z₁)⁻¹))
        (z₂.im * ((FPM_Complex_normSq z₂)⁻¹)) := by
    exact FPM_Complex_Inv_Im_Core_Substitution
      ctx N_safe C z₁ z₂
      him hden
      him_bd₁ hden_bd₂
  simpa using
    (FPM_Unary_Substitution
      (FPM_Complex_InvTarget ctx N_safe)
      FPM_Neg
      (z₁.im * ((FPM_Complex_normSq z₁)⁻¹))
      (z₂.im * ((FPM_Complex_normSq z₂)⁻¹))
      hcore)

/- ========================================================================
   SECTION 10: PUBLIC WRAPPERS
   This section cleans up the user-facing API:
   - bridge the named norm-square guard to the actual denominator,
   - package componentwise hypotheses into theorems on complex objects,
   - expose a reduced inverse theorem without unused apartness data.
   ======================================================================== -/

@[simp] theorem FPM_Complex_EventuallyApartNormSq_iff
    (z : FPM_Complex) (L N_safe : ℕ+) :
    FPM_Complex_EventuallyApartNormSq z L N_safe ↔
      FPM_EventuallyApart (FPM_Complex_normSq z) L N_safe := by
  simp [FPM_Complex_EventuallyApartNormSq, FPM_Complex_normSq]

/-- Norm-square transport from a single componentwise complex hypothesis. -/
theorem FPM_Complex_NormSq_Substitution_ofEq
    (ctx : _root_.Context) (C : ℕ+)
    (z₁ z₂ : FPM_Complex)
    (h : FPM_Complex_Eq (shift_context_complex_normSq ctx C) z₁ z₂)
    (hz₁ : FPM_Complex_Bounded z₁ C)
    (hz₂ : FPM_Complex_Bounded z₂ C) :
    FPM_Eq ctx (FPM_Complex_normSq z₁) (FPM_Complex_normSq z₂) := by
  exact FPM_Complex_NormSq_Substitution
    ctx C z₁ z₂
    h.1 h.2
    hz₁.1 hz₂.1
    hz₁.2 hz₂.2

/-- Denominator inversion transport using the named complex guard. -/
theorem FPM_Complex_NormSq_Inv_Substitution_ofGuard
    (ctx : _root_.Context) (L N_safe : ℕ+)
    (z₁ z₂ : FPM_Complex)
    (ha₁ : FPM_Complex_EventuallyApartNormSq z₁ L N_safe)
    (ha₂ : FPM_Complex_EventuallyApartNormSq z₂ L N_safe)
    (h : FPM_Eq (shift_context_inv_subst ctx L N_safe)
          (FPM_Complex_normSq z₁) (FPM_Complex_normSq z₂)) :
    FPM_Eq (FPM_Complex_InvTarget ctx N_safe)
      ((FPM_Complex_normSq z₁)⁻¹)
      ((FPM_Complex_normSq z₂)⁻¹) := by
  exact FPM_Complex_NormSq_Inv_Substitution
    ctx L N_safe z₁ z₂
    (by simpa [FPM_Complex_EventuallyApartNormSq, FPM_Complex_normSq] using ha₁)
    (by simpa [FPM_Complex_EventuallyApartNormSq, FPM_Complex_normSq] using ha₂)
    h

/-- Minimal final inverse transport:
    this is the actual componentwise complex theorem. -/
theorem FPM_Complex_Inv_Substitution_core
    (ctx : _root_.Context) (N_safe C : ℕ+)
    (z₁ z₂ : FPM_Complex)
    (hre :
      FPM_Eq (shift_context_complex_inv_re ctx N_safe C)
        z₁.re z₂.re)
    (him :
      FPM_Eq (shift_context_complex_inv_im ctx N_safe C)
        z₁.im z₂.im)
    (hden_re :
      FPM_Eq (shift_context_complex_inv_re ctx N_safe C)
        ((FPM_Complex_normSq z₁)⁻¹)
        ((FPM_Complex_normSq z₂)⁻¹))
    (hden_im :
      FPM_Eq (shift_context_complex_inv_im ctx N_safe C)
        ((FPM_Complex_normSq z₁)⁻¹)
        ((FPM_Complex_normSq z₂)⁻¹))
    (hre_bd₁ : FPM_Bounded z₁.re C)
    (him_bd₁ : FPM_Bounded z₁.im C)
    (hden_bd₂ : FPM_Bounded ((FPM_Complex_normSq z₂)⁻¹) C) :
    FPM_Complex_Eq (FPM_Complex_InvTarget ctx N_safe) z₁⁻¹ z₂⁻¹ := by
  have hre_inv :
      FPM_Eq (FPM_Complex_InvTarget ctx N_safe)
        (z₁.re * ((FPM_Complex_normSq z₁)⁻¹))
        (z₂.re * ((FPM_Complex_normSq z₂)⁻¹)) := by
    exact FPM_Complex_Inv_Re_Substitution
      ctx N_safe C z₁ z₂
      hre hden_re
      hre_bd₁ hden_bd₂
  have him_inv :
      FPM_Eq (FPM_Complex_InvTarget ctx N_safe)
        (-(z₁.im * ((FPM_Complex_normSq z₁)⁻¹)))
        (-(z₂.im * ((FPM_Complex_normSq z₂)⁻¹))) := by
    exact FPM_Complex_Inv_Im_Substitution
      ctx N_safe C z₁ z₂
      him hden_im
      him_bd₁ hden_bd₂
  exact FPM_Complex_Eq_mk
    (by simpa [FPM_Complex_inv_re] using hre_inv)
    (by simpa [FPM_Complex_inv_im] using him_inv)

/-- Compatibility wrapper retaining the earlier longer signature. -/
theorem FPM_Complex_Inv_Substitution
    (ctx : _root_.Context) (L N_safe C : ℕ+)
    (z₁ z₂ : FPM_Complex)
    (hre :
      FPM_Eq (shift_context_complex_inv_re ctx N_safe C)
        z₁.re z₂.re)
    (him :
      FPM_Eq (shift_context_complex_inv_im ctx N_safe C)
        z₁.im z₂.im)
    (hden_re :
      FPM_Eq (shift_context_complex_inv_re ctx N_safe C)
        ((FPM_Complex_normSq z₁)⁻¹)
        ((FPM_Complex_normSq z₂)⁻¹))
    (hden_im :
      FPM_Eq (shift_context_complex_inv_im ctx N_safe C)
        ((FPM_Complex_normSq z₁)⁻¹)
        ((FPM_Complex_normSq z₂)⁻¹))
    (_hns_apart₁ : FPM_EventuallyApart (FPM_Complex_normSq z₁) L N_safe)
    (_hns_apart₂ : FPM_EventuallyApart (FPM_Complex_normSq z₂) L N_safe)
    (hre_bd₁ : FPM_Bounded z₁.re C)
    (him_bd₁ : FPM_Bounded z₁.im C)
    (hden_bd₂ : FPM_Bounded ((FPM_Complex_normSq z₂)⁻¹) C) :
    FPM_Complex_Eq (FPM_Complex_InvTarget ctx N_safe) z₁⁻¹ z₂⁻¹ := by
  exact FPM_Complex_Inv_Substitution_core
    ctx N_safe C z₁ z₂
    hre him
    hden_re hden_im
    hre_bd₁ him_bd₁ hden_bd₂

/- ========================================================================
   SECTION 11: SMOKE TESTS
   These confirm that the final Phase 6 complex transport API is usable
   without adding any new compiler support.
   ======================================================================== -/

example (ctx : _root_.Context) (C : ℕ+)
    (z₁ z₂ : FPM_Complex)
    (h : FPM_Complex_Eq (shift_context_complex_normSq ctx C) z₁ z₂)
    (hz₁ : FPM_Complex_Bounded z₁ C)
    (hz₂ : FPM_Complex_Bounded z₂ C) :
    FPM_Eq ctx (FPM_Complex_normSq z₁) (FPM_Complex_normSq z₂) := by
  exact FPM_Complex_NormSq_Substitution_ofEq
    ctx C z₁ z₂ h hz₁ hz₂

example (ctx : _root_.Context) (L N_safe : ℕ+)
    (z₁ z₂ : FPM_Complex)
    (ha₁ : FPM_Complex_EventuallyApartNormSq z₁ L N_safe)
    (ha₂ : FPM_Complex_EventuallyApartNormSq z₂ L N_safe)
    (h : FPM_Eq (shift_context_inv_subst ctx L N_safe)
          (FPM_Complex_normSq z₁) (FPM_Complex_normSq z₂)) :
    FPM_Eq (FPM_Complex_InvTarget ctx N_safe)
      ((FPM_Complex_normSq z₁)⁻¹)
      ((FPM_Complex_normSq z₂)⁻¹) := by
  exact FPM_Complex_NormSq_Inv_Substitution_ofGuard
    ctx L N_safe z₁ z₂ ha₁ ha₂ h

example (ctx : _root_.Context) (N_safe C : ℕ+)
    (z₁ z₂ : FPM_Complex)
    (hre :
      FPM_Eq (shift_context_complex_inv_re ctx N_safe C)
        z₁.re z₂.re)
    (him :
      FPM_Eq (shift_context_complex_inv_im ctx N_safe C)
        z₁.im z₂.im)
    (hden_re :
      FPM_Eq (shift_context_complex_inv_re ctx N_safe C)
        ((FPM_Complex_normSq z₁)⁻¹)
        ((FPM_Complex_normSq z₂)⁻¹))
    (hden_im :
      FPM_Eq (shift_context_complex_inv_im ctx N_safe C)
        ((FPM_Complex_normSq z₁)⁻¹)
        ((FPM_Complex_normSq z₂)⁻¹))
    (hre_bd₁ : FPM_Bounded z₁.re C)
    (him_bd₁ : FPM_Bounded z₁.im C)
    (hden_bd₂ : FPM_Bounded ((FPM_Complex_normSq z₂)⁻¹) C) :
    FPM_Complex_Eq (FPM_Complex_InvTarget ctx N_safe) z₁⁻¹ z₂⁻¹ := by
  exact FPM_Complex_Inv_Substitution_core
    ctx N_safe C z₁ z₂
    hre him
    hden_re hden_im
    hre_bd₁ him_bd₁ hden_bd₂

example (ctx : _root_.Context) (L N_safe C : ℕ+)
    (z₁ z₂ : FPM_Complex)
    (hre :
      FPM_Eq (shift_context_complex_inv_re ctx N_safe C)
        z₁.re z₂.re)
    (him :
      FPM_Eq (shift_context_complex_inv_im ctx N_safe C)
        z₁.im z₂.im)
    (hden_re :
      FPM_Eq (shift_context_complex_inv_re ctx N_safe C)
        ((FPM_Complex_normSq z₁)⁻¹)
        ((FPM_Complex_normSq z₂)⁻¹))
    (hden_im :
      FPM_Eq (shift_context_complex_inv_im ctx N_safe C)
        ((FPM_Complex_normSq z₁)⁻¹)
        ((FPM_Complex_normSq z₂)⁻¹))
    (hns₁ : FPM_EventuallyApart (FPM_Complex_normSq z₁) L N_safe)
    (hns₂ : FPM_EventuallyApart (FPM_Complex_normSq z₂) L N_safe)
    (hre_bd₁ : FPM_Bounded z₁.re C)
    (him_bd₁ : FPM_Bounded z₁.im C)
    (hden_bd₂ : FPM_Bounded ((FPM_Complex_normSq z₂)⁻¹) C) :
    FPM_Complex_Eq (FPM_Complex_InvTarget ctx N_safe) z₁⁻¹ z₂⁻¹ := by
  exact FPM_Complex_Inv_Substitution
    ctx L N_safe C z₁ z₂
    hre him
    hden_re hden_im
    hns₁ hns₂
    hre_bd₁ him_bd₁ hden_bd₂

example (ctx : _root_.Context) (L N_safe C : ℕ+) (z : FPM_Complex)
    (hre :
      FPM_Eq (shift_context_complex_inv_re ctx N_safe C)
        z.re z.re)
    (him :
      FPM_Eq (shift_context_complex_inv_im ctx N_safe C)
        z.im z.im)
    (hden_re :
      FPM_Eq (shift_context_complex_inv_re ctx N_safe C)
        ((FPM_Complex_normSq z)⁻¹)
        ((FPM_Complex_normSq z)⁻¹))
    (hden_im :
      FPM_Eq (shift_context_complex_inv_im ctx N_safe C)
        ((FPM_Complex_normSq z)⁻¹)
        ((FPM_Complex_normSq z)⁻¹))
    (hns : FPM_EventuallyApart (FPM_Complex_normSq z) L N_safe)
    (hre_bd : FPM_Bounded z.re C)
    (him_bd : FPM_Bounded z.im C)
    (hden_bd : FPM_Bounded ((FPM_Complex_normSq z)⁻¹) C) :
    FPM_Complex_Eq (FPM_Complex_InvTarget ctx N_safe) z⁻¹ z⁻¹ := by
  exact FPM_Complex_Inv_Substitution
    ctx L N_safe C z z
    hre him
    hden_re hden_im
    hns hns
    hre_bd him_bd hden_bd

end
