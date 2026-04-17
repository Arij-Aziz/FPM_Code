import Again.FPM_Phase5_Execution
import Mathlib

noncomputable section

/-!
  # Phase 6: Calculus

  This file extends the FPM real engine toward:
  - limits,
  - derivatives.

  Design choice:
  - begin with structural objects and predicates,
  - define difference-quotient data explicitly,
  - delay transport theorems until the basic calculus API is fixed,
  - stay faithful to the visible Phase 5 real layer.
-/


/- ========================================================================
   SECTION 1: BASIC OBJECTS
   ======================================================================== -/


/-- Unary real functions for the calculus layer. -/
abbrev FPM_CalcFun := FPM_Real → FPM_Real


/-- Sequences in the FPM real layer. -/
abbrev FPM_Sequence := ℕ+ → FPM_Real


/-- Pointwise contextual equality for unary functions. -/
def FPM_CalcFun_Eq (ctx : _root_.Context)
    (f g : FPM_CalcFun) : Prop :=
  ∀ x : FPM_Real, FPM_Eq ctx (f x) (g x)


/-- Pointwise contextual equality for sequences. -/
def FPM_Sequence_Eq (ctx : _root_.Context)
    (a b : FPM_Sequence) : Prop :=
  ∀ n : ℕ+, FPM_Eq ctx (a n) (b n)


/-- Pointwise boundedness of a unary function. -/
def FPM_CalcFun_Bounded
    (f : FPM_CalcFun) (C : ℕ+) : Prop :=
  ∀ x : FPM_Real, FPM_Bounded (f x) C


/-- Pointwise boundedness of a sequence. -/
def FPM_Sequence_Bounded
    (a : FPM_Sequence) (C : ℕ+) : Prop :=
  ∀ n : ℕ+, FPM_Bounded (a n) C


@[simp] theorem FPM_CalcFun_Eq_app
    {ctx : _root_.Context} {f g : FPM_CalcFun}
    (h : FPM_CalcFun_Eq ctx f g) (x : FPM_Real) :
    FPM_Eq ctx (f x) (g x) :=
  h x


@[simp] theorem FPM_Sequence_Eq_app
    {ctx : _root_.Context} {a b : FPM_Sequence}
    (h : FPM_Sequence_Eq ctx a b) (n : ℕ+) :
    FPM_Eq ctx (a n) (b n) :=
  h n


@[simp] theorem FPM_CalcFun_Bounded_app
    {f : FPM_CalcFun} {C : ℕ+}
    (h : FPM_CalcFun_Bounded f C) (x : FPM_Real) :
    FPM_Bounded (f x) C :=
  h x


@[simp] theorem FPM_Sequence_Bounded_app
    {a : FPM_Sequence} {C : ℕ+}
    (h : FPM_Sequence_Bounded a C) (n : ℕ+) :
    FPM_Bounded (a n) C :=
  h n


theorem FPM_CalcFun_Eq_mk
    {ctx : _root_.Context} {f g : FPM_CalcFun}
    (h : ∀ x : FPM_Real, FPM_Eq ctx (f x) (g x)) :
    FPM_CalcFun_Eq ctx f g := by
  intro x
  exact h x


theorem FPM_Sequence_Eq_mk
    {ctx : _root_.Context} {a b : FPM_Sequence}
    (h : ∀ n : ℕ+, FPM_Eq ctx (a n) (b n)) :
    FPM_Sequence_Eq ctx a b := by
  intro n
  exact h n


theorem FPM_CalcFun_Bounded_mk
    {f : FPM_CalcFun} {C : ℕ+}
    (h : ∀ x : FPM_Real, FPM_Bounded (f x) C) :
    FPM_CalcFun_Bounded f C := by
  intro x
  exact h x


theorem FPM_Sequence_Bounded_mk
    {a : FPM_Sequence} {C : ℕ+}
    (h : ∀ n : ℕ+, FPM_Bounded (a n) C) :
    FPM_Sequence_Bounded a C := by
  intro n
  exact h n



/-
  Basic algebraic gadgets for calculus expressions.
-/


/-- The incremented input `x + h`. -/
def FPM_Calc_shiftInput
    (x h : FPM_Real) : FPM_Real :=
  x + h


/-- The forward difference numerator `f(x+h) - f(x)`, written additively. -/
def FPM_Calc_forwardDiff
    (f : FPM_CalcFun) (x h : FPM_Real) : FPM_Real :=
  (f (FPM_Calc_shiftInput x h)) + (-(f x))


/-- The formal forward difference quotient. -/
def FPM_Calc_diffQuot
    (f : FPM_CalcFun) (x h : FPM_Real) : FPM_Real :=
  (FPM_Calc_forwardDiff f x h) * (h⁻¹)


@[simp] theorem FPM_Calc_shiftInput_def
    (x h : FPM_Real) :
    FPM_Calc_shiftInput x h = x + h := rfl


@[simp] theorem FPM_Calc_forwardDiff_def
    (f : FPM_CalcFun) (x h : FPM_Real) :
    FPM_Calc_forwardDiff f x h = (f (x + h)) + (-(f x)) := rfl


@[simp] theorem FPM_Calc_diffQuot_def
    (f : FPM_CalcFun) (x h : FPM_Real) :
    FPM_Calc_diffQuot f x h = ((f (x + h)) + (-(f x))) * (h⁻¹) := rfl



/- ========================================================================
   SECTION 2: LIMIT AND DERIVATIVE PREDICATES
   ======================================================================== -/


/--
A sequence limit predicate at context `ctx`.

This is intentionally phrased structurally for now:
the sequence values are all contextually equal to the proposed limit.
Later sections can weaken or refine this into asymptotic notions.
-/
def FPM_Sequence_Limit
    (ctx : _root_.Context)
    (a : FPM_Sequence) (ℓ : FPM_Real) : Prop :=
  ∀ n : ℕ+, FPM_Eq ctx (a n) ℓ


/--
A function limit predicate along a chosen increment sequence `h`.

The idea is that `f(x + h_n)` tends to `ℓ` as the increment sequence is
driven through the calculus layer.
-/
def FPM_CalcFun_LimitAlong
    (ctx : _root_.Context)
    (f : FPM_CalcFun) (x : FPM_Real)
    (h : FPM_Sequence) (ℓ : FPM_Real) : Prop :=
  FPM_Sequence_Limit ctx (fun n => f (x + h n)) ℓ


/--
A derivative predicate along a chosen increment sequence `h`.

This uses the formal difference quotient and leaves the nonzero-guard
responsibility explicit for later sections.
-/
def FPM_CalcFun_DerivAlong
    (ctx : _root_.Context)
    (f : FPM_CalcFun) (x : FPM_Real)
    (h : FPM_Sequence) (d : FPM_Real) : Prop :=
  FPM_Sequence_Limit ctx (fun n => FPM_Calc_diffQuot f x (h n)) d


/--
A guarded derivative predicate, adding eventual apartness of the
increment sequence from zero.
-/
def FPM_CalcFun_DerivAlong_Guarded
    (ctx : _root_.Context)
    (f : FPM_CalcFun) (x : FPM_Real)
    (h : FPM_Sequence) (L N_safe : ℕ+) (d : FPM_Real) : Prop :=
  (∀ n : ℕ+, FPM_EventuallyApart (h n) L N_safe) ∧
  FPM_CalcFun_DerivAlong ctx f x h d


@[simp] theorem FPM_Sequence_Limit_app
    {ctx : _root_.Context} {a : FPM_Sequence} {ℓ : FPM_Real}
    (h : FPM_Sequence_Limit ctx a ℓ) (n : ℕ+) :
    FPM_Eq ctx (a n) ℓ :=
  h n


@[simp] theorem FPM_CalcFun_LimitAlong_def
    {ctx : _root_.Context}
    {f : FPM_CalcFun} {x : FPM_Real}
    {h : FPM_Sequence} {ℓ : FPM_Real} :
    FPM_CalcFun_LimitAlong ctx f x h ℓ =
      FPM_Sequence_Limit ctx (fun n => f (x + h n)) ℓ := rfl


@[simp] theorem FPM_CalcFun_DerivAlong_def
    {ctx : _root_.Context}
    {f : FPM_CalcFun} {x : FPM_Real}
    {h : FPM_Sequence} {d : FPM_Real} :
    FPM_CalcFun_DerivAlong ctx f x h d =
      FPM_Sequence_Limit ctx (fun n => FPM_Calc_diffQuot f x (h n)) d := rfl


@[simp] theorem FPM_CalcFun_DerivAlong_Guarded_apart
    {ctx : _root_.Context}
    {f : FPM_CalcFun} {x : FPM_Real}
    {h : FPM_Sequence} {L N_safe : ℕ+} {d : FPM_Real}
    (hd : FPM_CalcFun_DerivAlong_Guarded ctx f x h L N_safe d) :
    ∀ n : ℕ+, FPM_EventuallyApart (h n) L N_safe :=
  hd.1


@[simp] theorem FPM_CalcFun_DerivAlong_Guarded_deriv
    {ctx : _root_.Context}
    {f : FPM_CalcFun} {x : FPM_Real}
    {h : FPM_Sequence} {L N_safe : ℕ+} {d : FPM_Real}
    (hd : FPM_CalcFun_DerivAlong_Guarded ctx f x h L N_safe d) :
    FPM_CalcFun_DerivAlong ctx f x h d :=
  hd.2

/- ========================================================================
   SECTION 3: BASIC TRANSPORT
   We first lift the visible real substitution interface to:
   - unary function equality,
   - sequence equality,
   - shifted inputs `x + h`.
   ======================================================================== -/


/- Function and sequence operations --------------------------------- -/

instance : Neg FPM_CalcFun :=
  ⟨fun f x => -(f x)⟩

instance : Add FPM_CalcFun :=
  ⟨fun f g x => f x + g x⟩

instance : Sub FPM_CalcFun :=
  ⟨fun f g => f + (-g)⟩

instance : Neg FPM_Sequence :=
  ⟨fun a n => -(a n)⟩

instance : Add FPM_Sequence :=
  ⟨fun a b n => a n + b n⟩

instance : Sub FPM_Sequence :=
  ⟨fun a b => a + (-b)⟩


@[simp] theorem FPM_CalcFun_neg_apply
    (f : FPM_CalcFun) (x : FPM_Real) :
    (-f) x = -(f x) := rfl

@[simp] theorem FPM_CalcFun_add_apply
    (f g : FPM_CalcFun) (x : FPM_Real) :
    (f + g) x = f x + g x := rfl

@[simp] theorem FPM_CalcFun_sub_apply
    (f g : FPM_CalcFun) (x : FPM_Real) :
    (f - g) x = f x + (-(g x)) := rfl

@[simp] theorem FPM_Sequence_neg_apply
    (a : FPM_Sequence) (n : ℕ+) :
    (-a) n = -(a n) := rfl

@[simp] theorem FPM_Sequence_add_apply
    (a b : FPM_Sequence) (n : ℕ+) :
    (a + b) n = a n + b n := rfl

@[simp] theorem FPM_Sequence_sub_apply
    (a b : FPM_Sequence) (n : ℕ+) :
    (a - b) n = a n + (-(b n)) := rfl



/- Function and sequence transport ---------------------------------- -/

/-- Exact shifted-context transport for function negation. -/
theorem FPM_CalcFun_Neg_Substitution
    (ctx : _root_.Context)
    (f g : FPM_CalcFun)
    (h : FPM_CalcFun_Eq (shift_context_unary ctx FPM_Neg) f g) :
    FPM_CalcFun_Eq ctx (-f) (-g) := by
  intro x
  exact FPM_Unary_Substitution ctx FPM_Neg (f x) (g x) (h x)


/-- Exact shifted-context transport for function addition. -/
theorem FPM_CalcFun_Add_Substitution
    (ctx : _root_.Context)
    (f₁ f₂ g₁ g₂ : FPM_CalcFun)
    (hf : FPM_CalcFun_Eq (shift_context_bin ctx FPM_Add) f₁ f₂)
    (hg : FPM_CalcFun_Eq (shift_context_bin ctx FPM_Add) g₁ g₂) :
    FPM_CalcFun_Eq ctx (f₁ + g₁) (f₂ + g₂) := by
  intro x
  exact FPM_Add_Substitution ctx (f₁ x) (f₂ x) (g₁ x) (g₂ x) (hf x) (hg x)


/-- Exact shifted-context transport for function subtraction. -/
theorem FPM_CalcFun_Sub_Substitution
    (ctx : _root_.Context)
    (f₁ f₂ g₁ g₂ : FPM_CalcFun)
    (hf : FPM_CalcFun_Eq (shift_context_bin ctx FPM_Add) f₁ f₂)
    (hg : FPM_CalcFun_Eq (shift_context_bin ctx FPM_Add) (-g₁) (-g₂)) :
    FPM_CalcFun_Eq ctx (f₁ - g₁) (f₂ - g₂) := by
  simpa [Sub.sub] using
    FPM_CalcFun_Add_Substitution ctx f₁ f₂ (-g₁) (-g₂) hf hg


/-- Exact shifted-context transport for sequence negation. -/
theorem FPM_Sequence_Neg_Substitution
    (ctx : _root_.Context)
    (a b : FPM_Sequence)
    (h : FPM_Sequence_Eq (shift_context_unary ctx FPM_Neg) a b) :
    FPM_Sequence_Eq ctx (-a) (-b) := by
  intro n
  exact FPM_Unary_Substitution ctx FPM_Neg (a n) (b n) (h n)


/-- Exact shifted-context transport for sequence addition. -/
theorem FPM_Sequence_Add_Substitution
    (ctx : _root_.Context)
    (a₁ a₂ b₁ b₂ : FPM_Sequence)
    (ha : FPM_Sequence_Eq (shift_context_bin ctx FPM_Add) a₁ a₂)
    (hb : FPM_Sequence_Eq (shift_context_bin ctx FPM_Add) b₁ b₂) :
    FPM_Sequence_Eq ctx (a₁ + b₁) (a₂ + b₂) := by
  intro n
  exact FPM_Add_Substitution ctx (a₁ n) (a₂ n) (b₁ n) (b₂ n) (ha n) (hb n)


/-- Exact shifted-context transport for sequence subtraction. -/
theorem FPM_Sequence_Sub_Substitution
    (ctx : _root_.Context)
    (a₁ a₂ b₁ b₂ : FPM_Sequence)
    (ha : FPM_Sequence_Eq (shift_context_bin ctx FPM_Add) a₁ a₂)
    (hb : FPM_Sequence_Eq (shift_context_bin ctx FPM_Add) (-b₁) (-b₂)) :
    FPM_Sequence_Eq ctx (a₁ - b₁) (a₂ - b₂) := by
  simpa [Sub.sub] using
    FPM_Sequence_Add_Substitution ctx a₁ a₂ (-b₁) (-b₂) ha hb



/- Shifted-input transport ------------------------------------------ -/

/--
Support context for the shifted input `x + h`.
The base point `x` and increment `h` are both viewed under the addition
support context because `x + h` is formed by one real addition.
-/
def shift_context_calc_shift
    (ctx : _root_.Context) : _root_.Context :=
  shift_context_bin ctx FPM_Add


/-- Exact transport for shifted inputs `x + h`. -/
theorem FPM_Calc_shiftInput_Substitution
    (ctx : _root_.Context)
    (x₁ x₂ h₁ h₂ : FPM_Real)
    (hx : FPM_Eq (shift_context_calc_shift ctx) x₁ x₂)
    (hh : FPM_Eq (shift_context_calc_shift ctx) h₁ h₂) :
    FPM_Eq ctx
      (FPM_Calc_shiftInput x₁ h₁)
      (FPM_Calc_shiftInput x₂ h₂) := by
  simpa [FPM_Calc_shiftInput, shift_context_calc_shift] using
    (FPM_Add_Substitution ctx x₁ x₂ h₁ h₂ hx hh)


/-- Exact transport for the sequence of shifted inputs `x + h n`. -/
theorem FPM_Calc_shiftInput_Sequence_Substitution
    (ctx : _root_.Context)
    (x₁ x₂ : FPM_Real)
    (h₁ h₂ : FPM_Sequence)
    (hx : FPM_Eq (shift_context_calc_shift ctx) x₁ x₂)
    (hh : FPM_Sequence_Eq (shift_context_calc_shift ctx) h₁ h₂) :
    FPM_Sequence_Eq ctx
      (fun n => FPM_Calc_shiftInput x₁ (h₁ n))
      (fun n => FPM_Calc_shiftInput x₂ (h₂ n)) := by
  intro n
  exact FPM_Calc_shiftInput_Substitution ctx x₁ x₂ (h₁ n) (h₂ n) hx (hh n)



/- Boundedness helpers ---------------------------------------------- -/

theorem FPM_CalcFun_Bounded_neg {a : FPM_CalcFun} {C : ℕ+} :
    FPM_CalcFun_Bounded a C → FPM_CalcFun_Bounded (-a) C := by
  intro ha n
  simpa using FPM_Bounded_neg (ha n)

theorem FPM_Sequence_Bounded_neg {a : FPM_Sequence} {C : ℕ+} :
    FPM_Sequence_Bounded a C → FPM_Sequence_Bounded (-a) C := by
  intro ha n
  simpa using FPM_Bounded_neg (ha n)

/- ========================================================================
   SECTION 4: FORWARD-DIFFERENCE TRANSPORT
   We now transport the additive numerator of the difference quotient.
   The reciprocal factor h⁻¹ is delayed to the next section.
   ======================================================================== -/

/-- Evaluation of a calculus function along a base point and increment sequence. -/
def FPM_Calc_evalAlong
    (f : FPM_CalcFun) (x : FPM_Real) (h : FPM_Sequence) : FPM_Sequence :=
  fun n => f (x + h n)

/-- Sequence of forward differences along an increment sequence. -/
def FPM_Calc_forwardDiff_Seq
    (f : FPM_CalcFun) (x : FPM_Real) (h : FPM_Sequence) : FPM_Sequence :=
  fun n => FPM_Calc_forwardDiff f x (h n)

@[simp] theorem FPM_Calc_evalAlong_apply
    (f : FPM_CalcFun) (x : FPM_Real) (h : FPM_Sequence) (n : ℕ+) :
    FPM_Calc_evalAlong f x h n = f (x + h n) := rfl

@[simp] theorem FPM_Calc_forwardDiff_Seq_apply
    (f : FPM_CalcFun) (x : FPM_Real) (h : FPM_Sequence) (n : ℕ+) :
    FPM_Calc_forwardDiff_Seq f x h n = FPM_Calc_forwardDiff f x (h n) := rfl

/-- Pointwise transport of evaluation along a fixed base point and increment sequence. -/
theorem FPM_Calc_evalAlong_Substitution
    (ctx : _root_.Context)
    (f g : FPM_CalcFun)
    (x : FPM_Real) (h : FPM_Sequence)
    (hf : FPM_CalcFun_Eq ctx f g) :
    FPM_Sequence_Eq ctx
      (FPM_Calc_evalAlong f x h)
      (FPM_Calc_evalAlong g x h) := by
  intro n
  exact hf (x + h n)

/--
Support context for the positive term `f (x + h)` inside the forward difference.
This term is one summand of an outer addition.
-/
def shift_context_calc_forwardDiff_shift
    (ctx : _root_.Context) : _root_.Context :=
  shift_context_bin ctx FPM_Add

/--
Support context for the base-value term before outer negation in the forward difference.
We first negate `f x`, then add it to `f (x + h)`.
-/
def shift_context_calc_forwardDiff_base
    (ctx : _root_.Context) : _root_.Context :=
  shift_context_unary (shift_context_bin ctx FPM_Add) FPM_Neg

/-- Exact transport for a single forward difference. -/
theorem FPM_Calc_forwardDiff_Substitution
    (ctx : _root_.Context)
    (f g : FPM_CalcFun)
    (x h : FPM_Real)
    (hshift :
      FPM_Eq (shift_context_calc_forwardDiff_shift ctx)
        (f (FPM_Calc_shiftInput x h))
        (g (FPM_Calc_shiftInput x h)))
    (hbase :
      FPM_Eq (shift_context_calc_forwardDiff_base ctx)
        (f x) (g x)) :
    FPM_Eq ctx
      (FPM_Calc_forwardDiff f x h)
      (FPM_Calc_forwardDiff g x h) := by
  have hneg :
      FPM_Eq (shift_context_calc_forwardDiff_shift ctx)
        (-(f x)) (-(g x)) := by
    simpa [shift_context_calc_forwardDiff_base] using
      (FPM_Unary_Substitution
        (shift_context_calc_forwardDiff_shift ctx)
        FPM_Neg
        (f x) (g x) hbase)
  simpa [FPM_Calc_forwardDiff, FPM_Calc_shiftInput,
    shift_context_calc_forwardDiff_shift] using
    (FPM_Add_Substitution
      ctx
      (f (FPM_Calc_shiftInput x h))
      (g (FPM_Calc_shiftInput x h))
      (-(f x))
      (-(g x))
      hshift hneg)

/-- Forward-difference transport from split function-equality hypotheses. -/
theorem FPM_Calc_forwardDiff_Substitution_ofFunEq
    (ctx : _root_.Context)
    (f g : FPM_CalcFun)
    (x h : FPM_Real)
    (hshift :
      FPM_CalcFun_Eq (shift_context_calc_forwardDiff_shift ctx) f g)
    (hbase :
      FPM_CalcFun_Eq (shift_context_calc_forwardDiff_base ctx) f g) :
    FPM_Eq ctx
      (FPM_Calc_forwardDiff f x h)
      (FPM_Calc_forwardDiff g x h) := by
  exact FPM_Calc_forwardDiff_Substitution
    ctx f g x h
    (hshift (FPM_Calc_shiftInput x h))
    (hbase x)

/-- Exact sequence transport for forward differences along a fixed increment sequence. -/
theorem FPM_Calc_forwardDiff_Sequence_Substitution_ofFunEq
    (ctx : _root_.Context)
    (f g : FPM_CalcFun)
    (x : FPM_Real)
    (h : FPM_Sequence)
    (hshift :
      FPM_CalcFun_Eq (shift_context_calc_forwardDiff_shift ctx) f g)
    (hbase :
      FPM_CalcFun_Eq (shift_context_calc_forwardDiff_base ctx) f g) :
    FPM_Sequence_Eq ctx
      (FPM_Calc_forwardDiff_Seq f x h)
      (FPM_Calc_forwardDiff_Seq g x h) := by
  intro n
  exact FPM_Calc_forwardDiff_Substitution_ofFunEq
    ctx f g x (h n) hshift hbase

/- ========================================================================
   SECTION 5: GUARDED DIFFERENCE-QUOTIENT TRANSPORT

   We now transport the full formal difference quotient.
   This is the first genuinely guarded calculus section:
   - the numerator is the forward difference from Section 4,
   - the reciprocal factor is treated as an explicit support hypothesis,
   - the final target context reflects the inversion tail cost.
   ======================================================================== -/

/-- Final target context for a difference quotient after the inversion tail cost. -/
def FPM_Calc_diffQuot_Target
    (ctx : _root_.Context) (N_safe : ℕ+) : _root_.Context :=
  ⟨ctx.M, max ctx.N N_safe⟩

@[simp] theorem FPM_Calc_diffQuot_Target_M
    (ctx : _root_.Context) (N_safe : ℕ+) :
    (FPM_Calc_diffQuot_Target ctx N_safe).M = ctx.M := rfl

@[simp] theorem FPM_Calc_diffQuot_Target_N
    (ctx : _root_.Context) (N_safe : ℕ+) :
    (FPM_Calc_diffQuot_Target ctx N_safe).N = max ctx.N N_safe := rfl

/--
Support context for the forward-difference numerator inside the final quotient.

This is the multiplication-support context over the quotient target.
-/
def shift_context_calc_diffQuot_num
    (ctx : _root_.Context) (N_safe C : ℕ+) : _root_.Context :=
  shift_context_mul (FPM_Calc_diffQuot_Target ctx N_safe) C

/--
Support context for the reciprocal increment factor inside the final quotient.

It is named separately, even though it is the same multiplication-support
context as the numerator, because the two roles are conceptually different.
-/
def shift_context_calc_diffQuot_den
    (ctx : _root_.Context) (N_safe C : ℕ+) : _root_.Context :=
  shift_context_mul (FPM_Calc_diffQuot_Target ctx N_safe) C

@[simp] theorem shift_context_calc_diffQuot_num_def
    (ctx : _root_.Context) (N_safe C : ℕ+) :
    shift_context_calc_diffQuot_num ctx N_safe C =
      shift_context_mul (FPM_Calc_diffQuot_Target ctx N_safe) C := rfl

@[simp] theorem shift_context_calc_diffQuot_den_def
    (ctx : _root_.Context) (N_safe C : ℕ+) :
    shift_context_calc_diffQuot_den ctx N_safe C =
      shift_context_mul (FPM_Calc_diffQuot_Target ctx N_safe) C := rfl

/--
Exact guarded transport for a single formal difference quotient.

This theorem is intentionally explicit:
- the numerator equality is supplied at the quotient multiplication support,
- the reciprocal increment equality is supplied at the same support,
- boundedness of both factors is also explicit.
-/
theorem FPM_Calc_diffQuot_Substitution
    (ctx : _root_.Context)
    (N_safe C : ℕ+)
    (f g : FPM_CalcFun)
    (x h : FPM_Real)
    (hnum :
      FPM_Eq (shift_context_calc_diffQuot_num ctx N_safe C)
        (FPM_Calc_forwardDiff f x h)
        (FPM_Calc_forwardDiff g x h))
    (hden :
      FPM_Eq (shift_context_calc_diffQuot_den ctx N_safe C)
        (h⁻¹) (h⁻¹))
    (hnum_bd : FPM_Bounded (FPM_Calc_forwardDiff f x h) C)
    (hden_bd : FPM_Bounded (h⁻¹) C) :
    FPM_Eq (FPM_Calc_diffQuot_Target ctx N_safe)
      (FPM_Calc_diffQuot f x h)
      (FPM_Calc_diffQuot g x h) := by
  simpa [FPM_Calc_diffQuot,
    shift_context_calc_diffQuot_num,
    shift_context_calc_diffQuot_den] using
    (FPM_Mul_Substitution
      (FPM_Calc_diffQuot_Target ctx N_safe)
      C
      (FPM_Calc_forwardDiff f x h)
      (FPM_Calc_forwardDiff g x h)
      (h⁻¹)
      (h⁻¹)
      hnum_bd
      hden_bd
      hnum
      hden)

/--
Difference-quotient transport from split numerator data.

This packages the Section 4 forward-difference theorem into the numerator slot,
leaving only the reciprocal support proof and boundedness hypotheses explicit.
-/
theorem FPM_Calc_diffQuot_Substitution_ofSplit
    (ctx : _root_.Context)
    (N_safe C : ℕ+)
    (f g : FPM_CalcFun)
    (x h : FPM_Real)
    (hshift :
      FPM_CalcFun_Eq
        (shift_context_calc_forwardDiff_shift
          (shift_context_calc_diffQuot_num ctx N_safe C))
        f g)
    (hbase :
      FPM_CalcFun_Eq
        (shift_context_calc_forwardDiff_base
          (shift_context_calc_diffQuot_num ctx N_safe C))
        f g)
    (hden :
      FPM_Eq (shift_context_calc_diffQuot_den ctx N_safe C)
        (h⁻¹) (h⁻¹))
    (hnum_bd : FPM_Bounded (FPM_Calc_forwardDiff f x h) C)
    (hden_bd : FPM_Bounded (h⁻¹) C) :
    FPM_Eq (FPM_Calc_diffQuot_Target ctx N_safe)
      (FPM_Calc_diffQuot f x h)
      (FPM_Calc_diffQuot g x h) := by
  have hnum :
      FPM_Eq (shift_context_calc_diffQuot_num ctx N_safe C)
        (FPM_Calc_forwardDiff f x h)
        (FPM_Calc_forwardDiff g x h) := by
    exact
      FPM_Calc_forwardDiff_Substitution_ofFunEq
        (shift_context_calc_diffQuot_num ctx N_safe C)
        f g x h hshift hbase
  exact
    FPM_Calc_diffQuot_Substitution
      ctx N_safe C f g x h
      hnum hden hnum_bd hden_bd

/--
Sequence form of guarded difference-quotient transport, with explicit
pointwise support data for the reciprocal factor.
-/
theorem FPM_Calc_diffQuot_Sequence_Substitution_ofSplit
    (ctx : _root_.Context)
    (N_safe C : ℕ+)
    (f g : FPM_CalcFun)
    (x : FPM_Real)
    (h : FPM_Sequence)
    (hshift :
      FPM_CalcFun_Eq
        (shift_context_calc_forwardDiff_shift
          (shift_context_calc_diffQuot_num ctx N_safe C))
        f g)
    (hbase :
      FPM_CalcFun_Eq
        (shift_context_calc_forwardDiff_base
          (shift_context_calc_diffQuot_num ctx N_safe C))
        f g)
    (hden :
      ∀ n : ℕ+,
        FPM_Eq (shift_context_calc_diffQuot_den ctx N_safe C)
          ((h n)⁻¹) ((h n)⁻¹))
    (hnum_bd :
      ∀ n : ℕ+, FPM_Bounded (FPM_Calc_forwardDiff f x (h n)) C)
    (hden_bd :
      ∀ n : ℕ+, FPM_Bounded ((h n)⁻¹) C) :
    FPM_Sequence_Eq (FPM_Calc_diffQuot_Target ctx N_safe)
      (fun n => FPM_Calc_diffQuot f x (h n))
      (fun n => FPM_Calc_diffQuot g x (h n)) := by
  intro n
  exact
    FPM_Calc_diffQuot_Substitution_ofSplit
      ctx N_safe C f g x (h n)
      hshift hbase
      (hden n)
      (hnum_bd n)
      (hden_bd n)

/- ========================================================================
   SECTION 6: LIMIT AND DERIVATIVE PACKAGING

   This section does not add new asymptotic strength.
   Instead, it packages the structural predicates from Section 2 into:
   - constant-sequence form,
   - constructor/eliminator lemmas,
   - sequence-level aliases for limit and derivative expressions.
   ======================================================================== -/

/-- Constant sequences in the calculus layer. -/
def FPM_Calc_constSeq (ℓ : FPM_Real) : FPM_Sequence :=
  fun _ => ℓ

/-- The shifted-value sequence `n ↦ f (x + h n)`. -/
def FPM_Calc_shifted_Seq
    (f : FPM_CalcFun) (x : FPM_Real) (h : FPM_Sequence) : FPM_Sequence :=
  fun n => f (x + h n)

/-- The difference-quotient sequence `n ↦ ((f(x+h_n)-f(x)) * (h_n)⁻¹)`. -/
def FPM_Calc_diffQuot_Seq
    (f : FPM_CalcFun) (x : FPM_Real) (h : FPM_Sequence) : FPM_Sequence :=
  fun n => FPM_Calc_diffQuot f x (h n)

@[simp] theorem FPM_Calc_constSeq_apply
    (ℓ : FPM_Real) (n : ℕ+) :
    FPM_Calc_constSeq ℓ n = ℓ := rfl

@[simp] theorem FPM_Calc_shifted_Seq_apply
    (f : FPM_CalcFun) (x : FPM_Real) (h : FPM_Sequence) (n : ℕ+) :
    FPM_Calc_shifted_Seq f x h n = f (x + h n) := rfl

@[simp] theorem FPM_Calc_diffQuot_Seq_apply
    (f : FPM_CalcFun) (x : FPM_Real) (h : FPM_Sequence) (n : ℕ+) :
    FPM_Calc_diffQuot_Seq f x h n = FPM_Calc_diffQuot f x (h n) := rfl


/- Constant-sequence reformulations ---------------------------------- -/


theorem FPM_Sequence_Limit_iff_constSeq
    {ctx : _root_.Context} {a : FPM_Sequence} {ℓ : FPM_Real} :
    FPM_Sequence_Limit ctx a ℓ ↔
      FPM_Sequence_Eq ctx a (FPM_Calc_constSeq ℓ) := by
  constructor
  · intro h n
    simpa [FPM_Calc_constSeq] using h n
  · intro h n
    simpa [FPM_Calc_constSeq] using h n


theorem FPM_CalcFun_LimitAlong_iff_constSeq
    {ctx : _root_.Context}
    {f : FPM_CalcFun} {x : FPM_Real}
    {h : FPM_Sequence} {ℓ : FPM_Real} :
    FPM_CalcFun_LimitAlong ctx f x h ℓ ↔
      FPM_Sequence_Eq ctx (FPM_Calc_shifted_Seq f x h) (FPM_Calc_constSeq ℓ) := by
  simpa [FPM_CalcFun_LimitAlong, FPM_Calc_shifted_Seq] using
    (FPM_Sequence_Limit_iff_constSeq
      (ctx := ctx) (a := fun n => f (x + h n)) (ℓ := ℓ))


theorem FPM_CalcFun_DerivAlong_iff_constSeq
    {ctx : _root_.Context}
    {f : FPM_CalcFun} {x : FPM_Real}
    {h : FPM_Sequence} {d : FPM_Real} :
    FPM_CalcFun_DerivAlong ctx f x h d ↔
      FPM_Sequence_Eq ctx (FPM_Calc_diffQuot_Seq f x h) (FPM_Calc_constSeq d) := by
  simpa [FPM_CalcFun_DerivAlong, FPM_Calc_diffQuot_Seq] using
    (FPM_Sequence_Limit_iff_constSeq
      (ctx := ctx) (a := fun n => FPM_Calc_diffQuot f x (h n)) (ℓ := d))


theorem FPM_CalcFun_DerivAlong_Guarded_iff
    {ctx : _root_.Context}
    {f : FPM_CalcFun} {x : FPM_Real}
    {h : FPM_Sequence} {L N_safe : ℕ+} {d : FPM_Real} :
    FPM_CalcFun_DerivAlong_Guarded ctx f x h L N_safe d ↔
      (∀ n : ℕ+, FPM_EventuallyApart (h n) L N_safe) ∧
      FPM_Sequence_Eq ctx (FPM_Calc_diffQuot_Seq f x h) (FPM_Calc_constSeq d) := by
  constructor
  · intro hd
    refine ⟨hd.1, ?_⟩
    simpa [FPM_CalcFun_DerivAlong_iff_constSeq] using hd.2
  · intro hd
    refine ⟨hd.1, ?_⟩
    simpa [FPM_CalcFun_DerivAlong_iff_constSeq] using hd.2


/- Constructors ------------------------------------------------------- -/


theorem FPM_Calc_constSeq_Eq_mk
    {ctx : _root_.Context} {a b : FPM_Real}
    (h : FPM_Eq ctx a b) :
    FPM_Sequence_Eq ctx (FPM_Calc_constSeq a) (FPM_Calc_constSeq b) := by
  intro n
  simpa [FPM_Calc_constSeq] using h


theorem FPM_Sequence_Limit_of_constSeqEq
    {ctx : _root_.Context} {a : FPM_Sequence} {ℓ : FPM_Real}
    (h : FPM_Sequence_Eq ctx a (FPM_Calc_constSeq ℓ)) :
    FPM_Sequence_Limit ctx a ℓ := by
  intro n
  simpa [FPM_Calc_constSeq] using h n


theorem FPM_CalcFun_LimitAlong_mk
    {ctx : _root_.Context}
    {f : FPM_CalcFun} {x : FPM_Real}
    {h : FPM_Sequence} {ℓ : FPM_Real}
    (hlim :
      FPM_Sequence_Eq ctx
        (FPM_Calc_shifted_Seq f x h)
        (FPM_Calc_constSeq ℓ)) :
    FPM_CalcFun_LimitAlong ctx f x h ℓ := by
  simpa [FPM_CalcFun_LimitAlong_iff_constSeq] using hlim


theorem FPM_CalcFun_DerivAlong_mk
    {ctx : _root_.Context}
    {f : FPM_CalcFun} {x : FPM_Real}
    {h : FPM_Sequence} {d : FPM_Real}
    (hd :
      FPM_Sequence_Eq ctx
        (FPM_Calc_diffQuot_Seq f x h)
        (FPM_Calc_constSeq d)) :
    FPM_CalcFun_DerivAlong ctx f x h d := by
  simpa [FPM_CalcFun_DerivAlong_iff_constSeq] using hd


theorem FPM_CalcFun_DerivAlong_Guarded_mk
    {ctx : _root_.Context}
    {f : FPM_CalcFun} {x : FPM_Real}
    {h : FPM_Sequence} {L N_safe : ℕ+} {d : FPM_Real}
    (hapart : ∀ n : ℕ+, FPM_EventuallyApart (h n) L N_safe)
    (hd :
      FPM_Sequence_Eq ctx
        (FPM_Calc_diffQuot_Seq f x h)
        (FPM_Calc_constSeq d)) :
    FPM_CalcFun_DerivAlong_Guarded ctx f x h L N_safe d := by
  exact ⟨hapart, by simpa [FPM_CalcFun_DerivAlong_iff_constSeq] using hd⟩


/- Eliminators -------------------------------------------------------- -/


@[simp] theorem FPM_CalcFun_LimitAlong_app
    {ctx : _root_.Context}
    {f : FPM_CalcFun} {x : FPM_Real}
    {h : FPM_Sequence} {ℓ : FPM_Real}
    (hlim : FPM_CalcFun_LimitAlong ctx f x h ℓ) (n : ℕ+) :
    FPM_Eq ctx (FPM_Calc_shifted_Seq f x h n) ℓ := by
  simpa [FPM_Calc_shifted_Seq, FPM_CalcFun_LimitAlong] using hlim n


@[simp] theorem FPM_CalcFun_DerivAlong_app
    {ctx : _root_.Context}
    {f : FPM_CalcFun} {x : FPM_Real}
    {h : FPM_Sequence} {d : FPM_Real}
    (hd : FPM_CalcFun_DerivAlong ctx f x h d) (n : ℕ+) :
    FPM_Eq ctx (FPM_Calc_diffQuot_Seq f x h n) d := by
  simpa [FPM_Calc_diffQuot_Seq, FPM_CalcFun_DerivAlong] using hd n


@[simp] theorem FPM_CalcFun_DerivAlong_Guarded_app
    {ctx : _root_.Context}
    {f : FPM_CalcFun} {x : FPM_Real}
    {h : FPM_Sequence} {L N_safe : ℕ+} {d : FPM_Real}
    (hd : FPM_CalcFun_DerivAlong_Guarded ctx f x h L N_safe d) (n : ℕ+) :
    FPM_Eq ctx (FPM_Calc_diffQuot_Seq f x h n) d := by
  exact FPM_CalcFun_DerivAlong_app hd.2 n


/- Sequence aliases from earlier sections ----------------------------- -/


theorem FPM_CalcFun_LimitAlong_of_evalAlongEqConst
    {ctx : _root_.Context}
    {f : FPM_CalcFun} {x : FPM_Real}
    {h : FPM_Sequence} {ℓ : FPM_Real}
    (hlim :
      FPM_Sequence_Eq ctx
        (FPM_Calc_evalAlong f x h)
        (FPM_Calc_constSeq ℓ)) :
    FPM_CalcFun_LimitAlong ctx f x h ℓ := by
  exact FPM_CalcFun_LimitAlong_mk (by simpa [FPM_Calc_evalAlong, FPM_Calc_shifted_Seq] using hlim)


theorem FPM_CalcFun_DerivAlong_of_diffQuotSeqEqConst
    {ctx : _root_.Context}
    {f : FPM_CalcFun} {x : FPM_Real}
    {h : FPM_Sequence} {d : FPM_Real}
    (hd :
      FPM_Sequence_Eq ctx
        (FPM_Calc_diffQuot_Seq f x h)
        (FPM_Calc_constSeq d)) :
    FPM_CalcFun_DerivAlong ctx f x h d := by
  exact FPM_CalcFun_DerivAlong_mk hd

/- ========================================================================
   SECTION 7: PUBLIC WRAPPERS AND SMOKE TESTS
   ======================================================================== -/


/- Public wrappers: limits ------------------------------------------- -/

theorem FPM_CalcFun_LimitAlongSubstitution_toConst
    {ctx : _root_.Context}
    {f : FPM_CalcFun} {x : FPM_Real} {h : FPM_Sequence} {ℓ : FPM_Real}
    (hfg :
      FPM_Sequence_Eq ctx
        (FPM_Calc_shifted_Seq f x h)
        (FPM_Calc_constSeq ℓ)) :
    FPM_CalcFun_LimitAlong ctx f x h ℓ := by
  exact FPM_CalcFun_LimitAlong_mk hfg

theorem FPM_CalcFun_LimitAlongSubstitution_const
    {ctx : _root_.Context}
    {f : FPM_CalcFun} {x : FPM_Real} {h : FPM_Sequence} {ℓ : FPM_Real}
    (hlim : FPM_CalcFun_LimitAlong ctx f x h ℓ) :
    FPM_Sequence_Eq ctx
      (FPM_Calc_shifted_Seq f x h)
      (FPM_Calc_constSeq ℓ) := by
  simpa [FPM_CalcFun_LimitAlong_iff_constSeq] using hlim


/- Public wrappers: derivatives -------------------------------------- -/

theorem FPM_CalcFun_DerivAlongSubstitution_toConst
    {ctx : _root_.Context}
    {f : FPM_CalcFun} {x : FPM_Real} {h : FPM_Sequence} {d : FPM_Real}
    (hd :
      FPM_Sequence_Eq ctx
        (FPM_Calc_diffQuot_Seq f x h)
        (FPM_Calc_constSeq d)) :
    FPM_CalcFun_DerivAlong ctx f x h d := by
  exact FPM_CalcFun_DerivAlong_mk hd

theorem FPM_CalcFun_DerivAlongSubstitution_const
    {ctx : _root_.Context}
    {f : FPM_CalcFun} {x : FPM_Real} {h : FPM_Sequence} {d : FPM_Real}
    (hd : FPM_CalcFun_DerivAlong ctx f x h d) :
    FPM_Sequence_Eq ctx
      (FPM_Calc_diffQuot_Seq f x h)
      (FPM_Calc_constSeq d) := by
  simpa [FPM_CalcFun_DerivAlong_iff_constSeq] using hd

theorem FPM_CalcFun_DerivAlong_Guarded_ofGuard
    {ctx : _root_.Context}
    {f : FPM_CalcFun} {x : FPM_Real}
    {h : FPM_Sequence} {L N_safe : ℕ+} {d : FPM_Real}
    (hapart : ∀ n : ℕ+, FPM_EventuallyApart (h n) L N_safe)
    (hd : FPM_CalcFun_DerivAlong ctx f x h d) :
    FPM_CalcFun_DerivAlong_Guarded ctx f x h L N_safe d := by
  exact ⟨hapart, hd⟩

theorem FPM_CalcFun_DerivAlong_ofGuarded
    {ctx : _root_.Context}
    {f : FPM_CalcFun} {x : FPM_Real}
    {h : FPM_Sequence} {L N_safe : ℕ+} {d : FPM_Real}
    (hd : FPM_CalcFun_DerivAlong_Guarded ctx f x h L N_safe d) :
    FPM_CalcFun_DerivAlong ctx f x h d := by
  exact hd.2


/- Reduced core forms ------------------------------------------------ -/

theorem FPM_CalcFun_DerivAlong_Guarded_core
    {ctx : _root_.Context}
    {f : FPM_CalcFun} {x : FPM_Real}
    {h : FPM_Sequence} {L N_safe : ℕ+} {d : FPM_Real} :
    FPM_CalcFun_DerivAlong_Guarded ctx f x h L N_safe d ↔
      (∀ n : ℕ+, FPM_EventuallyApart (h n) L N_safe) ∧
      FPM_CalcFun_DerivAlong ctx f x h d := by
  rfl

theorem FPM_CalcFun_DerivAlong_Guarded_constCore
    {ctx : _root_.Context}
    {f : FPM_CalcFun} {x : FPM_Real}
    {h : FPM_Sequence} {L N_safe : ℕ+} {d : FPM_Real}
    (hd : FPM_CalcFun_DerivAlong_Guarded ctx f x h L N_safe d) :
    (∀ n : ℕ+, FPM_EventuallyApart (h n) L N_safe) ∧
    FPM_Sequence_Eq ctx
      (FPM_Calc_diffQuot_Seq f x h)
      (FPM_Calc_constSeq d) := by
  refine ⟨hd.1, ?_⟩
  simpa [FPM_CalcFun_DerivAlong_iff_constSeq] using hd.2

theorem FPM_CalcFun_DerivAlong_Guarded_ofConstCore
    {ctx : _root_.Context}
    {f : FPM_CalcFun} {x : FPM_Real}
    {h : FPM_Sequence} {L N_safe : ℕ+} {d : FPM_Real}
    (hd :
      (∀ n : ℕ+, FPM_EventuallyApart (h n) L N_safe) ∧
      FPM_Sequence_Eq ctx
        (FPM_Calc_diffQuot_Seq f x h)
        (FPM_Calc_constSeq d)) :
    FPM_CalcFun_DerivAlong_Guarded ctx f x h L N_safe d := by
  exact FPM_CalcFun_DerivAlong_Guarded_mk hd.1 hd.2


/- Compatibility wrappers ------------------------------------------- -/

theorem FPM_CalcFun_DerivAlong_of_diffQuotEqConst
    {ctx : _root_.Context}
    {f : FPM_CalcFun} {x : FPM_Real}
    {h : FPM_Sequence} {d : FPM_Real}
    (hd :
      FPM_Sequence_Eq ctx
        (fun n => FPM_Calc_diffQuot f x (h n))
        (FPM_Calc_constSeq d)) :
    FPM_CalcFun_DerivAlong ctx f x h d := by
  have hd' :
      FPM_Sequence_Eq ctx
        (FPM_Calc_diffQuot_Seq f x h)
        (FPM_Calc_constSeq d) := by
    intro n
    simpa [FPM_Calc_diffQuot_Seq] using hd n
  exact FPM_CalcFun_DerivAlong_mk hd'


/- Smoke tests ------------------------------------------------------- -/

example
    {ctx : _root_.Context}
    {f : FPM_CalcFun} {x : FPM_Real}
    {h : FPM_Sequence} {ℓ : FPM_Real}
    (hlim :
      FPM_Sequence_Eq ctx
        (FPM_Calc_shifted_Seq f x h)
        (FPM_Calc_constSeq ℓ)) :
    FPM_CalcFun_LimitAlong ctx f x h ℓ := by
  exact FPM_CalcFun_LimitAlongSubstitution_toConst hlim

example
    {ctx : _root_.Context}
    {f : FPM_CalcFun} {x : FPM_Real}
    {h : FPM_Sequence} {d : FPM_Real}
    (hd :
      FPM_Sequence_Eq ctx
        (FPM_Calc_diffQuot_Seq f x h)
        (FPM_Calc_constSeq d)) :
    FPM_CalcFun_DerivAlong ctx f x h d := by
  exact FPM_CalcFun_DerivAlongSubstitution_toConst hd

example
    {ctx : _root_.Context}
    {f : FPM_CalcFun} {x : FPM_Real}
    {h : FPM_Sequence} {L N_safe : ℕ+} {d : FPM_Real}
    (hapart : ∀ n : ℕ+, FPM_EventuallyApart (h n) L N_safe)
    (hd : FPM_CalcFun_DerivAlong ctx f x h d) :
    FPM_CalcFun_DerivAlong_Guarded ctx f x h L N_safe d := by
  exact FPM_CalcFun_DerivAlong_Guarded_ofGuard hapart hd

example
    {ctx : _root_.Context}
    {f : FPM_CalcFun} {x : FPM_Real}
    {h : FPM_Sequence} {L N_safe : ℕ+} {d : FPM_Real}
    (hd :
      (∀ n : ℕ+, FPM_EventuallyApart (h n) L N_safe) ∧
      FPM_Sequence_Eq ctx
        (FPM_Calc_diffQuot_Seq f x h)
        (FPM_Calc_constSeq d)) :
    FPM_CalcFun_DerivAlong_Guarded ctx f x h L N_safe d := by
  exact FPM_CalcFun_DerivAlong_Guarded_ofConstCore hd

theorem FPM_Sequence_Limit_neg
    {ctx : _root_.Context} {a : FPM_Sequence} {ℓ : FPM_Real}
    (h : FPM_Sequence_Limit ctx a ℓ) :
    FPM_Sequence_Limit ctx (-a) (-ℓ) := by
  intro n
  have hneg : FPM_Eq ctx (-(a n)) (-ℓ) :=
    FPM_Neg_Substitution ctx (a n) ℓ (by simpa [shift_context_unary, FPM_Neg] using h n)
  simpa [FPM_Sequence_neg_apply] using hneg

/-
PROBLEM
In the new axiom system, `FPM_Real` is a structure, so propositional
    equality (`=`) of two `FPM_Real` values requires equality of `seq`,
    `mod`, and `stable` fields. The weaker statement below asserts
    pointwise equality of the underlying sequences instead.

PROVIDED SOLUTION
Unfold FPM_Calc_diffQuot, FPM_Calc_forwardDiff, FPM_Calc_shiftInput, and all the
arithmetic operations down to their .seq definitions. Both sides should reduce to
rational arithmetic expressions that are equal by ring.
-/
theorem FPM_Calc_diffQuot_neg_seq
    (f : FPM_CalcFun) (x h : FPM_Real) (n : ℕ+) :
    (FPM_Calc_diffQuot (-f) x h).seq n = (-FPM_Calc_diffQuot f x h).seq n := by
  -- By definition of subtraction, we have -(f x) = -f x and (x + h) - x = h.
  simp [FPM_Calc_diffQuot, FPM_Calc_forwardDiff, FPM_Calc_shiftInput] at *;
  ring

/-
PROVIDED SOLUTION
Use FPM_Calc_diffQuot_neg_seq and the definitions of FPM_Calc_diffQuot_Seq_apply
and FPM_Sequence_neg_apply.
-/
theorem FPM_Calc_diffQuot_Seq_neg_seq
    (f : FPM_CalcFun) (x : FPM_Real) (h : FPM_Sequence) (n : ℕ+) (k : ℕ+) :
    (FPM_Calc_diffQuot_Seq (-f) x h n).seq k = ((-FPM_Calc_diffQuot_Seq f x h) n).seq k := by
  simp +decide [ FPM_Calc_diffQuot_Seq, FPM_Calc_diffQuot ];
  ring

theorem FPM_CalcFun_LimitAlong_neg
    {ctx : _root_.Context} {f : FPM_CalcFun} {x : FPM_Real}
    {h : FPM_Sequence} {ℓ : FPM_Real}
    (hf : FPM_CalcFun_LimitAlong ctx f x h ℓ) :
    FPM_CalcFun_LimitAlong ctx (-f) x h (-ℓ) := by
  have hneg : FPM_Sequence_Limit ctx (-(FPM_Calc_shifted_Seq f x h)) (-ℓ) :=
    FPM_Sequence_Limit_neg
      (a := FPM_Calc_shifted_Seq f x h) (ℓ := ℓ)
      (by simpa [FPM_CalcFun_LimitAlong, FPM_Calc_shifted_Seq] using hf)
  simpa [FPM_CalcFun_LimitAlong, FPM_Calc_shifted_Seq,
         FPM_CalcFun_neg_apply, FPM_Sequence_neg_apply] using hneg

/-
PROVIDED SOLUTION
We have h1 : FPM_Eq ctx (-(FPM_Calc_diffQuot f x (h n))) (-d). We need to
show FPM_Eq ctx (FPM_Calc_diffQuot (-f) x (h n)) (-d). These two LHS differ pointwise
by FPM_Calc_diffQuot_neg_seq. So for any k ≥ ctx.N, the overlap witness from h1 works
because the intervals have the same center (by the seq equality).
Unfold FPM_Eq and FPM_Interval, get a witness from h1, and rewrite the interval
membership using FPM_Calc_diffQuot_neg_seq.
-/
theorem FPM_CalcFun_DerivAlong_neg
    {ctx : _root_.Context} {f : FPM_CalcFun} {x : FPM_Real}
    {h : FPM_Sequence} {d : FPM_Real}
    (hf : FPM_CalcFun_DerivAlong ctx f x h d) :
    FPM_CalcFun_DerivAlong ctx (-f) x h (-d) := by
  have hneg : FPM_Sequence_Limit ctx (-(FPM_Calc_diffQuot_Seq f x h)) (-d) :=
    FPM_Sequence_Limit_neg
      (a := FPM_Calc_diffQuot_Seq f x h) (ℓ := d)
      (by simpa [FPM_CalcFun_DerivAlong, FPM_Calc_diffQuot_Seq] using hf)
  simp only [FPM_CalcFun_DerivAlong_def]
  intro n
  have h1 : FPM_Eq ctx (-(FPM_Calc_diffQuot f x (h n))) (-d) := by
    simpa [FPM_Sequence_neg_apply, FPM_Calc_diffQuot_Seq_apply] using hneg n
  -- In the new axiom system, we need to show the goals are observationally
  -- equal rather than propositionally equal. The sequences agree pointwise.
  intro k hk;
  convert h1 k hk using 1 ; unfold FPM_Interval ; ring_nf;
  congr! 2 ; exact FPM_Calc_diffQuot_neg_seq f x ( h n ) k ▸ rfl;

theorem FPM_CalcFun_DerivAlong_Guarded_neg
    {ctx : _root_.Context} {f : FPM_CalcFun} {x : FPM_Real}
    {h : FPM_Sequence} {L N_safe : ℕ+} {d : FPM_Real}
    (hf : FPM_CalcFun_DerivAlong_Guarded ctx f x h L N_safe d) :
    FPM_CalcFun_DerivAlong_Guarded ctx (-f) x h L N_safe (-d) :=
  ⟨hf.1, FPM_CalcFun_DerivAlong_neg hf.2⟩

end
