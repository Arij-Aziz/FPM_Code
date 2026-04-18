import Mathlib

/-!
  # Phase 1: FPM Core Primitives
  The foundational bedrock of Finitary Physical Mathematics.

  Philosophical Acknowledgment:
  The core generative and thermodynamic mechanics of FPM were developed
  independently. However, the philosophical mechanism for bridging this
  finitary system to classical ZFC mathematics—specifically the use of
  structural constants and asymptotic identity to bypass actual infinity—is
  directly inspired by Jiuzhang Constructive Mathematics (JCM). We credit
  JCM for the theoretical foundation of the classical bridge implemented here.
-/

/-- PRIMITIVE 1: THE PRECISION BUDGET
  A context defines the precision budget for a given measurement.
  `M` determines the spatial resolution (radius = 1 / 2M).
  `N` determines the temporal resolution (the tail index).
-/
structure Context where
  M : ℕ+
  N : ℕ+

/-- PRIMITIVE 2: THE STABILIZED GENERATOR
  A 'Real' is an indefinite generative procedure mapping temporal steps
  to rational approximations.
  To represent a measurable physical quantity, the procedure must
  explicitly state its own thermodynamic stabilization rate.
-/
structure FPM_Real where
  seq : ℕ+ → ℚ
  -- The thermodynamic stabilization rate: given spatial budget M,
  -- it returns the temporal step N where the sequence stabilizes.
  mod : ℕ+ → ℕ+
  stable : ∀ (M : ℕ+) (n m : ℕ+),
    n ≥ mod M → m ≥ mod M → abs (seq n - seq m) ≤ (1 : ℚ) / M

/-- PRIMITIVE 3: THE GLOBAL CONSTANTS (The JCM Bridge Components)
  The structural zeroes and ones that ZFC translations and standard algebra require.
  Because their sequences are constant, their stabilization modulus is trivially 1.
-/
def FPM_Zero : FPM_Real :=
  { seq := fun _ => 0,
    mod := fun _ => 1,
    stable := by
      intros M n m hn hm
      simp only [sub_self, abs_zero]
      exact div_nonneg zero_le_one (by positivity) }

def FPM_One : FPM_Real :=
  { seq := fun _ => 1,
    mod := fun _ => 1,
    stable := by
      intros M n m hn hm
      simp only [sub_self, abs_zero]
      exact div_nonneg zero_le_one (by positivity) }

/-- PRIMITIVE 4: THE INTERNAL VIEW
  At step `n`, an `FPM_Real` defines a closed interval of potentiality.
-/
def FPM_Interval (ctx : Context) (a : FPM_Real) (n : ℕ+) : Set ℚ :=
  { q | abs (q - a.seq n) ≤ (1 : ℚ) / (2 * (ctx.M : ℚ)) }

/-- PRIMITIVE 5: OBSERVATIONAL OVERLAP (Tolerance)
  Used to track strict thermodynamic error bounds during physical
  operations. (Non-transitive at a fixed context).
-/
def FPM_Eq (ctx : Context) (a b : FPM_Real) : Prop :=
  ∀ n ≥ ctx.N, (FPM_Interval ctx a n ∩ FPM_Interval ctx b n).Nonempty

/-- PRIMITIVE 6: EXACT IDENTITY (The JCM-Inspired Classical Bridge)
  Mathematical identity. Two procedures are identical if they can be forced
  to overlap at any arbitrary spatial resolution M by waiting long enough.
  This forms a true Equivalence Relation, allowing `Eq.trans` in the tactic
  engine at zero thermodynamic cost.
-/
def FPM_ExactEq (a b : FPM_Real) : Prop :=
  ∀ M : ℕ+, ∃ N : ℕ+, FPM_Eq { M := M, N := N } a b

/-- PRIMITIVE 7: THERMODYNAMICALLY BOUNDED FUNCTIONS
  The core computational safety guarantee: bounded error expansion.
-/
structure FPM_Fun where
  f : ℚ → ℚ
  K : ℕ+
  lipschitz_bound : ∀ x y : ℚ, abs (f x - f y) ≤ (K : ℚ) * abs (x - y)

/-- PRIMITIVE 8: THE THERMODYNAMIC SHIFT
  To guarantee an output at `ctx.M`, the engine shifts the input budget.
-/
def shift_context_unary (ctx : Context) (F : FPM_Fun) : Context :=
  { M := ctx.M * F.K, N := ctx.N }


/-!
  # Phase 2: Arithmetic Generators & Binary Precision

  It uses Phase 1 axioms where `FPM_Real` is a structure
  with an explicit stabilization modulus `mod` and convergence proof `stable`.
-/

/-- ENGINE COMPONENT: BINARY BOUNDED FUNCTIONS
    Binary operations consume precision from two independent sources.
    We bound the error expansion using the maximum of the input deviations.
-/
structure FPM_BinFun where
  f : ℚ → ℚ → ℚ
  K : ℕ+
  lipschitz_bound :
    ∀ x₁ y₁ x₂ y₂ : ℚ,
      abs (f x₁ y₁ - f x₂ y₂)
        ≤ (K : ℚ) * (abs (x₁ - x₂) + abs (y₁ - y₂))

/-- BINARY THERMODYNAMIC SHIFT
    To guarantee a binary output at `ctx.M`, both inputs must be evaluated
    at a higher resolution. If K=1 (like in addition), the budget doubles.
-/
def shift_context_bin (ctx : Context) (F : FPM_BinFun) : Context :=
  { M := ctx.M * F.K * (2 : ℕ+)
    N := ctx.N }

/-- Applying a binary rational procedure step-by-step, producing a
    stabilized `FPM_Real` with computed modulus. -/
noncomputable def FPM_BinApply (F : FPM_BinFun) (a b : FPM_Real) : FPM_Real :=
  { seq := fun n => F.f (a.seq n) (b.seq n)
    mod := fun M => max (a.mod (M * F.K * 2)) (b.mod (M * F.K * 2))
    stable := by
      intro M n m hn hm
      have hn_a : n ≥ a.mod (M * F.K * 2) := le_trans (le_max_left _ _) hn
      have hm_a : m ≥ a.mod (M * F.K * 2) := le_trans (le_max_left _ _) hm
      have hn_b : n ≥ b.mod (M * F.K * 2) := le_trans (le_max_right _ _) hn
      have hm_b : m ≥ b.mod (M * F.K * 2) := le_trans (le_max_right _ _) hm
      have ha := a.stable (M * F.K * 2) n m hn_a hm_a
      have hb := b.stable (M * F.K * 2) n m hn_b hm_b
      calc abs (F.f (a.seq n) (b.seq n) - F.f (a.seq m) (b.seq m))
          ≤ (F.K : ℚ) * (abs (a.seq n - a.seq m) + abs (b.seq n - b.seq m)) :=
            F.lipschitz_bound _ _ _ _
        _ ≤ (F.K : ℚ) * ((1 : ℚ) / (↑(M * F.K * 2)) + (1 : ℚ) / (↑(M * F.K * 2))) :=
            by gcongr
        _ = (1 : ℚ) / M := by
            push_cast
            have hK : (0 : ℚ) < (F.K : ℚ) := by positivity
            have hM : (0 : ℚ) < (M : ℚ) := by positivity
            field_simp
            ring }

/-- Applying a unary FPM_Fun to an FPM_Real, producing a stabilized result. -/
noncomputable def FPM_UnaryApply (F : FPM_Fun) (a : FPM_Real) : FPM_Real :=
  { seq := fun n => F.f (a.seq n)
    mod := fun M => a.mod (M * F.K)
    stable := by
      intro M n m hn hm
      have ha := a.stable (M * F.K) n m hn hm
      have hK : (0 : ℚ) < (F.K : ℚ) := by positivity
      have hM : (0 : ℚ) < (M : ℚ) := by positivity
      calc abs (F.f (a.seq n) - F.f (a.seq m))
          ≤ (F.K : ℚ) * abs (a.seq n - a.seq m) :=
            F.lipschitz_bound _ _
        _ ≤ (F.K : ℚ) * ((1 : ℚ) / ↑↑(M * F.K)) := by gcongr
        _ = (1 : ℚ) / ↑↑M := by push_cast; field_simp }

/-
  ========================================================================
  THE ADDITION GENERATOR
  Addition is a linear operation. Its precision cost is strictly constant.
  ========================================================================
-/

/-- The raw rational addition function. -/
def rat_add : ℚ → ℚ → ℚ := fun x y => x + y

/-- Addition has Lipschitz constant K = 1. -/
lemma add_lipschitz :
    ∀ x₁ y₁ x₂ y₂ : ℚ,
      abs (rat_add x₁ y₁ - rat_add x₂ y₂)
        ≤ (1 : ℚ) * (abs (x₁ - x₂) + abs (y₁ - y₂)) := by
  intro x₁ y₁ x₂ y₂
  simp only [rat_add, one_mul]
  have h1 : (x₁ + y₁) - (x₂ + y₂) = (x₁ - x₂) + (y₁ - y₂) := by ring
  rw [h1]
  exact abs_add_le _ _

/-- FPM Addition: a fully thermodynamically bounded binary operation. -/
def FPM_Add : FPM_BinFun :=
  { f := rat_add
    K := 1
    lipschitz_bound := add_lipschitz }

/-- Convenience wrapper for adding two FPM reals. -/
noncomputable def FPM_Real_Add (a b : FPM_Real) : FPM_Real :=
  FPM_BinApply FPM_Add a b

noncomputable instance : Add FPM_Real := ⟨FPM_Real_Add⟩

@[simp] lemma FPM_add_seq (a b : FPM_Real) (n : ℕ+) :
    (a + b).seq n = a.seq n + b.seq n := rfl

/-
========================================================================
  THE MASTER SUBSTITUTION LEMMA (ADDITION)
  ========================================================================

The proof follows the pattern: extract overlap witnesses from hypotheses at the
shifted context, then build a witness for the target context.
Given qa ∈ interval(a₁ n) ∩ interval(a₂ n) and qb ∈ interval(b₁ n) ∩ interval(b₂ n) at
the shifted context, the witness qa + qb lies in both intervals at the target
context because the shifted context
has M_shifted = M * 1 * 2 = 2*M, so the radius is 1/(2*2M) = 1/(4M).
Adding two such radii gives 1/(2M) which is the target radius.
-/
theorem FPM_Add_Substitution (ctx : Context) (a₁ a₂ b₁ b₂ : FPM_Real)
    (hA : FPM_Eq (shift_context_bin ctx FPM_Add) a₁ a₂)
    (hB : FPM_Eq (shift_context_bin ctx FPM_Add) b₁ b₂) :
    FPM_Eq ctx (a₁ + b₁) (a₂ + b₂) := by
  intro n hn;
  -- By definition of $FPM_Eq$, we know that there exist rational numbers $qa$ and $qb$ such that $qa$ and $qb$ lie in both intervals at the shifted context.
  obtain ⟨qa, hqa⟩ := hA n (by
  exact hn)
  obtain ⟨qb, hqb⟩ := hB n (by
  exact hn);
  use qa + qb;
  unfold FPM_Interval at *;
  simp_all +decide [ abs_le, FPM_Add ];
  unfold shift_context_bin at *; norm_num at *; constructor <;> constructor <;> linarith;

/-
  ========================================================================
  THE MULTIPLICATION GENERATOR & MAGNITUDE BOUNDS
  ========================================================================
-/

/-- A strict upper bound on the geometric amplitude of an FPM procedure. -/
def FPM_Bounded (a : FPM_Real) (C : ℕ+) : Prop :=
  ∀ n, abs (a.seq n) ≤ (C : ℚ)

/-- MULTIPLICATIVE THERMODYNAMIC SHIFT -/
def shift_context_mul (ctx : Context) (C : ℕ+) : Context :=
  { M := ctx.M * C * (4 : ℕ+)
    N := ctx.N }

/-- The raw rational multiplication function. -/
def rat_mul : ℚ → ℚ → ℚ := fun x y => x * y

/-- Computable bound: for n ≥ a.mod 1, |a.seq n| ≤ seqBound a -/
noncomputable def FPM_Real.seqBound (a : FPM_Real) : ℕ+ :=
  ⟨Nat.ceil (|a.seq (a.mod 1)| + 2), by positivity⟩

noncomputable def FPM_Real_Mul (a b : FPM_Real) : FPM_Real :=
  { seq := fun n => a.seq n * b.seq n
    mod := fun M =>
      let Ba := a.seqBound
      let Bb := b.seqBound
      max (max (a.mod 1) (b.mod 1)) (max (a.mod (2 * M * Bb)) (b.mod (2 * M * Ba)))
    stable := by
      intro M n m hn hm
      -- By the properties of the sequences and their stability, we can bound the differences.
      have h_diff_a : |a.seq n - a.seq m| ≤ 1 / (2 * M * b.seqBound : ℚ) := by
        convert a.stable ( 2 * M * b.seqBound ) n m _ _ using 1 <;> aesop
      have h_diff_b : |b.seq n - b.seq m| ≤ 1 / (2 * M * a.seqBound : ℚ) := by
        have := b.stable ( 2 * M * a.seqBound ) n m ?_ ?_ <;> aesop
      have h_abs_a : |a.seq n| ≤ a.seqBound := by
        have h_abs_a : |a.seq n - a.seq (a.mod 1)| ≤ 1 := by
          have := a.stable 1 n ( a.mod 1 ) ( by aesop ) ( by aesop ) ; aesop;
        simp_all +decide [ abs_le ];
        constructor <;> linarith [ abs_le.mp ( show |a.seq ( a.mod 1 )| ≤ ( a.seqBound : ℚ ) - 2 by exact le_tsub_of_add_le_right <| mod_cast Nat.le_ceil _ ) ]
      have h_abs_b : |b.seq m| ≤ b.seqBound := by
        have h_diff_b : |b.seq m - b.seq (b.mod 1)| ≤ 1 := by
          exact le_trans ( b.stable 1 m ( b.mod 1 ) ( by aesop ) ( by aesop ) ) ( by norm_num );
        rw [ abs_le ] at *;
        constructor <;> linarith [ abs_le.mp ( show |b.seq ( b.mod 1 )| ≤ ( b.seqBound : ℚ ) - 2 by exact le_tsub_of_add_le_right <| mod_cast Nat.le_ceil _ ), show ( b.seqBound : ℚ ) ≥ 1 by exact Nat.one_le_cast.mpr <| PNat.pos _ ];
      -- Using the triangle inequality and the bounds on the differences, we get:
      have h_triangle : |a.seq n * b.seq n - a.seq m * b.seq m| ≤ |a.seq n| * |b.seq n - b.seq m| + |a.seq n - a.seq m| * |b.seq m| := by
        rw [ ← abs_mul, ← abs_mul ];
        cases abs_cases ( a.seq n * b.seq n - a.seq m * b.seq m ) <;> cases abs_cases ( a.seq n * ( b.seq n - b.seq m ) ) <;> cases abs_cases ( ( a.seq n - a.seq m ) * b.seq m ) <;> linarith;
      refine le_trans h_triangle <| le_trans ( add_le_add ( mul_le_mul h_abs_a h_diff_b ( by positivity ) ( by positivity ) ) ( mul_le_mul h_diff_a h_abs_b ( by positivity ) ( by positivity ) ) ) ?_ ; ring_nf ; norm_num [ mul_assoc, mul_comm, mul_left_comm ] ; ring_nf ; norm_num; }

noncomputable instance : Mul FPM_Real := ⟨FPM_Real_Mul⟩

@[simp] lemma FPM_mul_seq (a b : FPM_Real) (n : ℕ+) :
    (a * b).seq n = a.seq n * b.seq n := rfl

/-
  ========================================================================
  LOCALIZED LIPSCHITZ BOUND FOR MULTIPLICATION
  ========================================================================
-/

lemma mul_lipschitz_bounded (x₁ y₁ x₂ y₂ : ℚ) (C : ℕ+)
    (hx₁ : abs x₁ ≤ (C : ℚ))
    (hy₂ : abs y₂ ≤ (C : ℚ)) :
    abs (rat_mul x₁ y₁ - rat_mul x₂ y₂)
      ≤ (C : ℚ) * (abs (x₁ - x₂) + abs (y₁ - y₂)) := by
  dsimp [rat_mul]
  have h_alg : x₁ * y₁ - x₂ * y₂ = x₁ * (y₁ - y₂) + (x₁ - x₂) * y₂ := by ring
  rw [h_alg]
  calc abs (x₁ * (y₁ - y₂) + (x₁ - x₂) * y₂)
      ≤ abs (x₁ * (y₁ - y₂)) + abs ((x₁ - x₂) * y₂) := abs_add_le _ _
    _ = abs x₁ * abs (y₁ - y₂) + abs (x₁ - x₂) * abs y₂ := by
        rw [abs_mul, abs_mul]
    _ ≤ (C : ℚ) * abs (y₁ - y₂) + abs (x₁ - x₂) * (C : ℚ) := by
        gcongr
    _ = (C : ℚ) * (abs (x₁ - x₂) + abs (y₁ - y₂)) := by ring

/-
========================================================================
  MASTER SUBSTITUTION LEMMA (MULTIPLICATION)
  ========================================================================

Extract overlap witnesses from the shifted context, use the Lipschitz bound for
multiplication (mul_lipschitz_bounded), and chain the budget arithmetic.
The shifted context has M_shifted = M * C * 4, giving radius 1/(2*M*C*4).
The difference |a₁ n - a₂ n| ≤ 2*radius (triangle inequality through overlap witness).
The Lipschitz bound gives |a₁*b₁ - a₂*b₂| ≤ C*(|a₁-a₂| + |b₁-b₂|) ≤ C*4*radius = C*4/(2*M*C*4) = 1/(2M). Use a₁ n * b₁ n as witness.
-/
theorem FPM_Mul_Substitution (ctx : Context) (C : ℕ+) (a₁ a₂ b₁ b₂ : FPM_Real)
    (ha₁ : FPM_Bounded a₁ C)
    (hb₂ : FPM_Bounded b₂ C)
    (hA : FPM_Eq (shift_context_mul ctx C) a₁ a₂)
    (hB : FPM_Eq (shift_context_mul ctx C) b₁ b₂) :
    FPM_Eq ctx (a₁ * b₁) (a₂ * b₂) := by
  intro n hn
  obtain ⟨qa, hqa⟩ := hA n (by
  exact hn)
  obtain ⟨qb, hqb⟩ := hB n (by
  exact hn);
  refine' ⟨ a₁.seq n * b₁.seq n, _, _ ⟩ <;> simp_all +decide [ FPM_Interval ];
  -- Apply the Lipschitz bound for multiplication.
  have h_lip : abs (a₁.seq n * b₁.seq n - a₂.seq n * b₂.seq n) ≤ (C : ℚ) * (abs (a₁.seq n - a₂.seq n) + abs (b₁.seq n - b₂.seq n)) := by
    have := mul_lipschitz_bounded ( a₁.seq n ) ( b₁.seq n ) ( a₂.seq n ) ( b₂.seq n ) C ( ha₁ n ) ( hb₂ n ) ; aesop;
  -- Apply the triangle inequality to the differences.
  have h_triangle : abs (a₁.seq n - a₂.seq n) ≤ 2 * (1 / (2 * (ctx.M * C * 4 : ℚ))) ∧ abs (b₁.seq n - b₂.seq n) ≤ 2 * (1 / (2 * (ctx.M * C * 4 : ℚ))) := by
    simp_all +decide [ abs_le, shift_context_mul ];
    exact ⟨ ⟨ by linarith, by linarith ⟩, ⟨ by linarith, by linarith ⟩ ⟩;
  refine' le_trans h_lip _;
  refine' le_trans ( mul_le_mul_of_nonneg_left ( add_le_add h_triangle.1 h_triangle.2 ) ( Nat.cast_nonneg _ ) ) _ ; ring_nf ; norm_num

theorem FPM_Mul_Substitution_full
    (ctx : Context) (C : ℕ+) (a₁ a₂ b₁ b₂ : FPM_Real)
    (ha₁ : FPM_Bounded a₁ C)
    (ha₂ : FPM_Bounded a₂ C)
    (hb₁ : FPM_Bounded b₁ C)
    (hb₂ : FPM_Bounded b₂ C)
    (hA : FPM_Eq (shift_context_mul ctx C) a₁ a₂)
    (hB : FPM_Eq (shift_context_mul ctx C) b₁ b₂) :
    FPM_Eq ctx (a₁ * b₁) (a₂ * b₂) :=
  FPM_Mul_Substitution ctx C a₁ a₂ b₁ b₂ ha₁ hb₂ hA hB

/-- Square transport, specialized from multiplication transport. -/
theorem FPM_Sq_Substitution
    (ctx : Context) (C : ℕ+)
    (a₁ a₂ : FPM_Real)
    (ha₁ : FPM_Bounded a₁ C)
    (ha₂ : FPM_Bounded a₂ C)
    (hA : FPM_Eq (shift_context_mul ctx C) a₁ a₂) :
    FPM_Eq ctx (a₁ * a₁) (a₂ * a₂) :=
  FPM_Mul_Substitution ctx C a₁ a₂ a₁ a₂ ha₁ ha₂ hA hA

/-
  ========================================================================
  NEGATION
  Negation flips the interval but preserves its radius.
  ========================================================================
-/

/-- The raw rational negation function. -/
def rat_neg : ℚ → ℚ := fun x => -x

lemma neg_lipschitz :
    ∀ x y : ℚ, abs (rat_neg x - rat_neg y) ≤ (1 : ℚ) * abs (x - y) := by
  intro x y
  simp only [rat_neg, one_mul]
  rw [show -x - -y = -(x - y) from by ring, abs_neg]

def FPM_Neg : FPM_Fun :=
  { f := rat_neg
    K := 1
    lipschitz_bound := neg_lipschitz }

noncomputable def FPM_Real_Neg (a : FPM_Real) : FPM_Real :=
  FPM_UnaryApply FPM_Neg a

noncomputable instance : Neg FPM_Real := ⟨FPM_Real_Neg⟩

@[simp] lemma FPM_neg_seq (a : FPM_Real) (n : ℕ+) :
    (-a).seq n = -(a.seq n) := rfl

/-
========================================================================
  MASTER SUBSTITUTION LEMMA (NEGATION)
  ========================================================================


Extract the overlap witness from the shifted context. Since FPM_Neg has K=1, the
shifted context is the same as the target. Use -qa as witness;
the distance |(-qa) - (-a_i n)| = |qa - a_i n| which is bounded by the same radius.
-/
theorem FPM_Neg_Substitution (ctx : Context) (a₁ a₂ : FPM_Real)
    (hA : FPM_Eq (shift_context_unary ctx FPM_Neg) a₁ a₂) :
    FPM_Eq ctx (-a₁) (-a₂) := by
  intro n hn;
  obtain ⟨ q, hq₁, hq₂ ⟩ := hA n hn;
  refine' ⟨ -q, _, _ ⟩ <;> simp_all +decide [ FPM_Interval ];
  · convert hq₁ using 1 <;> ring_nf!;
    · rw [ neg_add_eq_sub, abs_sub_comm ];
    · unfold shift_context_unary; aesop;
  · convert hq₂ using 1 <;> ring_nf;
    · rw [ neg_add_eq_sub, abs_sub_comm ];
    · unfold shift_context_unary; aesop;

/-
  ========================================================================
  THE RECIPROCAL GENERATOR (EVENTUAL APARTNESS)
  Inversion is non-linear. Cost scales with proximity to zero.
  ========================================================================
-/

/-- A procedure is eventually apart from zero if |a.seq n| ≥ 1/L for all n ≥ N_safe. -/
def FPM_EventuallyApart (a : FPM_Real) (L : ℕ+) (N_safe : ℕ+) : Prop :=
  ∀ n ≥ N_safe, (1 : ℚ) / (L : ℚ) ≤ abs (a.seq n)

/-- Conceptual inversion shift (spatial only). -/
def shift_context_inv (ctx : Context) (L : ℕ+) (N_safe : ℕ+) : Context :=
  { M := ctx.M * L * L
    N := max ctx.N N_safe }

/-- Substitution-ready inversion shift: extra factor 2 for the triangle step. -/
def shift_context_inv_subst (ctx : Context) (L : ℕ+) (N_safe : ℕ+) : Context :=
  { M := ctx.M * L * L * (2 : ℕ+)
    N := max ctx.N N_safe }

/-- The raw rational inversion function. -/
def rat_inv : ℚ → ℚ := fun x => x⁻¹

/-
  ========================================================================
  RECIPROCAL HELPER LEMMAS
  ========================================================================
-/

lemma FPM_EventuallyApart_at
    (a : FPM_Real) (L N_safe n : ℕ+)
    (ha : FPM_EventuallyApart a L N_safe)
    (hn : n ≥ N_safe) :
    (1 : ℚ) / (L : ℚ) ≤ abs (a.seq n) :=
  ha n hn

lemma FPM_EventuallyApart_nonzero
    (a : FPM_Real) (L N_safe n : ℕ+)
    (ha : FPM_EventuallyApart a L N_safe)
    (hn : n ≥ N_safe) :
    a.seq n ≠ 0 := by
  have hfloor := ha n hn
  have : (0 : ℚ) < abs (a.seq n) := lt_of_lt_of_le (by positivity) hfloor
  exact abs_pos.1 this

lemma FPM_Inv_SafeTail
    (ctx : Context) (L N_safe n : ℕ+)
    (hn : n ≥ (shift_context_inv_subst ctx L N_safe).N) :
    n ≥ N_safe := by
  have hmax : n ≥ max ctx.N N_safe := by
    simpa [shift_context_inv_subst] using hn
  exact le_trans (le_max_right ctx.N N_safe) hmax

/-
  ========================================================================
  LOCALIZED LIPSCHITZ BOUND FOR INVERSION
  Goal: |x⁻¹ - y⁻¹| ≤ L² * |x - y|,  assuming |x|, |y| ≥ 1/L
  ========================================================================
-/

lemma inv_lipschitz_bounded (x y : ℚ) (L : ℕ+)
    (hx : (1 : ℚ) / (L : ℚ) ≤ abs x)
    (hy : (1 : ℚ) / (L : ℚ) ≤ abs y) :
    abs (x⁻¹ - y⁻¹) ≤ ((L : ℚ) ^ 2) * abs (x - y) := by
  set Lq : ℚ := (L : ℚ) with hLq
  have hLqpos : (0 : ℚ) < Lq := by positivity
  have hLqne  : Lq ≠ 0 := ne_of_gt hLqpos
  have h1Lq : (0 : ℚ) < 1 / Lq := by positivity
  have hx0 : x ≠ 0 := by
    apply abs_pos.1; linarith
  have hy0 : y ≠ 0 := by
    apply abs_pos.1; linarith
  have h_alg : x⁻¹ - y⁻¹ = (y - x) / (x * y) := by field_simp
  have hprod_floor : (1 / Lq) * (1 / Lq) ≤ abs x * abs y :=
    mul_le_mul hx hy (le_of_lt h1Lq) (abs_nonneg x)
  have hprod_pos : (0 : ℚ) < abs x * abs y :=
    lt_of_lt_of_le (mul_pos h1Lq h1Lq) hprod_floor
  have hinv_prod : (abs x * abs y)⁻¹ ≤ Lq ^ 2 := by
    have h := one_div_le_one_div_of_le (mul_pos h1Lq h1Lq) hprod_floor
    have hsimp : ((1 / Lq) * (1 / Lq))⁻¹ = Lq ^ 2 := by field_simp
    simpa [one_div, hsimp, sq] using h
  calc abs (x⁻¹ - y⁻¹)
      = abs ((y - x) / (x * y))              := by rw [h_alg]
    _ = abs (y - x) * (abs x * abs y)⁻¹     := by
          rw [div_eq_mul_inv, abs_mul, abs_inv, abs_mul]
    _ = abs (x - y) * (abs x * abs y)⁻¹     := by
          rw [show y - x = -(x - y) from by ring, abs_neg]
    _ ≤ abs (x - y) * (Lq ^ 2)              :=
          mul_le_mul_of_nonneg_left hinv_prod (abs_nonneg _)
    _ = (Lq ^ 2) * abs (x - y)              := by ring

/-
  ========================================================================
  APART-CERTIFIED INVERSE
  ========================================================================
-/

/-- Reciprocal of an FPM_Real that is known to be eventually apart from zero.
    The stability of the inverse sequence requires a lower bound `1/L` on the
    absolute values.
    The modulus is `max N_safe (a.mod (M * L * L))`, ensuring both
    apartness and sufficient input precision for the Lipschitz bound `L²`. -/
/- Reciprocal of an `FPM_Real` that is known to be eventually apart from zero. -/
noncomputable def FPM_Real_Inv_Apart
    (a : FPM_Real) (L N_safe : ℕ+)
    (ha : FPM_EventuallyApart a L N_safe) : FPM_Real :=
  { seq := fun n => (a.seq n)⁻¹
    mod := fun M => max N_safe (a.mod (M * L * L))
    stable := by
      intro M n m hn hm
      have hn_safe : n ≥ N_safe := le_trans (le_max_left _ _) hn
      have hm_safe : m ≥ N_safe := le_trans (le_max_left _ _) hm
      have hn_mod : n ≥ a.mod (M * L * L) := le_trans (le_max_right _ _) hn
      have hm_mod : m ≥ a.mod (M * L * L) := le_trans (le_max_right _ _) hm
      have hx : (1 : ℚ) / (L : ℚ) ≤ abs (a.seq n) :=
        FPM_EventuallyApart_at a L N_safe n ha hn_safe
      have hy : (1 : ℚ) / (L : ℚ) ≤ abs (a.seq m) :=
        FPM_EventuallyApart_at a L N_safe m ha hm_safe
      have hdiff := a.stable (M * L * L) n m hn_mod hm_mod
      calc
        abs ((a.seq n)⁻¹ - (a.seq m)⁻¹)
            ≤ ((L : ℚ) ^ 2) * abs (a.seq n - a.seq m) := by
              exact inv_lipschitz_bounded _ _ L hx hy
        _ ≤ ((L : ℚ) ^ 2) * ((1 : ℚ) / ↑↑(M * L * L)) := by
              gcongr
        _ = (1 : ℚ) / ↑↑M := by
              push_cast
              have hL : (0 : ℚ) < (L : ℚ) := by positivity
              have hM : (0 : ℚ) < (M : ℚ) := by positivity
              field_simp }

/- The apart-certified inverse has the expected reciprocal sequence. -/
lemma FPM_Real_Inv_Apart_seq
    (a : FPM_Real) (L N_safe : ℕ+) (ha : FPM_EventuallyApart a L N_safe) (n : ℕ+) :
    (FPM_Real_Inv_Apart a L N_safe ha).seq n = (a.seq n)⁻¹ := rfl

/- Public inverse constructor kept for notation (`a⁻¹`) and minimal API churn.

   Historical note:
   an earlier version treated inverse as a total `FPM_Real → FPM_Real` operation
   and left its stability proof as `sorry`. That was not mathematically valid in
   general, since the inverse of a stabilized sequence need not be stabilized if
   the sequence can approach `0`.

   Current design:
   the canonical certified inverse is `FPM_Real_Inv_Apart`, which requires an
   eventual-apartness witness. The public notation-level inverse is retained as a
   compatibility wrapper so existing code continues to read naturally, while all
   correctness theorems about inversion are proved under explicit apartness
   hypotheses and routed through the certified construction. -/

noncomputable def FPM_Real_Inv (a : FPM_Real) : FPM_Real := by
  classical
  by_cases h : ∃ L N_safe, FPM_EventuallyApart a L N_safe
  · let L : ℕ+ := Classical.choose h
    let hL : ∃ N_safe, FPM_EventuallyApart a L N_safe := Classical.choose_spec h
    let N_safe : ℕ+ := Classical.choose hL
    let ha : FPM_EventuallyApart a L N_safe := Classical.choose_spec hL
    exact FPM_Real_Inv_Apart a L N_safe ha
  · exact FPM_Zero

noncomputable instance : Inv FPM_Real := ⟨FPM_Real_Inv⟩

/- Sequence-level bridge from the public inverse wrapper to the certified inverse.

   Under `FPM_EventuallyApart`, the wrapper inverse has the expected reciprocal
   sequence:
     `(a⁻¹).seq n = (a.seq n)⁻¹`.

   This is the key lemma used by downstream inverse theorems. It lets proofs work
   with the convenient public notation `a⁻¹` while discharging all real
   mathematical content through the guarded apartness hypothesis. -/

lemma FPM_Inv_seq_of_apart
    (a : FPM_Real) (L N_safe : ℕ+)
    (ha : FPM_EventuallyApart a L N_safe) (n : ℕ+) :
    (a⁻¹).seq n = (a.seq n)⁻¹ := by
  classical
  change (FPM_Real_Inv a).seq n = (a.seq n)⁻¹
  unfold FPM_Real_Inv
  split_ifs with h
  ·
    let L' : ℕ+ := Classical.choose h
    let hL' : ∃ N_safe, FPM_EventuallyApart a L' N_safe := Classical.choose_spec h
    let N' : ℕ+ := Classical.choose hL'
    let ha' : FPM_EventuallyApart a L' N' := Classical.choose_spec hL'
    simp [FPM_Real_Inv_Apart_seq]
  · exact False.elim (h ⟨L, N_safe, ha⟩)

/- Certified-sequence compatibility for the public inverse wrapper.

   When `a` is eventually apart from zero, the wrapper inverse and the canonical
   certified inverse `FPM_Real_Inv_Apart a L N_safe ha` agree at every sequence
   index. This records that the public inverse API is only a convenience layer:
   under the hypotheses that make inversion valid, it coincides pointwise with
   the certified construction. -/

lemma FPM_Inv_seq_eq_certified_of_apart
    (a : FPM_Real) (L N_safe : ℕ+)
    (ha : FPM_EventuallyApart a L N_safe) :
    ∀ n : ℕ+, (a⁻¹).seq n = (FPM_Real_Inv_Apart a L N_safe ha).seq n := by
  intro n
  rw [FPM_Inv_seq_of_apart a L N_safe ha n,
      FPM_Real_Inv_Apart_seq a L N_safe ha n]

/-
========================================================================
  THE GENERIC UNARY SUBSTITUTION THEOREM
  ========================================================================

Extract overlap witness q, then use F.f q as the output witness. The Lipschitz
bound gives |F.f q - F.f (a_i.seq n)| ≤ K * |q - a_i.seq n| ≤ K * radius_shifted = K * 1/(2*M*K) = 1/(2*M) = target radius.
-/
theorem FPM_Unary_Substitution
    (ctx : Context) (F : FPM_Fun) (a₁ a₂ : FPM_Real)
    (hA : FPM_Eq (shift_context_unary ctx F) a₁ a₂) :
    FPM_Eq ctx (FPM_UnaryApply F a₁) (FPM_UnaryApply F a₂) := by
  -- Extract the overlap witness from the shifted context.
  intro n hn
  obtain ⟨q, hq⟩ := hA n hn;
  refine' ⟨ F.f q, _, _ ⟩ <;> simp_all +decide [ FPM_Interval ];
  · refine' le_trans ( F.lipschitz_bound _ _ ) _;
    refine' le_trans ( mul_le_mul_of_nonneg_left hq.1 <| Nat.cast_nonneg _ ) _ ; norm_num [ shift_context_unary ] ; ring_nf ; norm_num;
  · have := F.lipschitz_bound q ( a₂.seq n ) ; simp_all +decide [ FPM_UnaryApply ] ;
    refine' le_trans this ( le_trans ( mul_le_mul_of_nonneg_left hq.2 <| Nat.cast_nonneg _ ) _ ) ; norm_num [ shift_context_unary ] ; ring_nf ; norm_num

/-
  ========================================================================
  NEGATION AS SPECIAL CASE OF GENERIC UNARY THEOREM
  ========================================================================
-/
theorem FPM_Neg_Substitution'
    (ctx : Context) (a₁ a₂ : FPM_Real)
    (hA : FPM_Eq (shift_context_unary ctx FPM_Neg) a₁ a₂) :
    FPM_Eq ctx (-a₁) (-a₂) := by
  have h := FPM_Unary_Substitution ctx FPM_Neg a₁ a₂ hA
  convert h using 2



/-
ctxS.M = ctx.M * L * L * 2, so rS = 1/(2 * ctx.M * L^2 * 2).
Then L^2 * (rS + rS) = L^2 * 2 * rS = L^2 * 2 / (2 * ctx.M * L^2 * 2) = 1 / (2 * ctx.M).
Use field_simp and ring after establishing positivity.
-/
lemma FPM_Inv_Budget
    (ctx : Context) (L N_safe : ℕ+) :
    let ctxS : Context := shift_context_inv_subst ctx L N_safe
    let rS : ℚ := (1 : ℚ) / (2 * (ctxS.M : ℚ))
    ((L : ℚ) ^ 2) * (rS + rS) = (1 : ℚ) / (2 * (ctx.M : ℚ)) := by
  -- Simplify the expression for the radius in the shifted context.
  field_simp [shift_context_inv_subst]
  ring_nf;
  unfold shift_context_inv_subst; norm_num; ring;

lemma FPM_Inv_Budget_le
    (ctx : Context) (L N_safe : ℕ+) :
    let ctxS : Context := shift_context_inv_subst ctx L N_safe
    let rS : ℚ := (1 : ℚ) / (2 * (ctxS.M : ℚ))
    ((L : ℚ) ^ 2) * (rS + rS) ≤ (1 : ℚ) / (2 * (ctx.M : ℚ)) :=
  le_of_eq (FPM_Inv_Budget ctx L N_safe)

theorem FPM_Bounded_neg {a : FPM_Real} {C : ℕ+} :
    FPM_Bounded a C → FPM_Bounded (-a) C := by
  intro ha n
  simp only [FPM_neg_seq, abs_neg]
  exact ha n

lemma FPM_EventuallyApart_neg
    (a : FPM_Real) (L N_safe : ℕ+)
    (ha : FPM_EventuallyApart a L N_safe) :
    FPM_EventuallyApart (-a) L N_safe := by
  intro n hn
  simp only [FPM_neg_seq, abs_neg]
  exact ha n hn

noncomputable def FPM_Real_Sub (a b : FPM_Real) : FPM_Real := a + (-b)

noncomputable instance : Sub FPM_Real := ⟨FPM_Real_Sub⟩

@[simp] theorem FPM_sub_seq
    (a b : FPM_Real) (n : ℕ+) :
    (a - b).seq n = a.seq n + (-(b.seq n)) := rfl

/-!
  ========================================================================
  N-ARY GENERATOR & THERMODYNAMICS
  flat n-ary operations with linear budget cost M·K·n,
  replacing the exponential M·2^n cost of recursive binary composition.
  ========================================================================
-/

/-- N-ARY BOUNDED FUNCTIONS
    Operations that consume an entire finite vector of inputs at once.
    The Lipschitz bound evaluates against the SUM of individual deviations,
    not the max, so the cost grows linearly in `n`.
-/
structure FPM_NaryFun (n : ℕ) where
  f : (Fin n → ℚ) → ℚ
  K : ℕ+
  lipschitz_bound :
    ∀ x y : (Fin n → ℚ),
      abs (f x - f y) ≤ (K : ℚ) * ∑ i, abs (x i - y i)

/-- N-ARY THERMODYNAMIC SHIFT
    Budget cost is M · K · n  (linear in both K and n).
    Compare: `shift_context_bin` costs M·K·2, `FPM_sum1` costs M·2^n.
-/
def shift_context_nary (ctx : Context) (n : ℕ+) (F : FPM_NaryFun n.val) : Context :=
  { M := ctx.M * F.K * n
    N := ctx.N }

/-- Applying an n-ary rational procedure to a vector of FPM_Reals.
    The modulus picks the MAXIMUM stabilization time across all n components,
    each evaluated at the shifted budget M·K·n. -/
noncomputable def FPM_NaryApply {n : ℕ+} (F : FPM_NaryFun n.val) (v : Fin n.val → FPM_Real) : FPM_Real :=
  { seq   := fun k => F.f (fun i => (v i).seq k)
    mod   := fun M =>
                let M_shifted : ℕ+ := M * F.K * n
                Finset.univ.sup' ⟨⟨0, n.pos⟩, Finset.mem_univ _⟩
                  (fun i : Fin n.val => (v i).mod M_shifted)
    stable := by
      intro M k l hk hl
      -- Step 1: each component's temporal index is above its modulus threshold
      -- Finset.le_sup' gives: (v i).mod ... ≤ sup', and hk/hl give sup' ≤ k/l
      -- Proof irrelevance makes the two Nonempty witnesses definitionally equal
      have hk_i : ∀ i : Fin n.val, k ≥ (v i).mod (M * F.K * n) := fun i =>
        le_trans
          (Finset.le_sup' (fun j => (v j).mod (M * F.K * n)) (Finset.mem_univ i))
          hk
      have hl_i : ∀ i : Fin n.val, l ≥ (v i).mod (M * F.K * n) := fun i =>
        le_trans
          (Finset.le_sup' (fun j => (v j).mod (M * F.K * n)) (Finset.mem_univ i))
          hl
      -- Step 2: each component's sequence difference is bounded by 1 / M_shifted
      have h_comp : ∀ i : Fin n.val,
          |(v i).seq k - (v i).seq l| ≤ (1 : ℚ) / ↑↑(M * F.K * n) :=
        fun i => (v i).stable (M * F.K * n) k l (hk_i i) (hl_i i)
      -- Step 3: chain F.lipschitz_bound, Finset.sum_le_sum, then arithmetic
      calc |F.f (fun i => (v i).seq k) - F.f (fun i => (v i).seq l)|
          ≤ (F.K : ℚ) * ∑ i : Fin n.val, |(v i).seq k - (v i).seq l| :=
              F.lipschitz_bound _ _
        _ ≤ (F.K : ℚ) * ∑ _i : Fin n.val, (1 : ℚ) / ↑↑(M * F.K * n) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              exact Finset.sum_le_sum (fun i _ => h_comp i)
        _ = (1 : ℚ) / ↑↑M := by
              -- ∑ over Fin n.val of a constant = n.val • constant
              rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
              -- resolve all ℕ+ and ℕ casts to ℚ
              push_cast
              have hK : (0 : ℚ) < (F.K : ℚ)   := by positivity
              have hM : (0 : ℚ) < (M : ℚ)       := by positivity
              have hn : (0 : ℚ) < (n.val : ℚ)   := by exact_mod_cast n.pos
              field_simp }

/-- N-ARY ADDITION GENERATOR — the specific n-ary sum. K = 1.
    Budget cost: M · 1 · n = M · n  (purely linear).
-/
def FPM_AddNary (n : ℕ) : FPM_NaryFun n :=
  { f := fun v => ∑ i, v i
    K := 1
    lipschitz_bound := by
      intro x y
      -- Step 1: resolve the ↑↑(1 : ℕ+) cast to (1 : ℚ) cheaply
      have hK : ((1 : ℕ+) : ℚ) = 1 := by norm_num
      rw [hK, one_mul]
      -- Step 2: prove ∑(x i - y i) = ∑ x i - ∑ y i using only sum_add_distrib
      have h : ∑ i : Fin n, (x i - y i) = ∑ i : Fin n, x i - ∑ i : Fin n, y i := by
        have key : ∑ i : Fin n, ((x i - y i) + y i) =
                   ∑ i : Fin n, (x i - y i) + ∑ i : Fin n, y i :=
          Finset.sum_add_distrib
        simp only [sub_add_cancel] at key
        linarith
      rw [← h]
      exact Finset.abs_sum_le_sum_abs _ _ }

/-- Public API: native n-ary FPM sum with linear budget cost. -/
noncomputable def FPM_sum_nary {n : ℕ+} (v : Fin n.val → FPM_Real) : FPM_Real :=
  FPM_NaryApply (FPM_AddNary n.val) v

@[simp] lemma FPM_sum_nary_seq {n : ℕ+} (v : Fin n.val → FPM_Real) (k : ℕ+) :
    (FPM_sum_nary v).seq k = ∑ i : Fin n.val, (v i).seq k := rfl

/-- Boundedness of binary addition with explicit component bounds. -/
theorem FPM_Bounded_add {a b : FPM_Real} {Ca Cb : ℕ+}
    (ha : FPM_Bounded a Ca) (hb : FPM_Bounded b Cb) :
    FPM_Bounded (a + b) (Ca + Cb) := by
  intro k
  calc
    abs ((a + b).seq k)
        = abs (a.seq k + b.seq k) := by
          simp [FPM_add_seq]
    _ ≤ abs (a.seq k) + abs (b.seq k) := by
          exact abs_add_le _ _
    _ ≤ (Ca : ℚ) + (Cb : ℚ) := by
          exact add_le_add (ha k) (hb k)
    _ = ((Ca + Cb : ℕ+) : ℚ) := by
          simp


/-- Uniform boundedness for an n-ary sum:
    if every summand is bounded by `C`, then the total sum is bounded by `n*C`. -/
theorem FPM_Bounded_sum_nary {n : ℕ+}
    (v : Fin n.val → FPM_Real) (C : ℕ+)
    (h : ∀ i : Fin n.val, FPM_Bounded (v i) C) :
    FPM_Bounded (FPM_sum_nary v) (n * C) := by
  intro k
  rw [FPM_sum_nary_seq]
  calc
    abs (∑ i : Fin n.val, (v i).seq k)
        ≤ ∑ i : Fin n.val, abs ((v i).seq k) := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n.val, (C : ℚ) := by
          exact Finset.sum_le_sum (fun i _ => h i k)
    _ = (n : ℚ) * (C : ℚ) := by
          rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    _ = ((n * C : ℕ+) : ℚ) := by
          simp


/-- sigma-style boundedness theorem:
    each summand may have its own bound `C i`, and the total sum is bounded
    by the sum of those bounds. -/
theorem FPM_Bounded_sum_nary_sigma {n : ℕ+}
    (v : Fin n.val → FPM_Real) (C : Fin n.val → ℕ+)
    (h : ∀ i : Fin n.val, FPM_Bounded (v i) (C i)) :
    FPM_Bounded (FPM_sum_nary v)
      ⟨∑ i : Fin n.val, ((C i : ℕ+) : ℕ), by
        classical
        let i0 : Fin n.val := ⟨0, n.pos⟩
        have hi0 : i0 ∈ (Finset.univ : Finset (Fin n.val)) := by
          simp
        have hterm : 0 < ((C i0 : ℕ+) : ℕ) := PNat.pos (C i0)
        have hle : ((C i0 : ℕ+) : ℕ) ≤ ∑ i : Fin n.val, ((C i : ℕ+) : ℕ) := by
          exact Finset.single_le_sum
            (fun i _ => Nat.zero_le (((C i : ℕ+) : ℕ))) hi0
        exact lt_of_lt_of_le hterm hle
      ⟩ := by
  classical
  intro k
  rw [FPM_sum_nary_seq]
  calc
    abs (∑ i : Fin n.val, (v i).seq k)
        ≤ ∑ i : Fin n.val, abs ((v i).seq k) := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin n.val, ((C i : ℕ+) : ℚ) := by
          exact Finset.sum_le_sum (fun i _ => h i k)
    _ = (⟨∑ i : Fin n.val, ((C i : ℕ+) : ℕ), by
            let i0 : Fin n.val := ⟨0, n.pos⟩
            have hi0 : i0 ∈ (Finset.univ : Finset (Fin n.val)) := by
              simp
            have hterm : 0 < ((C i0 : ℕ+) : ℕ) := PNat.pos (C i0)
            have hle : ((C i0 : ℕ+) : ℕ) ≤ ∑ i : Fin n.val, ((C i : ℕ+) : ℕ) := by
              exact Finset.single_le_sum
                (fun i _ => Nat.zero_le (((C i : ℕ+) : ℕ))) hi0
            exact lt_of_lt_of_le hterm hle
          ⟩ : ℕ+) := by
          simp

/-- Master substitution lemma for the native n-ary sum.
    This is the flat replacement for recursive `sum1` transport. -/
theorem FPM_NaryAdd_Substitution {n : ℕ+} (ctx : Context)
    (v₁ v₂ : Fin n.val → FPM_Real)
    (h :
      ∀ i : Fin n.val,
        FPM_Eq (shift_context_nary ctx n (FPM_AddNary n.val)) (v₁ i) (v₂ i)) :
    FPM_Eq ctx (FPM_sum_nary v₁) (FPM_sum_nary v₂) := by
  classical
  intro k hk
  have hk' : k ≥ (shift_context_nary ctx n (FPM_AddNary n.val)).N := by
    simpa [shift_context_nary] using hk
  choose q hq using (fun i : Fin n.val => h i k hk')
  have hbudget :
      ∑ _i : Fin n.val,
          (1 : ℚ) / (2 * ((shift_context_nary ctx n (FPM_AddNary n.val)).M : ℚ))
        = (1 : ℚ) / (2 * (ctx.M : ℚ)) := by
    rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    simp [shift_context_nary, FPM_AddNary]
    have hM : (0 : ℚ) < (ctx.M : ℚ) := by positivity
    have hn : (0 : ℚ) < (n.val : ℚ) := by
      exact_mod_cast n.pos
    field_simp
  have hsum₁ :
      (∑ i : Fin n.val, (q i - (v₁ i).seq k))
        = (∑ i : Fin n.val, q i) - ∑ i : Fin n.val, (v₁ i).seq k := by
    simp [Finset.sum_sub_distrib]
  have hsum₂ :
      (∑ i : Fin n.val, (q i - (v₂ i).seq k))
        = (∑ i : Fin n.val, q i) - ∑ i : Fin n.val, (v₂ i).seq k := by
    simp [Finset.sum_sub_distrib]
  refine ⟨∑ i : Fin n.val, q i, ?_⟩
  constructor
  · rw [FPM_Interval, FPM_sum_nary_seq]
    calc
      abs ((∑ i : Fin n.val, q i) - ∑ i : Fin n.val, (v₁ i).seq k)
          = abs (∑ i : Fin n.val, (q i - (v₁ i).seq k)) := by
              rw [← hsum₁]
      _ ≤ ∑ i : Fin n.val, abs (q i - (v₁ i).seq k) := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin n.val,
            (1 : ℚ) / (2 * ((shift_context_nary ctx n (FPM_AddNary n.val)).M : ℚ)) := by
              exact Finset.sum_le_sum (fun i _ => by
                simpa [FPM_Interval] using (hq i).1)
      _ = (1 : ℚ) / (2 * (ctx.M : ℚ)) := hbudget
  · rw [FPM_Interval, FPM_sum_nary_seq]
    calc
      abs ((∑ i : Fin n.val, q i) - ∑ i : Fin n.val, (v₂ i).seq k)
          = abs (∑ i : Fin n.val, (q i - (v₂ i).seq k)) := by
              rw [← hsum₂]
      _ ≤ ∑ i : Fin n.val, abs (q i - (v₂ i).seq k) := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin n.val,
            (1 : ℚ) / (2 * ((shift_context_nary ctx n (FPM_AddNary n.val)).M : ℚ)) := by
              exact Finset.sum_le_sum (fun i _ => by
                simpa [FPM_Interval] using (hq i).2)
      _ = (1 : ℚ) / (2 * (ctx.M : ℚ)) := hbudget


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

/-!
  # Phase 4 Core: Rewrite Registry

  written to use the new Phase 1 axioms.
  Uses `FPM_Fun` from Phase 1.
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

noncomputable section
/-!
  # Phase 6: Finite Vectors, Matrices, and Tensors

  This file extends the FPM real engine to finite-dimensional algebraic data:
  - finite vectors,
  - finite matrices,
  - finite tensors.

  Design choice:
  - stay structural first,
  - use componentwise contextual equality,
  - delay finite sums / contractions until later sections,
  - keep the interface fully faithful to the visible real-layer engine.
-/

/- ========================================================================
   SECTION 1: BASIC OBJECTS
   ======================================================================== -/

/-- A finite vector of length `n` over `FPM_Real`. -/
abbrev FPM_Vector (n : ℕ) := Fin n → FPM_Real

/-- A finite `m × n` matrix over `FPM_Real`. -/
abbrev FPM_Matrix (m n : ℕ) := Fin m → Fin n → FPM_Real

/-- A finite 3-tensor of shape `i × j × k` over `FPM_Real`. -/
abbrev FPM_Tensor3 (i j k : ℕ) := Fin i → Fin j → Fin k → FPM_Real

/-- A finite 4-tensor of shape `i × j × k × l` over `FPM_Real`. -/
abbrev FPM_Tensor4 (i j k l : ℕ) := Fin i → Fin j → Fin k → Fin l → FPM_Real


/-
  We keep the first tensor layer explicit rather than introducing a fully
  generic dependent-family tensor object immediately. This keeps the early
  API concrete and easy to use in later transport theorems.
-/

/- ========================================================================
   SECTION 2: COMPONENTWISE EQUALITY AND BOUNDEDNESS
   ======================================================================== -/

/-- Componentwise contextual equality for finite vectors. -/
def FPM_Vector_Eq (ctx : _root_.Context) {n : ℕ}
    (v w : FPM_Vector n) : Prop :=
  ∀ i : Fin n, FPM_Eq ctx (v i) (w i)

/-- Componentwise boundedness for finite vectors. -/
def FPM_Vector_Bounded {n : ℕ}
    (v : FPM_Vector n) (C : ℕ+) : Prop :=
  ∀ i : Fin n, FPM_Bounded (v i) C

/-- Componentwise contextual equality for finite matrices. -/
def FPM_Matrix_Eq (ctx : _root_.Context) {m n : ℕ}
    (A B : FPM_Matrix m n) : Prop :=
  ∀ i : Fin m, ∀ j : Fin n, FPM_Eq ctx (A i j) (B i j)

/-- Componentwise boundedness for finite matrices. -/
def FPM_Matrix_Bounded {m n : ℕ}
    (A : FPM_Matrix m n) (C : ℕ+) : Prop :=
  ∀ i : Fin m, ∀ j : Fin n, FPM_Bounded (A i j) C

/-- Componentwise contextual equality for finite 3-tensors. -/
def FPM_Tensor3_Eq (ctx : _root_.Context) {i j k : ℕ}
    (T S : FPM_Tensor3 i j k) : Prop :=
  ∀ a : Fin i, ∀ b : Fin j, ∀ c : Fin k,
    FPM_Eq ctx (T a b c) (S a b c)

/-- Componentwise boundedness for finite 3-tensors. -/
def FPM_Tensor3_Bounded {i j k : ℕ}
    (T : FPM_Tensor3 i j k) (C : ℕ+) : Prop :=
  ∀ a : Fin i, ∀ b : Fin j, ∀ c : Fin k,
    FPM_Bounded (T a b c) C

/-- Componentwise contextual equality for finite 4-tensors. -/
def FPM_Tensor4_Eq (ctx : _root_.Context) {i j k l : ℕ}
    (T S : FPM_Tensor4 i j k l) : Prop :=
  ∀ a : Fin i, ∀ b : Fin j, ∀ c : Fin k, ∀ d : Fin l,
    FPM_Eq ctx (T a b c d) (S a b c d)

/-- Componentwise boundedness for finite 4-tensors. -/
def FPM_Tensor4_Bounded {i j k l : ℕ}
    (T : FPM_Tensor4 i j k l) (C : ℕ+) : Prop :=
  ∀ a : Fin i, ∀ b : Fin j, ∀ c : Fin k, ∀ d : Fin l,
    FPM_Bounded (T a b c d) C


/-
  Basic projection lemmas.
-/

@[simp] theorem FPM_Vector_Eq_app
    {ctx : _root_.Context} {n : ℕ}
    {v w : FPM_Vector n}
    (h : FPM_Vector_Eq ctx v w) (i : Fin n) :
    FPM_Eq ctx (v i) (w i) :=
  h i

@[simp] theorem FPM_Vector_Bounded_app
    {n : ℕ} {v : FPM_Vector n} {C : ℕ+}
    (h : FPM_Vector_Bounded v C) (i : Fin n) :
    FPM_Bounded (v i) C :=
  h i

@[simp] theorem FPM_Matrix_Eq_app
    {ctx : _root_.Context} {m n : ℕ}
    {A B : FPM_Matrix m n}
    (h : FPM_Matrix_Eq ctx A B) (i : Fin m) (j : Fin n) :
    FPM_Eq ctx (A i j) (B i j) :=
  h i j

@[simp] theorem FPM_Matrix_Bounded_app
    {m n : ℕ} {A : FPM_Matrix m n} {C : ℕ+}
    (h : FPM_Matrix_Bounded A C) (i : Fin m) (j : Fin n) :
    FPM_Bounded (A i j) C :=
  h i j

@[simp] theorem FPM_Tensor3_Eq_app
    {ctx : _root_.Context} {i j k : ℕ}
    {T S : FPM_Tensor3 i j k}
    (h : FPM_Tensor3_Eq ctx T S)
    (a : Fin i) (b : Fin j) (c : Fin k) :
    FPM_Eq ctx (T a b c) (S a b c) :=
  h a b c

@[simp] theorem FPM_Tensor3_Bounded_app
    {i j k : ℕ} {T : FPM_Tensor3 i j k} {C : ℕ+}
    (h : FPM_Tensor3_Bounded T C)
    (a : Fin i) (b : Fin j) (c : Fin k) :
    FPM_Bounded (T a b c) C :=
  h a b c

@[simp] theorem FPM_Tensor4_Eq_app
    {ctx : _root_.Context} {i j k l : ℕ}
    {T S : FPM_Tensor4 i j k l}
    (h : FPM_Tensor4_Eq ctx T S)
    (a : Fin i) (b : Fin j) (c : Fin k) (d : Fin l) :
    FPM_Eq ctx (T a b c d) (S a b c d) :=
  h a b c d

@[simp] theorem FPM_Tensor4_Bounded_app
    {i j k l : ℕ} {T : FPM_Tensor4 i j k l} {C : ℕ+}
    (h : FPM_Tensor4_Bounded T C)
    (a : Fin i) (b : Fin j) (c : Fin k) (d : Fin l) :
    FPM_Bounded (T a b c d) C :=
  h a b c d


/-
  Constructor lemmas.
-/

theorem FPM_Vector_Eq_mk
    {ctx : _root_.Context} {n : ℕ}
    {v w : FPM_Vector n}
    (h : ∀ i : Fin n, FPM_Eq ctx (v i) (w i)) :
    FPM_Vector_Eq ctx v w := by
  intro i
  exact h i

theorem FPM_Matrix_Eq_mk
    {ctx : _root_.Context} {m n : ℕ}
    {A B : FPM_Matrix m n}
    (h : ∀ i : Fin m, ∀ j : Fin n, FPM_Eq ctx (A i j) (B i j)) :
    FPM_Matrix_Eq ctx A B := by
  intro i j
  exact h i j

theorem FPM_Tensor3_Eq_mk
    {ctx : _root_.Context} {i j k : ℕ}
    {T S : FPM_Tensor3 i j k}
    (h : ∀ a : Fin i, ∀ b : Fin j, ∀ c : Fin k,
      FPM_Eq ctx (T a b c) (S a b c)) :
    FPM_Tensor3_Eq ctx T S := by
  intro a b c
  exact h a b c

theorem FPM_Tensor4_Eq_mk
    {ctx : _root_.Context} {i j k l : ℕ}
    {T S : FPM_Tensor4 i j k l}
    (h : ∀ a : Fin i, ∀ b : Fin j, ∀ c : Fin k, ∀ d : Fin l,
      FPM_Eq ctx (T a b c d) (S a b c d)) :
    FPM_Tensor4_Eq ctx T S := by
  intro a b c d
  exact h a b c d

theorem FPM_Vector_Bounded_mk
    {n : ℕ} {v : FPM_Vector n} {C : ℕ+}
    (h : ∀ i : Fin n, FPM_Bounded (v i) C) :
    FPM_Vector_Bounded v C := by
  intro i
  exact h i

theorem FPM_Matrix_Bounded_mk
    {m n : ℕ} {A : FPM_Matrix m n} {C : ℕ+}
    (h : ∀ i : Fin m, ∀ j : Fin n, FPM_Bounded (A i j) C) :
    FPM_Matrix_Bounded A C := by
  intro i j
  exact h i j

theorem FPM_Tensor3_Bounded_mk
    {i j k : ℕ} {T : FPM_Tensor3 i j k} {C : ℕ+}
    (h : ∀ a : Fin i, ∀ b : Fin j, ∀ c : Fin k,
      FPM_Bounded (T a b c) C) :
    FPM_Tensor3_Bounded T C := by
  intro a b c
  exact h a b c

theorem FPM_Tensor4_Bounded_mk
    {i j k l : ℕ} {T : FPM_Tensor4 i j k l} {C : ℕ+}
    (h : ∀ a : Fin i, ∀ b : Fin j, ∀ c : Fin k, ∀ d : Fin l,
      FPM_Bounded (T a b c d) C) :
    FPM_Tensor4_Bounded T C := by
  intro a b c d
  exact h a b c d

/- ========================================================================
   SECTION 3: BASIC OPERATIONS
   We begin with pointwise algebra only:
   - negation,
   - addition,
   - subtraction.
   Multiplicative constructions such as dot products and matrix products
   will come later because they require finite-sum transport.
   ======================================================================== -/

/- --- Vectors ----------------------------------------------------------- -/
instance {n : ℕ} : Neg (FPM_Vector n) :=
  ⟨fun v i => -(v i)⟩

instance {n : ℕ} : Add (FPM_Vector n) :=
  ⟨fun v w i => v i + w i⟩

instance {n : ℕ} : Sub (FPM_Vector n) :=
  ⟨fun v w => v + (-w)⟩

@[simp] theorem FPM_Vector_neg_apply
    {n : ℕ} (v : FPM_Vector n) (i : Fin n) :
    (-v) i = -(v i) := rfl

@[simp] theorem FPM_Vector_add_apply
    {n : ℕ} (v w : FPM_Vector n) (i : Fin n) :
    (v + w) i = v i + w i := rfl

@[simp] theorem FPM_Vector_sub_apply
    {n : ℕ} (v w : FPM_Vector n) (i : Fin n) :
    (v - w) i = v i + (-(w i)) := rfl

--- Matrices ----------------------------------------------------------
instance {m n : ℕ} : Neg (FPM_Matrix m n) :=
  ⟨fun A i j => -(A i j)⟩

instance {m n : ℕ} : Add (FPM_Matrix m n) :=
  ⟨fun A B i j => A i j + B i j⟩

instance {m n : ℕ} : Sub (FPM_Matrix m n) :=
  ⟨fun A B => A + (-B)⟩

@[simp] theorem FPM_Matrix_neg_apply
    {m n : ℕ} (A : FPM_Matrix m n) (i : Fin m) (j : Fin n) :
    (-A) i j = -(A i j) := rfl

@[simp] theorem FPM_Matrix_add_apply
    {m n : ℕ} (A B : FPM_Matrix m n) (i : Fin m) (j : Fin n) :
    (A + B) i j = A i j + B i j := rfl

@[simp] theorem FPM_Matrix_sub_apply
    {m n : ℕ} (A B : FPM_Matrix m n) (i : Fin m) (j : Fin n) :
    (A - B) i j = A i j + (-(B i j)) := rfl

--- 3-tensors --------------------------------------------------------- -/
instance {i j k : ℕ} : Neg (FPM_Tensor3 i j k) :=
  ⟨fun T a b c => -(T a b c)⟩

instance {i j k : ℕ} : Add (FPM_Tensor3 i j k) :=
  ⟨fun T S a b c => T a b c + S a b c⟩

instance {i j k : ℕ} : Sub (FPM_Tensor3 i j k) :=
  ⟨fun T S => T + (-S)⟩

@[simp] theorem FPM_Tensor3_neg_apply
    {i j k : ℕ} (T : FPM_Tensor3 i j k)
    (a : Fin i) (b : Fin j) (c : Fin k) :
    (-T) a b c = -(T a b c) := rfl

@[simp] theorem FPM_Tensor3_add_apply
    {i j k : ℕ} (T S : FPM_Tensor3 i j k)
    (a : Fin i) (b : Fin j) (c : Fin k) :
    (T + S) a b c = T a b c + S a b c := rfl

@[simp] theorem FPM_Tensor3_sub_apply
    {i j k : ℕ} (T S : FPM_Tensor3 i j k)
    (a : Fin i) (b : Fin j) (c : Fin k) :
    (T - S) a b c = T a b c + (-(S a b c)) := rfl

/-- 4-tensors --------------------------------------------------------- -/
instance {i j k l : ℕ} : Neg (FPM_Tensor4 i j k l) :=
  ⟨fun T a b c d => -(T a b c d)⟩

instance {i j k l : ℕ} : Add (FPM_Tensor4 i j k l) :=
  ⟨fun T S a b c d => T a b c d + S a b c d⟩

instance {i j k l : ℕ} : Sub (FPM_Tensor4 i j k l) :=
  ⟨fun T S => T + (-S)⟩

@[simp] theorem FPM_Tensor4_neg_apply
    {i j k l : ℕ} (T : FPM_Tensor4 i j k l)
    (a : Fin i) (b : Fin j) (c : Fin k) (d : Fin l) :
    (-T) a b c d = -(T a b c d) := rfl

@[simp] theorem FPM_Tensor4_add_apply
    {i j k l : ℕ} (T S : FPM_Tensor4 i j k l)
    (a : Fin i) (b : Fin j) (c : Fin k) (d : Fin l) :
    (T + S) a b c d = T a b c d + S a b c d := rfl

@[simp] theorem FPM_Tensor4_sub_apply
    {i j k l : ℕ} (T S : FPM_Tensor4 i j k l)
    (a : Fin i) (b : Fin j) (c : Fin k) (d : Fin l) :
    (T - S) a b c d = T a b c d + (-(S a b c d)) := rfl

/- ========================================================================
   SECTION 4: BASIC TRANSPORT
   These are the pointwise lifts of the visible real substitution theorems.
   No finite sums appear yet; each proof is purely componentwise.
   ======================================================================== -/

/-- Vectors -----------------------------------------------------------

Exact shifted-context transport for vector negation. -/
theorem FPM_Vector_Neg_Substitution
    (ctx : _root_.Context) {n : ℕ}
    (v₁ v₂ : FPM_Vector n)
    (h : FPM_Vector_Eq (shift_context_unary ctx FPM_Neg) v₁ v₂) :
    FPM_Vector_Eq ctx (-v₁) (-v₂) := by
  intro i
  exact FPM_Unary_Substitution ctx FPM_Neg (v₁ i) (v₂ i) (h i)

/-- Exact shifted-context transport for vector addition. -/
theorem FPM_Vector_Add_Substitution
    (ctx : _root_.Context) {n : ℕ}
    (v₁ v₂ w₁ w₂ : FPM_Vector n)
    (hv : FPM_Vector_Eq (shift_context_bin ctx FPM_Add) v₁ v₂)
    (hw : FPM_Vector_Eq (shift_context_bin ctx FPM_Add) w₁ w₂) :
    FPM_Vector_Eq ctx (v₁ + w₁) (v₂ + w₂) := by
  intro i
  exact FPM_Add_Substitution ctx (v₁ i) (v₂ i) (w₁ i) (w₂ i) (hv i) (hw i)

/-- Exact shifted-context transport for vector subtraction. -/
theorem FPM_Vector_Sub_Substitution
    (ctx : _root_.Context) {n : ℕ}
    (v₁ v₂ w₁ w₂ : FPM_Vector n)
    (hv : FPM_Vector_Eq (shift_context_bin ctx FPM_Add) v₁ v₂)
    (hw : FPM_Vector_Eq (shift_context_bin ctx FPM_Add) (-w₁) (-w₂)) :
    FPM_Vector_Eq ctx (v₁ - w₁) (v₂ - w₂) := by
  simpa [Sub.sub] using
    FPM_Vector_Add_Substitution ctx v₁ v₂ (-w₁) (-w₂) hv hw


/-- Matrices ----------------------------------------------------------

Exact shifted-context transport for matrix negation. -/
theorem FPM_Matrix_Neg_Substitution
    (ctx : _root_.Context) {m n : ℕ}
    (A B : FPM_Matrix m n)
    (h : FPM_Matrix_Eq (shift_context_unary ctx FPM_Neg) A B) :
    FPM_Matrix_Eq ctx (-A) (-B) := by
  intro i j
  exact FPM_Unary_Substitution ctx FPM_Neg (A i j) (B i j) (h i j)

/-- Exact shifted-context transport for matrix addition. -/
theorem FPM_Matrix_Add_Substitution
    (ctx : _root_.Context) {m n : ℕ}
    (A₁ A₂ B₁ B₂ : FPM_Matrix m n)
    (hA : FPM_Matrix_Eq (shift_context_bin ctx FPM_Add) A₁ A₂)
    (hB : FPM_Matrix_Eq (shift_context_bin ctx FPM_Add) B₁ B₂) :
    FPM_Matrix_Eq ctx (A₁ + B₁) (A₂ + B₂) := by
  intro i j
  exact FPM_Add_Substitution ctx (A₁ i j) (A₂ i j) (B₁ i j) (B₂ i j)
    (hA i j) (hB i j)

/-- Exact shifted-context transport for matrix subtraction. -/
theorem FPM_Matrix_Sub_Substitution
    (ctx : _root_.Context) {m n : ℕ}
    (A₁ A₂ B₁ B₂ : FPM_Matrix m n)
    (hA : FPM_Matrix_Eq (shift_context_bin ctx FPM_Add) A₁ A₂)
    (hB : FPM_Matrix_Eq (shift_context_bin ctx FPM_Add) (-B₁) (-B₂)) :
    FPM_Matrix_Eq ctx (A₁ - B₁) (A₂ - B₂) := by
  simpa [Sub.sub] using
    FPM_Matrix_Add_Substitution ctx A₁ A₂ (-B₁) (-B₂) hA hB


/-- 3-tensors ---------------------------------------------------------

Exact shifted-context transport for 3-tensor negation. -/
theorem FPM_Tensor3_Neg_Substitution
    (ctx : _root_.Context) {i j k : ℕ}
    (T S : FPM_Tensor3 i j k)
    (h : FPM_Tensor3_Eq (shift_context_unary ctx FPM_Neg) T S) :
    FPM_Tensor3_Eq ctx (-T) (-S) := by
  intro a b c
  exact FPM_Unary_Substitution ctx FPM_Neg (T a b c) (S a b c) (h a b c)

/-- Exact shifted-context transport for 3-tensor addition. -/
theorem FPM_Tensor3_Add_Substitution
    (ctx : _root_.Context) {i j k : ℕ}
    (T₁ T₂ S₁ S₂ : FPM_Tensor3 i j k)
    (hT : FPM_Tensor3_Eq (shift_context_bin ctx FPM_Add) T₁ T₂)
    (hS : FPM_Tensor3_Eq (shift_context_bin ctx FPM_Add) S₁ S₂) :
    FPM_Tensor3_Eq ctx (T₁ + S₁) (T₂ + S₂) := by
  intro a b c
  exact FPM_Add_Substitution ctx
    (T₁ a b c) (T₂ a b c)
    (S₁ a b c) (S₂ a b c)
    (hT a b c) (hS a b c)

/-- Exact shifted-context transport for 3-tensor subtraction. -/
theorem FPM_Tensor3_Sub_Substitution
    (ctx : _root_.Context) {i j k : ℕ}
    (T₁ T₂ S₁ S₂ : FPM_Tensor3 i j k)
    (hT : FPM_Tensor3_Eq (shift_context_bin ctx FPM_Add) T₁ T₂)
    (hS : FPM_Tensor3_Eq (shift_context_bin ctx FPM_Add) (-S₁) (-S₂)) :
    FPM_Tensor3_Eq ctx (T₁ - S₁) (T₂ - S₂) := by
  simpa [Sub.sub] using
    FPM_Tensor3_Add_Substitution ctx T₁ T₂ (-S₁) (-S₂) hT hS


/-- - 4-tensors ---------------------------------------------------------

 Exact shifted-context transport for 4-tensor negation. -/
theorem FPM_Tensor4_Neg_Substitution
    (ctx : _root_.Context) {i j k l : ℕ}
    (T S : FPM_Tensor4 i j k l)
    (h : FPM_Tensor4_Eq (shift_context_unary ctx FPM_Neg) T S) :
    FPM_Tensor4_Eq ctx (-T) (-S) := by
  intro a b c d
  exact FPM_Unary_Substitution ctx FPM_Neg
    (T a b c d) (S a b c d) (h a b c d)

/-- Exact shifted-context transport for 4-tensor addition. -/
theorem FPM_Tensor4_Add_Substitution
    (ctx : _root_.Context) {i j k l : ℕ}
    (T₁ T₂ S₁ S₂ : FPM_Tensor4 i j k l)
    (hT : FPM_Tensor4_Eq (shift_context_bin ctx FPM_Add) T₁ T₂)
    (hS : FPM_Tensor4_Eq (shift_context_bin ctx FPM_Add) S₁ S₂) :
    FPM_Tensor4_Eq ctx (T₁ + S₁) (T₂ + S₂) := by
  intro a b c d
  exact FPM_Add_Substitution ctx
    (T₁ a b c d) (T₂ a b c d)
    (S₁ a b c d) (S₂ a b c d)
    (hT a b c d) (hS a b c d)

/-- Exact shifted-context transport for 4-tensor subtraction. -/
theorem FPM_Tensor4_Sub_Substitution
    (ctx : _root_.Context) {i j k l : ℕ}
    (T₁ T₂ S₁ S₂ : FPM_Tensor4 i j k l)
    (hT : FPM_Tensor4_Eq (shift_context_bin ctx FPM_Add) T₁ T₂)
    (hS : FPM_Tensor4_Eq (shift_context_bin ctx FPM_Add) (-S₁) (-S₂)) :
    FPM_Tensor4_Eq ctx (T₁ - S₁) (T₂ - S₂) := by
  simpa [Sub.sub] using
    FPM_Tensor4_Add_Substitution ctx T₁ T₂ (-S₁) (-S₂) hT hS

/- ========================================================================
   SECTION 5: GUARDED POINTWISE MULTIPLICATION
   We introduce Hadamard-style multiplication first:
   - vectors,
   - matrices,
   - 3-tensors,
   - 4-tensors.

   This stays fully within the visible real transport engine, since each
   component is just one guarded real multiplication.
   ======================================================================== -/

/- --- Pointwise multiplication operators -------------------------------- -/

/-- Hadamard product of finite vectors. -/
def FPM_Vector_hMul {n : ℕ}
    (v w : FPM_Vector n) : FPM_Vector n :=
  fun i => v i * w i

/-- Hadamard product of finite matrices. -/
def FPM_Matrix_hMul {m n : ℕ}
    (A B : FPM_Matrix m n) : FPM_Matrix m n :=
  fun i j => A i j * B i j

/-- Hadamard product of finite 3-tensors. -/
def FPM_Tensor3_hMul {i j k : ℕ}
    (T S : FPM_Tensor3 i j k) : FPM_Tensor3 i j k :=
  fun a b c => T a b c * S a b c

/-- Hadamard product of finite 4-tensors. -/
def FPM_Tensor4_hMul {i j k l : ℕ}
    (T S : FPM_Tensor4 i j k l) : FPM_Tensor4 i j k l :=
  fun a b c d => T a b c d * S a b c d

@[simp] theorem FPM_Vector_hMul_apply
    {n : ℕ} (v w : FPM_Vector n) (i : Fin n) :
    FPM_Vector_hMul v w i = v i * w i := rfl

@[simp] theorem FPM_Matrix_hMul_apply
    {m n : ℕ} (A B : FPM_Matrix m n) (i : Fin m) (j : Fin n) :
    FPM_Matrix_hMul A B i j = A i j * B i j := rfl

@[simp] theorem FPM_Tensor3_hMul_apply
    {i j k : ℕ} (T S : FPM_Tensor3 i j k)
    (a : Fin i) (b : Fin j) (c : Fin k) :
    FPM_Tensor3_hMul T S a b c = T a b c * S a b c := rfl

@[simp] theorem FPM_Tensor4_hMul_apply
    {i j k l : ℕ} (T S : FPM_Tensor4 i j k l)
    (a : Fin i) (b : Fin j) (c : Fin k) (d : Fin l) :
    FPM_Tensor4_hMul T S a b c d = T a b c d * S a b c d := rfl


/-
  The support context is just the guarded real multiplication context.
-/

def shift_context_vector_hMul
    (ctx : _root_.Context) (C : ℕ+) : _root_.Context :=
  shift_context_mul ctx C

def shift_context_matrix_hMul
    (ctx : _root_.Context) (C : ℕ+) : _root_.Context :=
  shift_context_mul ctx C

def shift_context_tensor3_hMul
    (ctx : _root_.Context) (C : ℕ+) : _root_.Context :=
  shift_context_mul ctx C

def shift_context_tensor4_hMul
    (ctx : _root_.Context) (C : ℕ+) : _root_.Context :=
  shift_context_mul ctx C


/-- Vector transport --------------------------------------------------

 Exact guarded transport for vector Hadamard multiplication. -/
theorem FPM_Vector_hMul_Substitution
    (ctx : _root_.Context) (C : ℕ+) {n : ℕ}
    (v₁ v₂ w₁ w₂ : FPM_Vector n)
    (hv : FPM_Vector_Eq (shift_context_vector_hMul ctx C) v₁ v₂)
    (hw : FPM_Vector_Eq (shift_context_vector_hMul ctx C) w₁ w₂)
    (hv_bd : FPM_Vector_Bounded v₁ C)
    (hw_bd : FPM_Vector_Bounded w₂ C) :
    FPM_Vector_Eq ctx (FPM_Vector_hMul v₁ w₁) (FPM_Vector_hMul v₂ w₂) := by
  intro i
  exact FPM_Mul_Substitution
    ctx C
    (v₁ i) (v₂ i) (w₁ i) (w₂ i)
    (hv_bd i) (hw_bd i)
    (hv i) (hw i)

/-- Matrix transport --------------------------------------------------

Exact guarded transport for matrix Hadamard multiplication. -/
theorem FPM_Matrix_hMul_Substitution
    (ctx : _root_.Context) (C : ℕ+) {m n : ℕ}
    (A₁ A₂ B₁ B₂ : FPM_Matrix m n)
    (hA : FPM_Matrix_Eq (shift_context_matrix_hMul ctx C) A₁ A₂)
    (hB : FPM_Matrix_Eq (shift_context_matrix_hMul ctx C) B₁ B₂)
    (hA_bd : FPM_Matrix_Bounded A₁ C)
    (hB_bd : FPM_Matrix_Bounded B₂ C) :
    FPM_Matrix_Eq ctx (FPM_Matrix_hMul A₁ B₁) (FPM_Matrix_hMul A₂ B₂) := by
  intro i j
  exact FPM_Mul_Substitution
    ctx C
    (A₁ i j) (A₂ i j) (B₁ i j) (B₂ i j)
    (hA_bd i j) (hB_bd i j)
    (hA i j) (hB i j)

/-- 3-tensor transport ------------------------------------------------

Exact guarded transport for 3-tensor Hadamard multiplication. -/
theorem FPM_Tensor3_hMul_Substitution
    (ctx : _root_.Context) (C : ℕ+) {i j k : ℕ}
    (T₁ T₂ S₁ S₂ : FPM_Tensor3 i j k)
    (hT : FPM_Tensor3_Eq (shift_context_tensor3_hMul ctx C) T₁ T₂)
    (hS : FPM_Tensor3_Eq (shift_context_tensor3_hMul ctx C) S₁ S₂)
    (hT_bd : FPM_Tensor3_Bounded T₁ C)
    (hS_bd : FPM_Tensor3_Bounded S₂ C) :
    FPM_Tensor3_Eq ctx (FPM_Tensor3_hMul T₁ S₁) (FPM_Tensor3_hMul T₂ S₂) := by
  intro a b c
  exact FPM_Mul_Substitution
    ctx C
    (T₁ a b c) (T₂ a b c) (S₁ a b c) (S₂ a b c)
    (hT_bd a b c) (hS_bd a b c)
    (hT a b c) (hS a b c)

/-- 4-tensor transport ------------------------------------------------

Exact guarded transport for 4-tensor Hadamard multiplication. -/
theorem FPM_Tensor4_hMul_Substitution
    (ctx : _root_.Context) (C : ℕ+) {i j k l : ℕ}
    (T₁ T₂ S₁ S₂ : FPM_Tensor4 i j k l)
    (hT : FPM_Tensor4_Eq (shift_context_tensor4_hMul ctx C) T₁ T₂)
    (hS : FPM_Tensor4_Eq (shift_context_tensor4_hMul ctx C) S₁ S₂)
    (hT_bd : FPM_Tensor4_Bounded T₁ C)
    (hS_bd : FPM_Tensor4_Bounded S₂ C) :
    FPM_Tensor4_Eq ctx (FPM_Tensor4_hMul T₁ S₁) (FPM_Tensor4_hMul T₂ S₂) := by
  intro a b c d
  exact FPM_Mul_Substitution
    ctx C
    (T₁ a b c d) (T₂ a b c d) (S₁ a b c d) (S₂ a b c d)
    (hT_bd a b c d) (hS_bd a b c d)
    (hT a b c d) (hS a b c d)

/- ========================================================================
   SECTION 6: NATIVE N-ARY SUMS AND CONTRACTIONS

   We replace recursive nonempty summation by the native ontology-sum layer:
   - no `FPM_sum1`
   - no `FPM_sum_nary`
   - dot products, matrix multiplication, and tensor contraction are defined
     directly by `FPM_sum_nary`.
   ======================================================================== -/

/-- Support context for a contracted product family that will later be
    collapsed by native n-ary summation.  The multiplication transport
    should land in `shift_context_nary ...`, so we package the support
    context in the exact form needed by `FPM_Mul_Substitution`. -/
def shift_context_contract_nary
    (ctx : _root_.Context) (C : ℕ+) (n : ℕ+) : _root_.Context :=
  shift_context_mul (shift_context_nary ctx n (FPM_AddNary n.val)) C


def FPMMatrixrow m n (A : FPM_Matrix m n) (i : Fin m) : FPM_Vector n :=
  fun j => A i j

def FPMMatrixcol m n (A : FPM_Matrix m n) (j : Fin n) : FPM_Vector m :=
  fun i => A i j

abbrev FPM_Matrix_row := FPMMatrixrow
abbrev FPM_Matrix_col := FPMMatrixcol

theorem FPM_Matrix_row_apply {m n : ℕ} (A : FPM_Matrix m n) (i : Fin m) (j : Fin n) :
    FPM_Matrix_row m n A i j = A i j := rfl

@[simp] theorem FPM_Matrix_col_apply {m n : ℕ} (A : FPM_Matrix m n) (j : Fin n) (i : Fin m) :
    FPM_Matrix_col m n A j i = A i j := rfl

/-- Dot product using native n-ary summation. -/
noncomputable def FPM_Vector_dot_nary {n : ℕ+}
    (v w : FPM_Vector n.val) : FPM_Real :=
  FPM_sum_nary (fun i => v i * w i)

@[simp] theorem FPM_Vector_dot_nary_def
    {n : ℕ+} (v w : FPM_Vector n.val) :
    FPM_Vector_dot_nary v w = FPM_sum_nary (fun i => v i * w i) := rfl

/-- Matrix multiplication using native n-ary summation over the inner
    contracted dimension. -/
noncomputable def FPM_Matrix_mul_nary
    {m p : ℕ} {n : ℕ+}
    (A : FPM_Matrix m n.val) (B : FPM_Matrix n.val p) : FPM_Matrix m p :=
  fun i j => FPM_sum_nary (fun r => A i r * B r j)

@[simp] theorem FPM_Matrix_mul_nary_apply
    {m p : ℕ} {n : ℕ+}
    (A : FPM_Matrix m n.val) (B : FPM_Matrix n.val p)
    (i : Fin m) (j : Fin p) :
    FPM_Matrix_mul_nary A B i j = FPM_sum_nary (fun r => A i r * B r j) := rfl

/-- Contract the last index of a 3-tensor with the first index of another
    3-tensor using native n-ary summation over the shared contracted index. -/
noncomputable def FPM_Tensor3_contract_nary
    {i j l m : ℕ} {k : ℕ+}
    (T : FPM_Tensor3 i j k.val) (S : FPM_Tensor3 k.val l m) :
    FPM_Tensor4 i j l m :=
  fun a b d e => FPM_sum_nary (fun c => T a b c * S c d e)

@[simp] theorem FPM_Tensor3_contract_nary_apply
    {i j l m : ℕ} {k : ℕ+}
    (T : FPM_Tensor3 i j k.val) (S : FPM_Tensor3 k.val l m)
    (a : Fin i) (b : Fin j) (d : Fin l) (e : Fin m) :
    FPM_Tensor3_contract_nary T S a b d e
      = FPM_sum_nary (fun c => T a b c * S c d e) := rfl

/-- Optional aliases, mirroring the old Section 6 naming style. -/
abbrev shift_context_dot_nary
    (ctx : _root_.Context) (C : ℕ+) (n : ℕ+) : _root_.Context :=
  shift_context_contract_nary ctx C n

abbrev shift_context_matrix_mul_nary
    (ctx : _root_.Context) (C : ℕ+) (n : ℕ+) : _root_.Context :=
  shift_context_contract_nary ctx C n

abbrev shift_context_tensor3_contract_nary
    (ctx : _root_.Context) (C : ℕ+) (k : ℕ+) : _root_.Context :=
  shift_context_contract_nary ctx C k

/- ========================================================================
   SECTION 7: TRANSPORT FOR NATIVE N-ARY CONTRACTIONS

   These replace the old recursive `FPM_sum1`-based transport theorems.
   The pattern is always:
   1. prove pointwise product transport at the n-ary support context,
   2. collapse the transported family with `FPM_NaryAdd_Substitution`.
   ======================================================================== -/

/-- Exact guarded transport for native n-ary vector dot product. -/
theorem FPM_Vector_dot_nary_Substitution
    (ctx : _root_.Context) (C : ℕ+) {n : ℕ+}
    (v₁ v₂ w₁ w₂ : FPM_Vector n.val)
    (hv : FPM_Vector_Eq (shift_context_contract_nary ctx C n) v₁ v₂)
    (hw : FPM_Vector_Eq (shift_context_contract_nary ctx C n) w₁ w₂)
    (hv_bd : FPM_Vector_Bounded v₁ C)
    (hw_bd : FPM_Vector_Bounded w₂ C) :
    FPM_Eq ctx (FPM_Vector_dot_nary v₁ w₁) (FPM_Vector_dot_nary v₂ w₂) := by
  unfold FPM_Vector_dot_nary
  apply FPM_NaryAdd_Substitution
  intro i
  exact FPM_Mul_Substitution
    (shift_context_nary ctx n (FPM_AddNary n.val))
    C
    (v₁ i) (v₂ i)
    (w₁ i) (w₂ i)
    (hv_bd i)
    (hw_bd i)
    (by
      simpa [shift_context_contract_nary] using hv i)
    (by
      simpa [shift_context_contract_nary] using hw i)

/-- Exact guarded transport for native n-ary matrix multiplication. -/
theorem FPM_Matrix_mul_nary_Substitution
    (ctx : _root_.Context) (C : ℕ+) {m p : ℕ} {n : ℕ+}
    (A₁ A₂ : FPM_Matrix m n.val)
    (B₁ B₂ : FPM_Matrix n.val p)
    (hA : ∀ i : Fin m, ∀ k : Fin n.val,
      FPM_Eq (shift_context_contract_nary ctx C n) (A₁ i k) (A₂ i k))
    (hB : ∀ k : Fin n.val, ∀ j : Fin p,
      FPM_Eq (shift_context_contract_nary ctx C n) (B₁ k j) (B₂ k j))
    (hA_bd : FPM_Matrix_Bounded A₁ C)
    (hB_bd : FPM_Matrix_Bounded B₂ C) :
    FPM_Matrix_Eq ctx (FPM_Matrix_mul_nary A₁ B₁) (FPM_Matrix_mul_nary A₂ B₂) := by
  intro i j
  unfold FPM_Matrix_mul_nary
  apply FPM_NaryAdd_Substitution
  intro r
  exact FPM_Mul_Substitution
    (shift_context_nary ctx n (FPM_AddNary n.val))
    C
    (A₁ i r) (A₂ i r)
    (B₁ r j) (B₂ r j)
    (hA_bd i r)
    (hB_bd r j)
    (by
      simpa [shift_context_contract_nary] using hA i r)
    (by
      simpa [shift_context_contract_nary] using hB r j)

/-- Exact guarded transport for native n-ary 3-tensor contraction. -/
theorem FPM_Tensor3_contract_nary_Substitution
    (ctx : _root_.Context) (C : ℕ+) {i j l m : ℕ} {k : ℕ+}
    (T₁ T₂ : FPM_Tensor3 i j k.val)
    (S₁ S₂ : FPM_Tensor3 k.val l m)
    (hT : ∀ a : Fin i, ∀ b : Fin j, ∀ c : Fin k.val,
      FPM_Eq (shift_context_contract_nary ctx C k) (T₁ a b c) (T₂ a b c))
    (hS : ∀ c : Fin k.val, ∀ d : Fin l, ∀ e : Fin m,
      FPM_Eq (shift_context_contract_nary ctx C k) (S₁ c d e) (S₂ c d e))
    (hT_bd : FPM_Tensor3_Bounded T₁ C)
    (hS_bd : FPM_Tensor3_Bounded S₂ C) :
    FPM_Tensor4_Eq ctx
      (FPM_Tensor3_contract_nary T₁ S₁)
      (FPM_Tensor3_contract_nary T₂ S₂) := by
  intro a b d e
  unfold FPM_Tensor3_contract_nary
  apply FPM_NaryAdd_Substitution
  intro c
  exact FPM_Mul_Substitution
    (shift_context_nary ctx k (FPM_AddNary k.val))
    C
    (T₁ a b c) (T₂ a b c)
    (S₁ c d e) (S₂ c d e)
    (hT_bd a b c)
    (hS_bd c d e)
    (by
      simpa [shift_context_contract_nary] using hT a b c)
    (by
      simpa [shift_context_contract_nary] using hS c d e)

/- ========================================================================
   SECTION 8: PUBLIC WRAPPERS
   These theorems package the earlier transport results into easier
   user-facing forms based on structured equality and boundedness data.
   ======================================================================== -/

/- --- Pointwise multiplication wrappers -------------------------------- -/

theorem FPM_Vector_hMul_Substitution_ofEq
    (ctx : _root_.Context) (C : ℕ+) {n : ℕ}
    (v₁ v₂ w₁ w₂ : FPM_Vector n)
    (hv : FPM_Vector_Eq (shift_context_vector_hMul ctx C) v₁ v₂)
    (hw : FPM_Vector_Eq (shift_context_vector_hMul ctx C) w₁ w₂)
    (hv_bd : FPM_Vector_Bounded v₁ C)
    (hw_bd : FPM_Vector_Bounded w₂ C) :
    FPM_Vector_Eq ctx (FPM_Vector_hMul v₁ w₁) (FPM_Vector_hMul v₂ w₂) := by
  exact FPM_Vector_hMul_Substitution
    ctx C v₁ v₂ w₁ w₂ hv hw hv_bd hw_bd

theorem FPM_Matrix_hMul_Substitution_ofEq
    (ctx : _root_.Context) (C : ℕ+) {m n : ℕ}
    (A₁ A₂ B₁ B₂ : FPM_Matrix m n)
    (hA : FPM_Matrix_Eq (shift_context_matrix_hMul ctx C) A₁ A₂)
    (hB : FPM_Matrix_Eq (shift_context_matrix_hMul ctx C) B₁ B₂)
    (hA_bd : FPM_Matrix_Bounded A₁ C)
    (hB_bd : FPM_Matrix_Bounded B₂ C) :
    FPM_Matrix_Eq ctx (FPM_Matrix_hMul A₁ B₁) (FPM_Matrix_hMul A₂ B₂) := by
  exact FPM_Matrix_hMul_Substitution
    ctx C A₁ A₂ B₁ B₂ hA hB hA_bd hB_bd

theorem FPM_Tensor3_hMul_Substitution_ofEq
    (ctx : _root_.Context) (C : ℕ+) {i j k : ℕ}
    (T₁ T₂ S₁ S₂ : FPM_Tensor3 i j k)
    (hT : FPM_Tensor3_Eq (shift_context_tensor3_hMul ctx C) T₁ T₂)
    (hS : FPM_Tensor3_Eq (shift_context_tensor3_hMul ctx C) S₁ S₂)
    (hT_bd : FPM_Tensor3_Bounded T₁ C)
    (hS_bd : FPM_Tensor3_Bounded S₂ C) :
    FPM_Tensor3_Eq ctx (FPM_Tensor3_hMul T₁ S₁) (FPM_Tensor3_hMul T₂ S₂) := by
  exact FPM_Tensor3_hMul_Substitution
    ctx C T₁ T₂ S₁ S₂ hT hS hT_bd hS_bd

theorem FPM_Tensor4_hMul_Substitution_ofEq
    (ctx : _root_.Context) (C : ℕ+) {i j k l : ℕ}
    (T₁ T₂ S₁ S₂ : FPM_Tensor4 i j k l)
    (hT : FPM_Tensor4_Eq (shift_context_tensor4_hMul ctx C) T₁ T₂)
    (hS : FPM_Tensor4_Eq (shift_context_tensor4_hMul ctx C) S₁ S₂)
    (hT_bd : FPM_Tensor4_Bounded T₁ C)
    (hS_bd : FPM_Tensor4_Bounded S₂ C) :
    FPM_Tensor4_Eq ctx (FPM_Tensor4_hMul T₁ S₁) (FPM_Tensor4_hMul T₂ S₂) := by
  exact FPM_Tensor4_hMul_Substitution
    ctx C T₁ T₂ S₁ S₂ hT hS hT_bd hS_bd


/- --- Dot-product wrappers --------------------------------------------- -/

theorem FPM_Sum_nary_Substitution_ofEq
    (ctx : _root_.Context) {n : ℕ+}
    (f g : Fin n.val → FPM_Real)
    (h : ∀ i : Fin n.val,
      FPM_Eq (shift_context_nary ctx n (FPM_AddNary n.val)) (f i) (g i)) :
    FPM_Eq ctx (FPM_sum_nary f) (FPM_sum_nary g) := by
  exact FPM_NaryAdd_Substitution ctx f g h

theorem FPM_Vector_dot_nary_Substitution_ofEq
    (ctx : _root_.Context) (C : ℕ+) {n : ℕ+}
    (v₁ v₂ w₁ w₂ : FPM_Vector n.val)
    (hv : FPM_Vector_Eq (shift_context_contract_nary ctx C n) v₁ v₂)
    (hw : FPM_Vector_Eq (shift_context_contract_nary ctx C n) w₁ w₂)
    (hv_bd : FPM_Vector_Bounded v₁ C)
    (hw_bd : FPM_Vector_Bounded w₂ C) :
    FPM_Eq ctx (FPM_Vector_dot_nary v₁ w₁) (FPM_Vector_dot_nary v₂ w₂) := by
  exact FPM_Vector_dot_nary_Substitution
    ctx C v₁ v₂ w₁ w₂ hv hw hv_bd hw_bd


/- --- Matrix multiplication wrappers ----------------------------------- -/

theorem FPM_Matrix_mul_nary_Substitution_ofEq
    (ctx : _root_.Context) (C : ℕ+) {m p : ℕ} {n : ℕ+}
    (A₁ A₂ : FPM_Matrix m n.val)
    (B₁ B₂ : FPM_Matrix n.val p)
    (hA : ∀ i : Fin m, ∀ k : Fin n.val,
      FPM_Eq (shift_context_contract_nary ctx C n) (A₁ i k) (A₂ i k))
    (hB : ∀ k : Fin n.val, ∀ j : Fin p,
      FPM_Eq (shift_context_contract_nary ctx C n) (B₁ k j) (B₂ k j))
    (hA_bd : FPM_Matrix_Bounded A₁ C)
    (hB_bd : FPM_Matrix_Bounded B₂ C) :
    FPM_Matrix_Eq ctx (FPM_Matrix_mul_nary A₁ B₁) (FPM_Matrix_mul_nary A₂ B₂) := by
  exact FPM_Matrix_mul_nary_Substitution
    ctx C A₁ A₂ B₁ B₂ hA hB hA_bd hB_bd


/- --- Tensor contraction wrappers -------------------------------------- -/

theorem FPM_Tensor3_contract_nary_Substitution_ofEq
    (ctx : _root_.Context) (C : ℕ+) {i j l m : ℕ} {k : ℕ+}
    (T₁ T₂ : FPM_Tensor3 i j k.val)
    (S₁ S₂ : FPM_Tensor3 k.val l m)
    (hT : ∀ a : Fin i, ∀ b : Fin j, ∀ c : Fin k.val,
      FPM_Eq (shift_context_contract_nary ctx C k) (T₁ a b c) (T₂ a b c))
    (hS : ∀ c : Fin k.val, ∀ d : Fin l, ∀ e : Fin m,
      FPM_Eq (shift_context_contract_nary ctx C k) (S₁ c d e) (S₂ c d e))
    (hT_bd : FPM_Tensor3_Bounded T₁ C)
    (hS_bd : FPM_Tensor3_Bounded S₂ C) :
    FPM_Tensor4_Eq ctx
      (FPM_Tensor3_contract_nary T₁ S₁)
      (FPM_Tensor3_contract_nary T₂ S₂) := by
  exact FPM_Tensor3_contract_nary_Substitution
    ctx C T₁ T₂ S₁ S₂ hT hS hT_bd hS_bd

/- --- Negation boundedness wrappers ------------------------------------- -/

theorem FPM_Vector_Bounded_neg
    {n : ℕ}
    {v : FPM_Vector n} {C : ℕ+}
    (h : FPM_Vector_Bounded v C) :
    FPM_Vector_Bounded (-v) C := by
  intro i
  simpa [FPM_Vector_neg_apply] using
    (FPM_Bounded_neg (h i))

theorem FPM_Matrix_Bounded_neg
    {m n : ℕ}
    {A : FPM_Matrix m n} {C : ℕ+}
    (h : FPM_Matrix_Bounded A C) :
    FPM_Matrix_Bounded (-A) C := by
  intro i j
  simpa [FPM_Matrix_neg_apply] using
    (FPM_Bounded_neg (h i j))

theorem FPM_Tensor3_Bounded_neg
    {i j k : ℕ}
    {T : FPM_Tensor3 i j k} {C : ℕ+}
    (h : FPM_Tensor3_Bounded T C) :
    FPM_Tensor3_Bounded (-T) C := by
  intro a b c
  simpa [FPM_Tensor3_neg_apply] using
    (FPM_Bounded_neg (h a b c))

theorem FPM_Tensor4_Bounded_neg
    {i j k l : ℕ}
    {T : FPM_Tensor4 i j k l} {C : ℕ+}
    (h : FPM_Tensor4_Bounded T C) :
    FPM_Tensor4_Bounded (-T) C := by
  intro a b c d
  simpa [FPM_Tensor4_neg_apply] using
    (FPM_Bounded_neg (h a b c d))

/- --- Row/column helper equalities ------------------------------------- -/

theorem FPM_Matrix_row_Eq_of_Matrix_Eq
    (ctx : _root_.Context) {m n : ℕ}
    (A B : FPM_Matrix m n)
    (h : FPM_Matrix_Eq ctx A B)
    (i : Fin m) :
    FPM_Vector_Eq ctx (FPM_Matrix_row m n A i) (FPM_Matrix_row m n B i) := by
  intro j
  simpa [FPM_Matrix_row] using h i j

theorem FPM_Matrix_col_Eq_of_Matrix_Eq
    (ctx : _root_.Context) {m n : ℕ}
    (A B : FPM_Matrix m n)
    (h : FPM_Matrix_Eq ctx A B)
    (j : Fin n) :
    FPM_Vector_Eq ctx (FPM_Matrix_col m n A j) (FPM_Matrix_col m n B j) := by
  intro i
  simpa [FPM_Matrix_col] using h i j

theorem FPM_Matrix_row_Bounded_of_Matrix_Bounded
    {m n : ℕ} (A : FPM_Matrix m n) (C : ℕ+)
    (h : FPM_Matrix_Bounded A C)
    (i : Fin m) :
    FPM_Vector_Bounded (FPM_Matrix_row m n A i) C := by
  intro j
  simpa [FPM_Matrix_row] using h i j

theorem FPM_Matrix_col_Bounded_of_Matrix_Bounded
    {m n : ℕ} (A : FPM_Matrix m n) (C : ℕ+)
    (h : FPM_Matrix_Bounded A C)
    (j : Fin n) :
    FPM_Vector_Bounded (FPM_Matrix_col m n A j) C := by
  intro i
  simpa [FPM_Matrix_col] using h i j

/- ========================================================================
   NEGATION / SUBTRACTION HELPERS
   ======================================================================== -/

/-- Pointwise equality of sequences: -(a + (-b)) and (-a) + (--b) -/
@[simp] theorem FPM_neg_add_neg_seq
    (a b : FPM_Real) (n : ℕ+) :
    (- (a + (-(b)))).seq n = ((-a) + (-( -b))).seq n := by
  simp [FPM_neg_seq, FPM_add_seq]
  ring

theorem FPM_Bounded_neg_add_neg
    {a b : FPM_Real} {C : ℕ+}
    (h : FPM_Bounded (a + (-(b))) C) :
    FPM_Bounded ((-a) + (-( -b))) C := by
  intro n
  have := FPM_Bounded_neg h n
  simp only [FPM_neg_seq, FPM_add_seq] at this ⊢
  convert this using 1
  ring_nf

theorem FPM_Bounded_neg_sub
    {a b : FPM_Real} {C : ℕ+}
    (h : FPM_Bounded (a - b) C) :
    FPM_Bounded ((-a) - (-b)) C := by
  intro n
  have := FPM_Bounded_neg h n
  simp only [FPM_neg_seq, FPM_sub_seq] at this ⊢
  convert this using 1
  ring_nf

theorem FPM_Vector_Bounded_neg_sub
    {n : ℕ}
    {v w : FPM_Vector n} {C : ℕ+}
    (h : FPM_Vector_Bounded (v - w) C) :
    FPM_Vector_Bounded ((-v) - (-w)) C := by
  intro i
  simpa [FPM_Vector_sub_apply, FPM_Vector_neg_apply] using
    (FPM_Bounded_neg_sub (h i))

theorem FPM_Matrix_Bounded_neg_sub
    {m n : ℕ}
    {A B : FPM_Matrix m n} {C : ℕ+}
    (h : FPM_Matrix_Bounded (A - B) C) :
    FPM_Matrix_Bounded ((-A) - (-B)) C := by
  intro i j
  simpa [FPM_Matrix_sub_apply, FPM_Matrix_neg_apply] using
    (FPM_Bounded_neg_sub (h i j))

theorem FPM_Tensor3_Bounded_neg_sub
    {i j k : ℕ}
    {T S : FPM_Tensor3 i j k} {C : ℕ+}
    (h : FPM_Tensor3_Bounded (T - S) C) :
    FPM_Tensor3_Bounded ((-T) - (-S)) C := by
  intro a b c
  simpa [FPM_Tensor3_sub_apply, FPM_Tensor3_neg_apply] using
    (FPM_Bounded_neg_sub (h a b c))

theorem FPM_Tensor4_Bounded_neg_sub
    {i j k l : ℕ}
    {T S : FPM_Tensor4 i j k l} {C : ℕ+}
    (h : FPM_Tensor4_Bounded (T - S) C) :
    FPM_Tensor4_Bounded ((-T) - (-S)) C := by
  intro a b c d
  simpa [FPM_Tensor4_sub_apply, FPM_Tensor4_neg_apply] using
    (FPM_Bounded_neg_sub (h a b c d))


/- ========================================================================
   SECTION 9: SMOKE TESTS
   These examples confirm that the final public API for finite vectors,
   matrices, and tensors is usable without adding any new compiler support.
   ======================================================================== -/

/- Sum -------------------------------------------------------------- -/

example
  (ctx : _root_.Context) (n : ℕ+) (f g : Fin n.val → FPM_Real)
  (h : ∀ i : Fin n.val,
    FPM_Eq (shift_context_nary ctx n (FPM_AddNary n.val)) (f i) (g i)) :
  FPM_Eq ctx (FPM_sum_nary f) (FPM_sum_nary g) := by
  exact FPM_Sum_nary_Substitution_ofEq ctx f g h


/- Dot product ------------------------------------------------------ -/

example (ctx : _root_.Context) (C : ℕ+) {n : ℕ}
    (v₁ v₂ w₁ w₂ : FPM_Vector (n + 1))
    (hv : ∀ i : Fin (n + 1),
      FPM_Eq (shift_context_dot_nary ctx C ⟨n + 1, Nat.succ_pos n⟩) (v₁ i) (v₂ i))
    (hw : ∀ i : Fin (n + 1),
      FPM_Eq (shift_context_dot_nary ctx C ⟨n + 1, Nat.succ_pos n⟩) (w₁ i) (w₂ i))
    (hv_bd : FPM_Vector_Bounded v₁ C)
    (hw_bd : FPM_Vector_Bounded w₂ C) :
    FPM_Eq ctx
      (FPM_Vector_dot_nary (n := ⟨n + 1, Nat.succ_pos n⟩) v₁ w₁)
      (FPM_Vector_dot_nary (n := ⟨n + 1, Nat.succ_pos n⟩) v₂ w₂) := by
  let N : ℕ+ := ⟨n + 1, Nat.succ_pos n⟩
  exact FPM_Vector_dot_nary_Substitution_ofEq
    (ctx := ctx) (C := C) (n := N) v₁ v₂ w₁ w₂
    (by
      intro i
      simpa [N, shift_context_dot_nary] using hv i)
    (by
      intro i
      simpa [N, shift_context_dot_nary] using hw i)
    hv_bd hw_bd

example (ctx : _root_.Context) (C : ℕ+) {n : ℕ}
    (v₁ v₂ w₁ w₂ : FPM_Vector (n + 1))
    (hv : ∀ i : Fin (n + 1),
      FPM_Eq (shift_context_dot_nary ctx C ⟨n + 1, Nat.succ_pos n⟩) (v₁ i) (v₂ i))
    (hw : ∀ i : Fin (n + 1),
      FPM_Eq (shift_context_dot_nary ctx C ⟨n + 1, Nat.succ_pos n⟩) (w₁ i) (w₂ i))
    (hv_bd : FPM_Vector_Bounded v₁ C)
    (hw_bd : FPM_Vector_Bounded w₂ C) :
    FPM_Eq ctx
      (FPM_Vector_dot_nary (n := ⟨n + 1, Nat.succ_pos n⟩) v₁ w₁)
      (FPM_Vector_dot_nary (n := ⟨n + 1, Nat.succ_pos n⟩) v₂ w₂) := by
  let N : ℕ+ := ⟨n + 1, Nat.succ_pos n⟩
  exact FPM_Vector_dot_nary_Substitution_ofEq
    (ctx := ctx) (C := C) (n := N) v₁ v₂ w₁ w₂
    (by
      intro i
      simpa [N, shift_context_dot_nary] using hv i)
    (by
      intro i
      simpa [N, shift_context_dot_nary] using hw i)
    hv_bd hw_bd


/- Matrix multiplication -------------------------------------------- -/

example (ctx : _root_.Context) (C : ℕ+) {m n p : ℕ}
    (A₁ A₂ : FPM_Matrix m (n + 1))
    (B₁ B₂ : FPM_Matrix (n + 1) p)
    (hA : ∀ i : Fin m, ∀ k : Fin (n + 1),
      FPM_Eq (shift_context_matrix_mul_nary ctx C ⟨n + 1, Nat.succ_pos n⟩) (A₁ i k) (A₂ i k))
    (hB : ∀ k : Fin (n + 1), ∀ j : Fin p,
      FPM_Eq (shift_context_matrix_mul_nary ctx C ⟨n + 1, Nat.succ_pos n⟩) (B₁ k j) (B₂ k j))
    (hA_bd : FPM_Matrix_Bounded A₁ C)
    (hB_bd : FPM_Matrix_Bounded B₂ C) :
    FPM_Matrix_Eq ctx
      (FPM_Matrix_mul_nary (n := ⟨n + 1, Nat.succ_pos n⟩) A₁ B₁)
      (FPM_Matrix_mul_nary (n := ⟨n + 1, Nat.succ_pos n⟩) A₂ B₂) := by
  let N : ℕ+ := ⟨n + 1, Nat.succ_pos n⟩
  exact FPM_Matrix_mul_nary_Substitution_ofEq
    (ctx := ctx) (C := C) (n := N) A₁ A₂ B₁ B₂
    (by
      intro i k
      simpa [N, shift_context_matrix_mul_nary] using hA i k)
    (by
      intro k j
      simpa [N, shift_context_matrix_mul_nary] using hB k j)
    hA_bd hB_bd

example (ctx : _root_.Context) (C : ℕ+) {m n p : ℕ}
    (A₁ A₂ : FPM_Matrix m (n + 1))
    (B₁ B₂ : FPM_Matrix (n + 1) p)
    (hA : ∀ i : Fin m, ∀ k : Fin (n + 1),
      FPM_Eq (shift_context_matrix_mul_nary ctx C ⟨n + 1, Nat.succ_pos n⟩) (A₁ i k) (A₂ i k))
    (hB : ∀ k : Fin (n + 1), ∀ j : Fin p,
      FPM_Eq (shift_context_matrix_mul_nary ctx C ⟨n + 1, Nat.succ_pos n⟩) (B₁ k j) (B₂ k j))
    (hA_bd : FPM_Matrix_Bounded A₁ C)
    (hB_bd : FPM_Matrix_Bounded B₂ C) :
    FPM_Matrix_Eq ctx
      (FPM_Matrix_mul_nary (n := ⟨n + 1, Nat.succ_pos n⟩) A₁ B₁)
      (FPM_Matrix_mul_nary (n := ⟨n + 1, Nat.succ_pos n⟩) A₂ B₂) := by
  let N : ℕ+ := ⟨n + 1, Nat.succ_pos n⟩
  exact FPM_Matrix_mul_nary_Substitution_ofEq
    (ctx := ctx) (C := C) (n := N) A₁ A₂ B₁ B₂
    (by
      intro i k
      simpa [N, shift_context_matrix_mul_nary] using hA i k)
    (by
      intro k j
      simpa [N, shift_context_matrix_mul_nary] using hB k j)
    hA_bd hB_bd


/- Tensor contraction ----------------------------------------------- -/

example (ctx : _root_.Context) (C : ℕ+) {i j k l m : ℕ}
    (T₁ T₂ : FPM_Tensor3 i j (k + 1))
    (S₁ S₂ : FPM_Tensor3 (k + 1) l m)
    (hT : ∀ a : Fin i, ∀ b : Fin j, ∀ c : Fin (k + 1),
      FPM_Eq (shift_context_tensor3_contract_nary ctx C ⟨k + 1, Nat.succ_pos k⟩)
        (T₁ a b c) (T₂ a b c))
    (hS : ∀ c : Fin (k + 1), ∀ d : Fin l, ∀ e : Fin m,
      FPM_Eq (shift_context_tensor3_contract_nary ctx C ⟨k + 1, Nat.succ_pos k⟩)
        (S₁ c d e) (S₂ c d e))
    (hT_bd : FPM_Tensor3_Bounded T₁ C)
    (hS_bd : FPM_Tensor3_Bounded S₂ C) :
    FPM_Tensor4_Eq ctx
      (FPM_Tensor3_contract_nary (k := ⟨k + 1, Nat.succ_pos k⟩) T₁ S₁)
      (FPM_Tensor3_contract_nary (k := ⟨k + 1, Nat.succ_pos k⟩) T₂ S₂) := by
  let K : ℕ+ := ⟨k + 1, Nat.succ_pos k⟩
  exact FPM_Tensor3_contract_nary_Substitution_ofEq
    (ctx := ctx) (C := C) (k := K) T₁ T₂ S₁ S₂
    (by
      intro a b c
      simpa [K, shift_context_tensor3_contract_nary] using hT a b c)
    (by
      intro c d e
      simpa [K, shift_context_tensor3_contract_nary] using hS c d e)
    hT_bd hS_bd

example (ctx : _root_.Context) (C : ℕ+) {i j k l m : ℕ}
    (T₁ T₂ : FPM_Tensor3 i j (k + 1))
    (S₁ S₂ : FPM_Tensor3 (k + 1) l m)
    (hT : ∀ a : Fin i, ∀ b : Fin j, ∀ c : Fin (k + 1),
      FPM_Eq (shift_context_tensor3_contract_nary ctx C ⟨k + 1, Nat.succ_pos k⟩)
        (T₁ a b c) (T₂ a b c))
    (hS : ∀ c : Fin (k + 1), ∀ d : Fin l, ∀ e : Fin m,
      FPM_Eq (shift_context_tensor3_contract_nary ctx C ⟨k + 1, Nat.succ_pos k⟩)
        (S₁ c d e) (S₂ c d e))
    (hT_bd : FPM_Tensor3_Bounded T₁ C)
    (hS_bd : FPM_Tensor3_Bounded S₂ C) :
    FPM_Tensor4_Eq ctx
      (FPM_Tensor3_contract_nary (k := ⟨k + 1, Nat.succ_pos k⟩) T₁ S₁)
      (FPM_Tensor3_contract_nary (k := ⟨k + 1, Nat.succ_pos k⟩) T₂ S₂) := by
  let K : ℕ+ := ⟨k + 1, Nat.succ_pos k⟩
  exact FPM_Tensor3_contract_nary_Substitution_ofEq
    (ctx := ctx) (C := C) (k := K) T₁ T₂ S₁ S₂
    (by
      intro a b c
      simpa [K, shift_context_tensor3_contract_nary] using hT a b c)
    (by
      intro c d e
      simpa [K, shift_context_tensor3_contract_nary] using hS c d e)
    hT_bd hS_bd


/- Row/column helpers ----------------------------------------------- -/

example (ctx : _root_.Context) {m n : ℕ}
    (A B : FPM_Matrix m n)
    (h : FPM_Matrix_Eq ctx A B)
    (i : Fin m) :
    FPM_Vector_Eq ctx (FPM_Matrix_row m n A i) (FPM_Matrix_row m n B i) := by
  exact FPM_Matrix_row_Eq_of_Matrix_Eq ctx A B h i

example (ctx : _root_.Context) {m n : ℕ}
    (A B : FPM_Matrix m n)
    (h : FPM_Matrix_Eq ctx A B)
    (j : Fin n) :
    FPM_Vector_Eq ctx (FPM_Matrix_col m n A j) (FPM_Matrix_col m n B j) := by
  exact FPM_Matrix_col_Eq_of_Matrix_Eq ctx A B h j

end

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

noncomputable section
/- ========================================================================
  # Phase 6: Topology
   SECTION 1: BASIC LOCAL WINDOW OBJECTS

   We begin with finite-dimensional local data in the most conservative form:
   a componentwise bounded window around a chosen center.

   This stays fully aligned with the existing Phase 6 linear interface:
   - vectors, matrices, and tensors are finite families of `FPM_Real`,
   - locality is recorded componentwise,
   - scalar "difference" is written as `a + (-b)`,
   - no abstract topological-space layer is introduced yet.
   ======================================================================== -/

/-- Componentwise bounded window around a vector center. -/
def FPM_Vector_Window {n : ℕ}
    (x : FPM_Vector n) (C : ℕ+) (v : FPM_Vector n) : Prop :=
  ∀ i : Fin n, FPM_Bounded (v i + (-(x i))) C

/-- Componentwise bounded window around a matrix center. -/
def FPM_Matrix_Window {m n : ℕ}
    (X : FPM_Matrix m n) (C : ℕ+) (A : FPM_Matrix m n) : Prop :=
  ∀ i : Fin m, ∀ j : Fin n, FPM_Bounded (A i j + (-(X i j))) C

/-- Componentwise bounded window around a 3-tensor center. -/
def FPM_Tensor3_Window {i j k : ℕ}
    (T0 : FPM_Tensor3 i j k) (C : ℕ+) (T : FPM_Tensor3 i j k) : Prop :=
  ∀ a : Fin i, ∀ b : Fin j, ∀ c : Fin k,
    FPM_Bounded (T a b c + (-(T0 a b c))) C

/-- Componentwise bounded window around a 4-tensor center. -/
def FPM_Tensor4_Window {i j k l : ℕ}
    (T0 : FPM_Tensor4 i j k l) (C : ℕ+) (T : FPM_Tensor4 i j k l) : Prop :=
  ∀ a : Fin i, ∀ b : Fin j, ∀ c : Fin k, ∀ d : Fin l,
    FPM_Bounded (T a b c d + (-(T0 a b c d))) C

/-
  Basic projection lemmas.
-/

@[simp] theorem FPM_Vector_Window_app
    {n : ℕ}
    {x v : FPM_Vector n} {C : ℕ+}
    (h : FPM_Vector_Window x C v) (i : Fin n) :
    FPM_Bounded (v i + (-(x i))) C :=
  h i

@[simp] theorem FPM_Matrix_Window_app
    {m n : ℕ}
    {X A : FPM_Matrix m n} {C : ℕ+}
    (h : FPM_Matrix_Window X C A) (i : Fin m) (j : Fin n) :
    FPM_Bounded (A i j + (-(X i j))) C :=
  h i j

@[simp] theorem FPM_Tensor3_Window_app
    {i j k : ℕ}
    {T0 T : FPM_Tensor3 i j k} {C : ℕ+}
    (h : FPM_Tensor3_Window T0 C T)
    (a : Fin i) (b : Fin j) (c : Fin k) :
    FPM_Bounded (T a b c + (-(T0 a b c))) C :=
  h a b c

@[simp] theorem FPM_Tensor4_Window_app
    {i j k l : ℕ}
    {T0 T : FPM_Tensor4 i j k l} {C : ℕ+}
    (h : FPM_Tensor4_Window T0 C T)
    (a : Fin i) (b : Fin j) (c : Fin k) (d : Fin l) :
    FPM_Bounded (T a b c d + (-(T0 a b c d))) C :=
  h a b c d

/-
  Constructor lemmas.
-/

theorem FPM_Vector_Window_mk
    {n : ℕ}
    {x v : FPM_Vector n} {C : ℕ+}
    (h : ∀ i : Fin n, FPM_Bounded (v i + (-(x i))) C) :
    FPM_Vector_Window x C v := by
  intro i
  exact h i

theorem FPM_Matrix_Window_mk
    {m n : ℕ}
    {X A : FPM_Matrix m n} {C : ℕ+}
    (h : ∀ i : Fin m, ∀ j : Fin n, FPM_Bounded (A i j + (-(X i j))) C) :
    FPM_Matrix_Window X C A := by
  intro i j
  exact h i j

theorem FPM_Tensor3_Window_mk
    {i j k : ℕ}
    {T0 T : FPM_Tensor3 i j k} {C : ℕ+}
    (h : ∀ a : Fin i, ∀ b : Fin j, ∀ c : Fin k,
      FPM_Bounded (T a b c + (-(T0 a b c))) C) :
    FPM_Tensor3_Window T0 C T := by
  intro a b c
  exact h a b c

theorem FPM_Tensor4_Window_mk
    {i j k l : ℕ}
    {T0 T : FPM_Tensor4 i j k l} {C : ℕ+}
    (h : ∀ a : Fin i, ∀ b : Fin j, ∀ c : Fin k, ∀ d : Fin l,
      FPM_Bounded (T a b c d + (-(T0 a b c d))) C) :
    FPM_Tensor4_Window T0 C T := by
  intro a b c d
  exact h a b c d

/- ========================================================================
   SECTION 2: MATRIX ROW/COLUMN LOCAL WINDOWS

   These lemmas reduce matrix-locality statements to vector-locality
   statements on rows and columns.
   ======================================================================== -/

/-- The local window on the `i`th row induced by a matrix center. -/
def FPM_Matrix_row_Window {m n : ℕ}
    (X : FPM_Matrix m n) (C : ℕ+) (i : Fin m) (v : FPM_Vector n) : Prop :=
  FPM_Vector_Window (FPM_Matrix_row m n X i) C v

def FPM_Matrix_col_Window {m n : ℕ}
    (X : FPM_Matrix m n) (C : ℕ+) (j : Fin n) (v : FPM_Vector m) : Prop :=
  FPM_Vector_Window (FPM_Matrix_col m n X j) C v

/-
  Basic projection lemmas.
-/

@[simp] theorem FPM_Matrix_row_Window_app
    {m n : ℕ}
    {X : FPM_Matrix m n} {C : ℕ+} {i : Fin m}
    {v : FPM_Vector n}
    (h : FPM_Matrix_row_Window X C i v) (j : Fin n) :
    FPM_Bounded (v j + (-(FPM_Matrix_row m n X i j))) C :=
  h j

@[simp] theorem FPM_Matrix_col_Window_app
    {m n : ℕ}
    {X : FPM_Matrix m n} {C : ℕ+} {j : Fin n}
    {v : FPM_Vector m}
    (h : FPM_Matrix_col_Window X C j v) (i : Fin m) :
    FPM_Bounded (v i + (-(FPM_Matrix_col m n X j i))) C :=
  h i

/-
  Constructor lemmas.
-/

theorem FPM_Matrix_row_Window_mk
    {m n : ℕ}
    {X : FPM_Matrix m n} {C : ℕ+} {i : Fin m}
    {v : FPM_Vector n}
    (h : ∀ j : Fin n, FPM_Bounded (v j + (-(FPM_Matrix_row m n X i j))) C) :
    FPM_Matrix_row_Window X C i v := by
  intro j
  exact h j

theorem FPM_Matrix_col_Window_mk
    {m n : ℕ}
    {X : FPM_Matrix m n} {C : ℕ+} {j : Fin n}
    {v : FPM_Vector m}
    (h : ∀ i : Fin m, FPM_Bounded (v i + (-(FPM_Matrix_col m n X j i))) C) :
    FPM_Matrix_col_Window X C j v := by
  intro i
  exact h i

/-
  Matrix-window to row/column-window reductions.
-/

theorem FPM_Matrix_row_Window_of_Matrix_Window
    {m n : ℕ}
    {X A : FPM_Matrix m n} {C : ℕ+}
    (h : FPM_Matrix_Window X C A) (i : Fin m) :
    FPM_Matrix_row_Window X C i (FPM_Matrix_row m n A i) := by
  intro j
  simpa [FPM_Matrix_row, FPM_Vector_Window] using h i j

theorem FPM_Matrix_col_Window_of_Matrix_Window
    {m n : ℕ}
    {X A : FPM_Matrix m n} {C : ℕ+}
    (h : FPM_Matrix_Window X C A) (j : Fin n) :
    FPM_Matrix_col_Window X C j (FPM_Matrix_col m n A j) := by
  intro i
  simpa [FPM_Matrix_col, FPM_Vector_Window] using h i j

/- ========================================================================
   SECTION 3: WINDOWS AS BOUNDED DIFFERENCES

   These lemmas repackage local-window membership as ordinary componentwise
   boundedness of the corresponding subtraction object.
   ======================================================================== -/

theorem FPM_Vector_Window_iff_sub_bounded
    {n : ℕ}
    {x v : FPM_Vector n} {C : ℕ+} :
    FPM_Vector_Window x C v ↔ FPM_Vector_Bounded (v - x) C := by
  constructor
  · intro h i
    simpa using h i
  · intro h i
    simpa using h i

theorem FPM_Matrix_Window_iff_sub_bounded
    {m n : ℕ}
    {X A : FPM_Matrix m n} {C : ℕ+} :
    FPM_Matrix_Window X C A ↔ FPM_Matrix_Bounded (A - X) C := by
  constructor
  · intro h i j
    simpa using h i j
  · intro h i j
    simpa using h i j

theorem FPM_Tensor3_Window_iff_sub_bounded
    {i j k : ℕ}
    {T0 T : FPM_Tensor3 i j k} {C : ℕ+} :
    FPM_Tensor3_Window T0 C T ↔ FPM_Tensor3_Bounded (T - T0) C := by
  constructor
  · intro h a b c
    simpa using h a b c
  · intro h a b c
    simpa using h a b c

theorem FPM_Tensor4_Window_iff_sub_bounded
    {i j k l : ℕ}
    {T0 T : FPM_Tensor4 i j k l} {C : ℕ+} :
    FPM_Tensor4_Window T0 C T ↔ FPM_Tensor4_Bounded (T - T0) C := by
  constructor
  · intro h a b c d
    simpa using h a b c d
  · intro h a b c d
    simpa using h a b c d

/-
  Row/column reformulations.
-/

theorem FPM_Matrix_row_Window_iff_sub_bounded
    {m n : ℕ}
    {X : FPM_Matrix m n} {C : ℕ+} {i : Fin m}
    {v : FPM_Vector n} :
    FPM_Matrix_row_Window X C i v ↔
      FPM_Vector_Bounded (v - FPM_Matrix_row m n X i) C := by
  constructor
  · intro h j
    simpa using h j
  · intro h j
    simpa using h j

theorem FPM_Matrix_col_Window_iff_sub_bounded
    {m n : ℕ}
    {X : FPM_Matrix m n} {C : ℕ+} {j : Fin n}
    {v : FPM_Vector m} :
    FPM_Matrix_col_Window X C j v ↔
      FPM_Vector_Bounded (v - FPM_Matrix_col m n X j) C := by
  constructor
  · intro h i
    simpa using h i
  · intro h i
    simpa using h i

/- ========================================================================
   SECTION 6: ROW/COLUMN BOUNDEDNESS UNDER NEGATION

   These are small matrix-facing corollaries built from:
   - `FPM_Matrix_row_Bounded_of_Matrix_Bounded`
   - `FPM_Matrix_col_Bounded_of_Matrix_Bounded`
   - `FPM_Vector_Bounded_neg`
   ======================================================================== -/

theorem FPM_Matrix_row_Bounded_neg_of_Matrix_Bounded
    {m n : ℕ} {A : FPM_Matrix m n} {C : ℕ+}
    (hA : FPM_Matrix_Bounded A C)
    (i : Fin m) :
    FPM_Vector_Bounded (-(FPM_Matrix_row m n A i)) C := by
  exact FPM_Vector_Bounded_neg
    (FPM_Matrix_row_Bounded_of_Matrix_Bounded A C hA i)


theorem FPM_Matrix_col_Bounded_neg_of_Matrix_Bounded
    {m n : ℕ} {A : FPM_Matrix m n} {C : ℕ+}
    (j : Fin n)
    (hA : FPM_Matrix_Bounded A C) :
    FPM_Vector_Bounded (-(FPM_Matrix_col m n A j)) C := by
  exact FPM_Vector_Bounded_neg
    (FPM_Matrix_col_Bounded_of_Matrix_Bounded A C hA j)


theorem FPM_Matrix_neg_row_Bounded
    {m n : ℕ}
    {A : FPM_Matrix m n} {C : ℕ+}
    (hA : FPM_Matrix_Bounded A C)
    (i : Fin m) :
    FPM_Vector_Bounded (FPM_Matrix_row m n (-A) i) C := by
  simpa [FPM_Matrix_row, FPM_Vector_neg_apply] using
    (FPM_Matrix_row_Bounded_neg_of_Matrix_Bounded hA i)

theorem FPM_Matrix_neg_col_Bounded
    {m n : ℕ}
    {A : FPM_Matrix m n} {C : ℕ+}
    (hA : FPM_Matrix_Bounded A C)
    (j : Fin n) :
    FPM_Vector_Bounded (FPM_Matrix_col m n (-A) j) C := by
  simpa [FPM_Matrix_col, FPM_Vector_neg_apply] using
    (FPM_Matrix_col_Bounded_neg_of_Matrix_Bounded j hA)

/- ========================================================================
   SECTION 7: ROW/COLUMN DIFFERENCE PACKAGING

   These lemmas package matrix-window membership into directly usable
   boundedness statements for row and column differences, and conversely
   rebuild row/column windows from those boundedness statements.
   ======================================================================== -/

theorem FPM_Matrix_row_sub_Bounded_of_Matrix_Window
    {m n : ℕ}
    {X A : FPM_Matrix m n} {C : ℕ+}
    (h : FPM_Matrix_Window X C A) (i : Fin m) :
    FPM_Vector_Bounded (FPM_Matrix_row m n A i - FPM_Matrix_row m n X i) C := by
  exact
    (FPM_Matrix_row_Window_iff_sub_bounded).1
      (FPM_Matrix_row_Window_of_Matrix_Window h i)


theorem FPM_Matrix_col_sub_Bounded_of_Matrix_Window
    {m n : ℕ}
    {X A : FPM_Matrix m n} {C : ℕ+}
    (h : FPM_Matrix_Window X C A) (j : Fin n) :
    FPM_Vector_Bounded (FPM_Matrix_col m n A j - FPM_Matrix_col m n X j) C := by
  exact
    (FPM_Matrix_col_Window_iff_sub_bounded).1
      (FPM_Matrix_col_Window_of_Matrix_Window h j)


theorem FPM_Matrix_row_Window_of_row_sub_Bounded
    {m n : ℕ}
    {X : FPM_Matrix m n} {C : ℕ+} {i : Fin m}
    {v : FPM_Vector n}
    (h : FPM_Vector_Bounded (v - FPM_Matrix_row m n X i) C) :
    FPM_Matrix_row_Window X C i v := by
  exact
    (FPM_Matrix_row_Window_iff_sub_bounded).2 h


theorem FPM_Matrix_col_Window_of_col_sub_Bounded
    {m n : ℕ}
    {X : FPM_Matrix m n} {C : ℕ+} {j : Fin n}
    {v : FPM_Vector m}
    (h : FPM_Vector_Bounded (v - FPM_Matrix_col m n X j) C) :
    FPM_Matrix_col_Window X C j v := by
  exact
    (FPM_Matrix_col_Window_iff_sub_bounded).2 h

/-
========================================================================
   SECTION 8: WINDOWS UNDER NEGATION

   Negating both the center and the point preserves window membership.
   This is the local-window analogue of boundedness stability under negation.
   ========================================================================

For each component i, we need FPM_Bounded ((-v) i + (-((-x) i))) C. This equals
FPM_Bounded (-(v i) + (-( -(x i)))) C. Since (v i + (-(x i))) is bounded
by C (from h), and -(v i) + (-(-(x i))) has the same seq values
as -(v i + (-(x i))) (by ring on each term), the result follows from FPM_Bounded_neg
applied to h i, and then converting the seq-pointwise equality.
-/
theorem FPM_Vector_Window_neg
    {n : ℕ}
    {x v : FPM_Vector n} {C : ℕ+}
    (h : FPM_Vector_Window x C v) :
    FPM_Vector_Window (-x) C (-v) := by
  rw [FPM_Vector_Window_iff_sub_bounded] at h ⊢
  exact FPM_Vector_Bounded_neg_sub h

/-
Same pattern as FPM_Vector_Window_neg but for matrices. For each (i,j), get the
bound from h, apply FPM_Bounded_neg, then show the seq values match by ring/grind.
-/
theorem FPM_Matrix_Window_neg
    {m n : ℕ}
    {X A : FPM_Matrix m n} {C : ℕ+}
    (h : FPM_Matrix_Window X C A) :
    FPM_Matrix_Window (-X) C (-A) := by
  rw [FPM_Matrix_Window_iff_sub_bounded] at h ⊢
  exact FPM_Matrix_Bounded_neg_sub h

/-
Same pattern. For each (a,b,c), get bound from h, apply FPM_Bounded_neg, show seq
values match.
-/
theorem FPM_Tensor3_Window_neg
    {i j k : ℕ}
    {T0 T : FPM_Tensor3 i j k} {C : ℕ+}
    (h : FPM_Tensor3_Window T0 C T) :
    FPM_Tensor3_Window (-T0) C (-T) := by
  rw [FPM_Tensor3_Window_iff_sub_bounded] at h ⊢
  exact FPM_Tensor3_Bounded_neg_sub h

/-
Follow the exact same proof pattern as FPM_Tensor3_Window_neg which was proved above.
Get the bound habcd from h, apply FPM_Bounded_neg, show seq values match
using simp and ring, then conclude.
-/
theorem FPM_Tensor4_Window_neg
    {i j k l : ℕ}
    {T0 T : FPM_Tensor4 i j k l} {C : ℕ+}
    (h : FPM_Tensor4_Window T0 C T) :
    FPM_Tensor4_Window (-T0) C (-T) := by
  rw [FPM_Tensor4_Window_iff_sub_bounded] at h ⊢
  exact FPM_Tensor4_Bounded_neg_sub h

theorem FPM_Matrix_row_Window_neg
    {m n : ℕ}
    {X : FPM_Matrix m n} {C : ℕ+} {i : Fin m}
    {v : FPM_Vector n}
    (h : FPM_Matrix_row_Window X C i v) :
    FPM_Matrix_row_Window (-X) C i (-v) := by
  exact FPM_Vector_Window_neg h


theorem FPM_Matrix_col_Window_neg
    {m n : ℕ}
    {X : FPM_Matrix m n} {C : ℕ+} {j : Fin n}
    {v : FPM_Vector m}
    (h : FPM_Matrix_col_Window X C j v) :
    FPM_Matrix_col_Window (-X) C j (-v) := by
  unfold FPM_Matrix_col_Window at h ⊢
  simpa [FPM_Matrix_col, FPM_Vector_neg_apply] using
    (FPM_Vector_Window_neg h)

/- ========================================================================
   SECTION 9: CONTEXTUAL SHEAFS OVER LOCAL WINDOWS

   We now place a chart / transition / local-field layer on top of the
   finite-dimensional window API developed above.

   Design:
   - a local chart is just a center plus a window radius,
   - membership is local-window membership,
   - a chart transition carries both:
       * window transport,
       * contextual equality transport with precision-loss factor `K`,
   - a chart section is a local field defined on one chart,
   - overlap means contextual agreement after transport along a transition.
   ======================================================================== -/

/-- A local chart is a chosen center together with a local window radius. -/
structure FPM_LocalChart (n : ℕ) where
  center : FPM_Vector n
  C : ℕ+

/-- Membership in a local chart is membership in the corresponding vector window. -/
def FPM_LocalChart.Mem {n : ℕ}
    (U : FPM_LocalChart n) (x : FPM_Vector n) : Prop :=
  FPM_Vector_Window U.center U.C x

@[simp] theorem FPM_LocalChart.mem_def
    {n : ℕ} (U : FPM_LocalChart n) (x : FPM_Vector n) :
    U.Mem x = FPM_Vector_Window U.center U.C x := rfl

/-- A local scalar field on a finite-dimensional chart domain. -/
abbrev FPM_LocalField (n : ℕ) := FPM_Vector n → FPM_Real

/-- A chart together with its local scalar field. -/
structure FPM_ChartSection (n : ℕ) where
  chart : FPM_LocalChart n
  field : FPM_LocalField n

/--
A chart transition from `U` to `V`.

`K` records the precision-loss factor for transporting contextual equality.
-/
structure FPM_ChartTransition (n : ℕ)
    (U V : FPM_LocalChart n) where
  trans : FPM_Vector n → FPM_Vector n
  K : ℕ+
  map_mem :
    ∀ {x : FPM_Vector n}, U.Mem x → V.Mem (trans x)
  transport :
    ∀ (ctx : _root_.Context) {x y : FPM_Vector n},
      FPM_Vector_Eq ctx x y →
      FPM_Vector_Eq { M := ctx.M * K, N := ctx.N }
        (trans x) (trans y)

@[simp] theorem FPM_ChartTransition.map_mem_app
    {n : ℕ} {U V : FPM_LocalChart n}
    (T : FPM_ChartTransition n U V)
    {x : FPM_Vector n} (hx : U.Mem x) :
    V.Mem (T.trans x) :=
  T.map_mem hx

@[simp] theorem FPM_ChartTransition.transport_app
    {n : ℕ} {U V : FPM_LocalChart n}
    (T : FPM_ChartTransition n U V)
    (ctx : _root_.Context) {x y : FPM_Vector n}
    (h : FPM_Vector_Eq ctx x y) :
    FPM_Vector_Eq { M := ctx.M * T.K, N := ctx.N }
      (T.trans x) (T.trans y) :=
  T.transport ctx h

/-- Identity transition on a chart. -/
def FPM_ChartTransition.id
    {n : ℕ} (U : FPM_LocalChart n) :
    FPM_ChartTransition n U U where
  trans := fun x => x
  K := (1 : ℕ+)
  map_mem := by
    intro x hx
    simpa using hx
  transport := by
    intro ctx x y h
    simpa using h

/--
Composition of chart transitions.

The precision-loss factors multiply.
-/
def FPM_ChartTransition.comp
    {n : ℕ}
    {U V W : FPM_LocalChart n}
    (TUV : FPM_ChartTransition n U V)
    (TVW : FPM_ChartTransition n V W) :
    FPM_ChartTransition n U W where
  trans := fun x => TVW.trans (TUV.trans x)
  K := TUV.K * TVW.K
  map_mem := by
    intro x hx
    exact TVW.map_mem (TUV.map_mem hx)
  transport := by
    intro ctx x y hxy
    have h₁ :
        FPM_Vector_Eq { M := ctx.M * TUV.K, N := ctx.N }
          (TUV.trans x) (TUV.trans y) :=
      TUV.transport ctx hxy
    have h₂ :
        FPM_Vector_Eq { M := (ctx.M * TUV.K) * TVW.K, N := ctx.N }
          (TVW.trans (TUV.trans x))
          (TVW.trans (TUV.trans y)) := by
      simpa using TVW.transport { M := ctx.M * TUV.K, N := ctx.N } h₁
    change
      FPM_Vector_Eq { M := ctx.M * (TUV.K * TVW.K), N := ctx.N }
        (TVW.trans (TUV.trans x))
        (TVW.trans (TUV.trans y))
    simpa [mul_assoc] using h₂

/--
Overlap agreement of two local sections across a chart transition.

Agreement is only required on the source chart window, and it lands in the
degraded context determined by the transition factor `K`.
-/
def FPM_Sheaf_Overlap
    {n : ℕ}
    (ctx : _root_.Context)
    (s₁ s₂ : FPM_ChartSection n)
    (T : FPM_ChartTransition n s₁.chart s₂.chart) : Prop :=
  ∀ ⦃x : FPM_Vector n⦄, s₁.chart.Mem x →
    FPM_Eq { M := ctx.M * T.K, N := ctx.N }
      (s₁.field x)
      (s₂.field (T.trans x))

@[simp] theorem FPM_Sheaf_Overlap_app
    {n : ℕ}
    {ctx : _root_.Context}
    {s₁ s₂ : FPM_ChartSection n}
    {T : FPM_ChartTransition n s₁.chart s₂.chart}
    (h : FPM_Sheaf_Overlap ctx s₁ s₂ T)
    {x : FPM_Vector n} (hx : s₁.chart.Mem x) :
    FPM_Eq { M := ctx.M * T.K, N := ctx.N }
      (s₁.field x)
      (s₂.field (T.trans x)) :=
  h hx

/-- Reflexive overlap via the identity transition. -/
theorem FPM_Sheaf_Overlap_refl
    {n : ℕ}
    (ctx : _root_.Context)
    (s : FPM_ChartSection n)
    (hfield :
      ∀ x : FPM_Vector n,
        FPM_Eq { M := ctx.M * (1 : ℕ+), N := ctx.N }
          (s.field x) (s.field x)) :
    FPM_Sheaf_Overlap ctx s s (FPM_ChartTransition.id s.chart) := by
  intro x hx
  simp only [FPM_ChartTransition.id]
  exact hfield x

/--
Weaken an overlap statement to a weaker ambient context.

This is the sheaf-level lift of `FPM_Eq_weaken`.
-/
theorem FPM_Sheaf_Overlap_weaken
    {n : ℕ}
    {ctx₁ ctx₂ : _root_.Context}
    {s₁ s₂ : FPM_ChartSection n}
    {T : FPM_ChartTransition n s₁.chart s₂.chart}
    (hM : ctx₁.M ≤ ctx₂.M)
    (hN : ctx₂.N ≤ ctx₁.N)
    (h : FPM_Sheaf_Overlap ctx₂ s₁ s₂ T) :
    FPM_Sheaf_Overlap ctx₁ s₁ s₂ T := by
  intro x hx
  have hx' :
      FPM_Eq { M := ctx₂.M * T.K, N := ctx₂.N }
        (s₁.field x)
        (s₂.field (T.trans x)) :=
    h hx
  refine FPM_Eq_weaken ?_ ?_ hx'
  ·
    change ctx₁.M * T.K ≤ ctx₂.M * T.K
    exact Nat.mul_le_mul_right _ hM
  ·
    simpa using hN

/--
A chart atlas with a chosen local section on every chart and a chosen
transition between every ordered pair of charts.
-/
structure FPM_SheafAtlas (ι : Type) (n : ℕ) where
  chart : ι → FPM_LocalChart n
  field : ι → FPM_LocalField n
  transition : ∀ i j : ι, FPM_ChartTransition n (chart i) (chart j)

/-- The `i`th section extracted from an atlas. -/
def FPM_SheafAtlas.Section
    {ι : Type} {n : ℕ}
    (A : FPM_SheafAtlas ι n) (i : ι) :
    FPM_ChartSection n where
  chart := A.chart i
  field := A.field i

@[simp] theorem FPM_SheafAtlas.Section_chart
    {ι : Type} {n : ℕ}
    (A : FPM_SheafAtlas ι n) (i : ι) :
    (A.Section i).chart = A.chart i := rfl

@[simp] theorem FPM_SheafAtlas.Section_field
    {ι : Type} {n : ℕ}
    (A : FPM_SheafAtlas ι n) (i : ι) :
    (A.Section i).field = A.field i := rfl

/-- Atlas compatibility means pairwise overlap compatibility everywhere. -/
def FPM_SheafAtlas.Compatible
    {ι : Type} {n : ℕ}
    (ctx : _root_.Context)
    (A : FPM_SheafAtlas ι n) : Prop :=
  ∀ i j : ι,
    FPM_Sheaf_Overlap ctx (A.Section i) (A.Section j) (A.transition i j)

@[simp] theorem FPM_SheafAtlas.compatible_app
    {ι : Type} {n : ℕ}
    {ctx : _root_.Context}
    {A : FPM_SheafAtlas ι n}
    (hA : A.Compatible ctx)
    (i j : ι) :
    FPM_Sheaf_Overlap ctx (A.Section i) (A.Section j) (A.transition i j) :=
  hA i j

/- ========================================================================
   SECTION 10: SMOKE TESTS

   These examples confirm that the local-window API is usable in its final
   public form:
   - windows can be converted to bounded differences,
   - bounded differences can rebuild windows,
   - matrix windows reduce to row/column windows,
   - negation preserves window membership.
   ======================================================================== -/


/- Vector windows -------------------------------------------------------- -/

example
    {n : ℕ}
    {x v : FPM_Vector n} {C : ℕ+}
    (h : FPM_Vector_Window x C v) :
    FPM_Vector_Bounded (v - x) C := by
  exact (FPM_Vector_Window_iff_sub_bounded).1 h


example
    {n : ℕ}
    {x v : FPM_Vector n} {C : ℕ+}
    (h : FPM_Vector_Bounded (v - x) C) :
    FPM_Vector_Window x C v := by
  exact (FPM_Vector_Window_iff_sub_bounded).2 h


example
    {n : ℕ}
    {x v : FPM_Vector n} {C : ℕ+}
    (h : FPM_Vector_Window x C v) :
    FPM_Vector_Window (-x) C (-v) := by
  exact FPM_Vector_Window_neg h


/- Matrix windows -------------------------------------------------------- -/

example
    {m n : ℕ}
    {X A : FPM_Matrix m n} {C : ℕ+}
    (h : FPM_Matrix_Window X C A) :
    FPM_Matrix_Bounded (A - X) C := by
  exact (FPM_Matrix_Window_iff_sub_bounded).1 h


example
    {m n : ℕ}
    {X A : FPM_Matrix m n} {C : ℕ+}
    (h : FPM_Matrix_Bounded (A - X) C) :
    FPM_Matrix_Window X C A := by
  exact (FPM_Matrix_Window_iff_sub_bounded).2 h


example
    {m n : ℕ}
    {X A : FPM_Matrix m n} {C : ℕ+}
    (h : FPM_Matrix_Window X C A) :
    FPM_Matrix_Window (-X) C (-A) := by
  exact FPM_Matrix_Window_neg h


/- Row/column reductions ------------------------------------------------- -/

example
    {m n : ℕ}
    {X A : FPM_Matrix m n} {C : ℕ+}
    (h : FPM_Matrix_Window X C A) (i : Fin m) :
    FPM_Matrix_row_Window X C i (FPM_Matrix_row m n A i) := by
  exact FPM_Matrix_row_Window_of_Matrix_Window h i


example
    {m n : ℕ}
    {X A : FPM_Matrix m n} {C : ℕ+}
    (h : FPM_Matrix_Window X C A) (j : Fin n) :
    FPM_Matrix_col_Window X C j (FPM_Matrix_col m n A j) := by
  exact FPM_Matrix_col_Window_of_Matrix_Window h j


example
    {m n : ℕ}
    {X A : FPM_Matrix m n} {C : ℕ+}
    (h : FPM_Matrix_Window X C A) (i : Fin m) :
    FPM_Vector_Bounded (FPM_Matrix_row m n A i - FPM_Matrix_row m n X i) C := by
  exact FPM_Matrix_row_sub_Bounded_of_Matrix_Window h i


example
    {m n : ℕ}
    {X A : FPM_Matrix m n} {C : ℕ+}
    (h : FPM_Matrix_Window X C A) (j : Fin n) :
    FPM_Vector_Bounded (FPM_Matrix_col m n A j - FPM_Matrix_col m n X j) C := by
  exact FPM_Matrix_col_sub_Bounded_of_Matrix_Window h j


example
    {m n : ℕ}
    {X : FPM_Matrix m n} {C : ℕ+} {i : Fin m}
    {v : FPM_Vector n}
    (h : FPM_Vector_Bounded (v - FPM_Matrix_row m n X i) C) :
    FPM_Matrix_row_Window X C i v := by
  exact FPM_Matrix_row_Window_of_row_sub_Bounded h


example
    {m n : ℕ}
    {X : FPM_Matrix m n} {C : ℕ+} {j : Fin n}
    {v : FPM_Vector m}
    (h : FPM_Vector_Bounded (v - FPM_Matrix_col m n X j) C) :
    FPM_Matrix_col_Window X C j v := by
  exact FPM_Matrix_col_Window_of_col_sub_Bounded h


example
    {m n : ℕ}
    {X : FPM_Matrix m n} {C : ℕ+} {i : Fin m}
    {v : FPM_Vector n}
    (h : FPM_Matrix_row_Window X C i v) :
    FPM_Matrix_row_Window (-X) C i (-v) := by
  exact FPM_Matrix_row_Window_neg h


example
    {m n : ℕ}
    {X : FPM_Matrix m n} {C : ℕ+} {j : Fin n}
    {v : FPM_Vector m}
    (h : FPM_Matrix_col_Window X C j v) :
    FPM_Matrix_col_Window (-X) C j (-v) := by
  exact FPM_Matrix_col_Window_neg h


/- Tensor windows -------------------------------------------------------- -/

example
    {i j k : ℕ}
    {T0 T : FPM_Tensor3 i j k} {C : ℕ+}
    (h : FPM_Tensor3_Window T0 C T) :
    FPM_Tensor3_Bounded (T - T0) C := by
  exact (FPM_Tensor3_Window_iff_sub_bounded).1 h


example
    {i j k : ℕ}
    {T0 T : FPM_Tensor3 i j k} {C : ℕ+}
    (h : FPM_Tensor3_Bounded (T - T0) C) :
    FPM_Tensor3_Window T0 C T := by
  exact (FPM_Tensor3_Window_iff_sub_bounded).2 h


example
    {i j k : ℕ}
    {T0 T : FPM_Tensor3 i j k} {C : ℕ+}
    (h : FPM_Tensor3_Window T0 C T) :
    FPM_Tensor3_Window (-T0) C (-T) := by
  exact FPM_Tensor3_Window_neg h


example
    {i j k l : ℕ}
    {T0 T : FPM_Tensor4 i j k l} {C : ℕ+}
    (h : FPM_Tensor4_Window T0 C T) :
    FPM_Tensor4_Bounded (T - T0) C := by
  exact (FPM_Tensor4_Window_iff_sub_bounded).1 h


example
    {i j k l : ℕ}
    {T0 T : FPM_Tensor4 i j k l} {C : ℕ+}
    (h : FPM_Tensor4_Bounded (T - T0) C) :
    FPM_Tensor4_Window T0 C T := by
  exact (FPM_Tensor4_Window_iff_sub_bounded).2 h


example
    {i j k l : ℕ}
    {T0 T : FPM_Tensor4 i j k l} {C : ℕ+}
    (h : FPM_Tensor4_Window T0 C T) :
    FPM_Tensor4_Window (-T0) C (-T) := by
  exact FPM_Tensor4_Window_neg h

-- contextual sheaves examples----------------------------------------------- -/
/- Chart membership ------------------------------------------------------ -/

example
    {n : ℕ}
    (U : FPM_LocalChart n)
    {x : FPM_Vector n}
    (hx : U.Mem x) :
    FPM_Vector_Window U.center U.C x := by
  simpa using hx

example
    {n : ℕ}
    (U : FPM_LocalChart n)
    {x : FPM_Vector n}
    (hx : FPM_Vector_Window U.center U.C x) :
    U.Mem x := by
  simpa using hx


/- Transition transport -------------------------------------------------- -/

example
    {n : ℕ}
    {U V : FPM_LocalChart n}
    (T : FPM_ChartTransition n U V)
    {x : FPM_Vector n}
    (hx : U.Mem x) :
    V.Mem (T.trans x) := by
  exact T.map_mem hx

example
    {n : ℕ}
    {U V : FPM_LocalChart n}
    (T : FPM_ChartTransition n U V)
    (ctx : _root_.Context)
    {x y : FPM_Vector n}
    (hxy : FPM_Vector_Eq ctx x y) :
    FPM_Vector_Eq { M := ctx.M * T.K, N := ctx.N }
      (T.trans x) (T.trans y) := by
  exact T.transport ctx hxy

example
    {n : ℕ}
    (U : FPM_LocalChart n)
    (ctx : _root_.Context)
    {x y : FPM_Vector n}
    (hxy : FPM_Vector_Eq ctx x y) :
    FPM_Vector_Eq { M := ctx.M * (1 : ℕ+), N := ctx.N }
      ((FPM_ChartTransition.id U).trans x)
      ((FPM_ChartTransition.id U).trans y) := by
  simp only [FPM_ChartTransition.id, mul_one]
  exact hxy

example
    {n : ℕ}
    {U V W : FPM_LocalChart n}
    (TUV : FPM_ChartTransition n U V)
    (TVW : FPM_ChartTransition n V W)
    {x : FPM_Vector n}
    (hx : U.Mem x) :
    W.Mem ((FPM_ChartTransition.comp TUV TVW).trans x) := by
  exact (FPM_ChartTransition.comp TUV TVW).map_mem hx


/- Overlap --------------------------------------------------------------- -/

example
    {n : ℕ}
    {ctx : _root_.Context}
    {s₁ s₂ : FPM_ChartSection n}
    {T : FPM_ChartTransition n s₁.chart s₂.chart}
    (h : FPM_Sheaf_Overlap ctx s₁ s₂ T)
    {x : FPM_Vector n}
    (hx : s₁.chart.Mem x) :
    FPM_Eq { M := ctx.M * T.K, N := ctx.N }
      (s₁.field x)
      (s₂.field (T.trans x)) := by
  exact h hx

example
    {n : ℕ}
    {ctx₁ ctx₂ : _root_.Context}
    {s₁ s₂ : FPM_ChartSection n}
    {T : FPM_ChartTransition n s₁.chart s₂.chart}
    (hM : ctx₁.M ≤ ctx₂.M)
    (hN : ctx₂.N ≤ ctx₁.N)
    (h : FPM_Sheaf_Overlap ctx₂ s₁ s₂ T) :
    FPM_Sheaf_Overlap ctx₁ s₁ s₂ T := by
  exact FPM_Sheaf_Overlap_weaken hM hN h


/- Atlas compatibility --------------------------------------------------- -/

example
    {ι : Type} {n : ℕ}
    (ctx : _root_.Context)
    (A : FPM_SheafAtlas ι n)
    (hA : A.Compatible ctx)
    (i j : ι) :
    FPM_Sheaf_Overlap ctx (A.Section i) (A.Section j) (A.transition i j) := by
  exact hA i j

example
    {ι : Type} {n : ℕ}
    (ctx : _root_.Context)
    (A : FPM_SheafAtlas ι n)
    (hA : A.Compatible ctx)
    (i j : ι)
    {x : FPM_Vector n}
    (hx : (A.chart i).Mem x) :
    FPM_Eq
      { M := ctx.M * (A.transition i j).K, N := ctx.N }
      ((A.field i) x)
      ((A.field j) ((A.transition i j).trans x)) := by
  exact (hA i j) hx

end

noncomputable section

section FPM_Phase7

/-
  ========================================================================
  PHASE 7: LOCAL FINITARY DYNAMICS
  SECTION 1: BASIC MODEL DATA
  We start with the smallest reliable layer:
  - parameters,
  - local state,
  - force / acceleration observables,
  - an energy core without the 1/2 factor yet.
  ========================================================================
-/

/-- Physical parameters for the first Phase 7 model.

    `mass_apart` is included so acceleration can use the certified inverse
    `FPM_Real_Inv_Apart` instead of the compatibility wrapper. -/
structure FPM_Phase7_Params where
  mass : FPM_Real
  spring : FPM_Real
  Cmass : ℕ+
  Cspring : ℕ+
  Lmass : ℕ+
  Nmass : ℕ+
  mass_bounded : FPM_Bounded mass Cmass
  spring_bounded : FPM_Bounded spring Cspring
  mass_apart : FPM_EventuallyApart mass Lmass Nmass

/-- Local oscillator-style state: position and velocity. -/
structure FPM_Phase7_State where
  pos : FPM_Real
  vel : FPM_Real

/-- Separate boundedness data for the two state coordinates. -/
def FPM_Phase7_State_Bounded
    (s : FPM_Phase7_State) (Cpos Cvel : ℕ+) : Prop :=
  FPM_Bounded s.pos Cpos ∧ FPM_Bounded s.vel Cvel

@[simp] theorem FPM_Phase7_State_Bounded_pos
    {s : FPM_Phase7_State} {Cpos Cvel : ℕ+}
    (h : FPM_Phase7_State_Bounded s Cpos Cvel) :
    FPM_Bounded s.pos Cpos :=
  h.1

@[simp] theorem FPM_Phase7_State_Bounded_vel
    {s : FPM_Phase7_State} {Cpos Cvel : ℕ+}
    (h : FPM_Phase7_State_Bounded s Cpos Cvel) :
    FPM_Bounded s.vel Cvel :=
  h.2

/-- Certified inverse mass, built from the explicit apartness witness. -/
noncomputable def FPM_Phase7_InvMass
    (p : FPM_Phase7_Params) : FPM_Real :=
  FPM_Real_Inv_Apart p.mass p.Lmass p.Nmass p.mass_apart

/-- Restoring force for the first model: `-k x`. -/
noncomputable def FPM_Phase7_Force
    (p : FPM_Phase7_Params) (s : FPM_Phase7_State) : FPM_Real :=
  -(p.spring * s.pos)

/-- Acceleration for the first model: `m⁻¹ * (-k x)`. -/
noncomputable def FPM_Phase7_Acceleration
    (p : FPM_Phase7_Params) (s : FPM_Phase7_State) : FPM_Real :=
  FPM_Phase7_InvMass p * FPM_Phase7_Force p s

/-- Kinetic part without the `1/2` factor yet. -/
noncomputable def FPM_Phase7_KineticCore
    (p : FPM_Phase7_Params) (s : FPM_Phase7_State) : FPM_Real :=
  p.mass * (s.vel * s.vel)

/-- Potential part without the `1/2` factor yet. -/
noncomputable def FPM_Phase7_PotentialCore
    (p : FPM_Phase7_Params) (s : FPM_Phase7_State) : FPM_Real :=
  p.spring * (s.pos * s.pos)

/-- Total energy core, postponing the `1/2` normalization until later. -/
noncomputable def FPM_Phase7_EnergyCore
    (p : FPM_Phase7_Params) (s : FPM_Phase7_State) : FPM_Real :=
  FPM_Phase7_KineticCore p s + FPM_Phase7_PotentialCore p s

@[simp] theorem FPM_Phase7_InvMass_seq
    (p : FPM_Phase7_Params) (n : ℕ+) :
    (FPM_Phase7_InvMass p).seq n = (p.mass.seq n)⁻¹ := by
  simpa [FPM_Phase7_InvMass] using
    FPM_Real_Inv_Apart_seq p.mass p.Lmass p.Nmass p.mass_apart n


@[simp] theorem FPM_Phase7_Acceleration_seq
    (p : FPM_Phase7_Params) (s : FPM_Phase7_State) (n : ℕ+) :
    (FPM_Phase7_Acceleration p s).seq n =
      ((p.mass.seq n)⁻¹) * ( -((p.spring.seq n) * (s.pos.seq n)) ) := by
  simp only [
    FPM_Phase7_Acceleration,
    FPM_Phase7_Force,
    FPM_Phase7_InvMass,
    FPM_mul_seq,
    FPM_neg_seq,
    FPM_Real_Inv_Apart_seq
  ]

@[simp] theorem FPM_Phase7_KineticCore_seq
    (p : FPM_Phase7_Params) (s : FPM_Phase7_State) (n : ℕ+) :
    (FPM_Phase7_KineticCore p s).seq n =
      (p.mass.seq n) * ((s.vel.seq n) * (s.vel.seq n)) := by
  simp [FPM_Phase7_KineticCore]

@[simp] theorem FPM_Phase7_PotentialCore_seq
    (p : FPM_Phase7_Params) (s : FPM_Phase7_State) (n : ℕ+) :
    (FPM_Phase7_PotentialCore p s).seq n =
      (p.spring.seq n) * ((s.pos.seq n) * (s.pos.seq n)) := by
  simp [FPM_Phase7_PotentialCore]

@[simp] theorem FPM_Phase7_EnergyCore_seq
    (p : FPM_Phase7_Params) (s : FPM_Phase7_State) (n : ℕ+) :
    (FPM_Phase7_EnergyCore p s).seq n =
      (p.mass.seq n) * ((s.vel.seq n) * (s.vel.seq n)) +
      (p.spring.seq n) * ((s.pos.seq n) * (s.pos.seq n)) := by
  simp [FPM_Phase7_EnergyCore, FPM_Phase7_KineticCore, FPM_Phase7_PotentialCore]

/-! SECTION 2: BASIC BOUNDEDNESS -/

/-- Local helper: boundedness of a product.  We keep this in Phase 7 so the
section does not depend on whether a global `FPM_Boundedmul` theorem has already
been named in the core file. -/
theorem FPM_Phase7_mul_bounded
    (a b : FPM_Real) {Ca Cb : ℕ+}
    (ha : FPM_Bounded a Ca) (hb : FPM_Bounded b Cb) :
    FPM_Bounded (a * b) (Ca * Cb) := by
  intro n
  rw [FPM_mul_seq, abs_mul]
  rw [show (↑↑(Ca * Cb) : ℚ) = ↑↑Ca * ↑↑Cb by norm_cast]
  exact mul_le_mul (ha n) (hb n) (by exact abs_nonneg _) (by positivity)

@[simp] theorem FPM_Phase7_Force_seq
    (p : FPM_Phase7_Params) (s : FPM_Phase7_State) (n : ℕ+) :
    (FPM_Phase7_Force p s).seq n =
      -((p.spring.seq n) * (s.pos.seq n)) := by
  simp only [FPM_Phase7_Force, FPM_mul_seq, FPM_neg_seq]

/-- Force is bounded whenever the spring constant and position are bounded. -/
theorem FPM_Phase7_Force_bounded
    (p : FPM_Phase7_Params) (s : FPM_Phase7_State)
    {K X : ℕ+}
    (hK : FPM_Bounded p.spring K)
    (hX : FPM_Bounded s.pos X) :
    FPM_Bounded (FPM_Phase7_Force p s) (K * X) := by
  simpa [FPM_Phase7_Force] using
    (FPM_Bounded_neg
      (a := p.spring * s.pos)
      (C := K * X)
      (FPM_Phase7_mul_bounded (a := p.spring) (b := s.pos) hK hX))

/-- Acceleration is bounded once inverse mass and force are bounded.  This keeps
the inverse guard explicit and avoids overcommitting before you choose the final
global bound strategy for `InvMass`. -/
theorem FPM_Phase7_Acceleration_bounded
    (p : FPM_Phase7_Params) (s : FPM_Phase7_State)
    {Cm Cf : ℕ+}
    (hm : FPM_Bounded (FPM_Phase7_InvMass p) Cm)
    (hf : FPM_Bounded (FPM_Phase7_Force p s) Cf) :
    FPM_Bounded (FPM_Phase7_Acceleration p s) (Cm * Cf) := by
  simpa [FPM_Phase7_Acceleration] using
    (FPM_Phase7_mul_bounded
      (a := FPM_Phase7_InvMass p)
      (b := FPM_Phase7_Force p s)
      hm hf)

/-- More convenient bundled version: if you already have a bound for inverse
mass, then spring and position bounds immediately give an acceleration bound. -/
theorem FPM_Phase7_Acceleration_bounded_of_bounds
    (p : FPM_Phase7_Params) (s : FPM_Phase7_State)
    {Cm K X : ℕ+}
    (hm : FPM_Bounded (FPM_Phase7_InvMass p) Cm)
    (hK : FPM_Bounded p.spring K)
    (hX : FPM_Bounded s.pos X) :
    FPM_Bounded (FPM_Phase7_Acceleration p s) (Cm * (K * X)) := by
  have hF : FPM_Bounded (FPM_Phase7_Force p s) (K * X) :=
    FPM_Phase7_Force_bounded p s hK hX
  simpa [mul_assoc] using
    (FPM_Phase7_Acceleration_bounded p s hm hF)

/-!
  ========================================================================
  SECTION 3: LINEAR-COST ENERGY PACKAGING
  We now repackage the energy observable through the native n-ary sum so that
  finite summation stays flat rather than recursively binary.
  ========================================================================
-/


/-- The two energy summands packaged as a finite family. Index `0` is kinetic,
index `1` is potential. -/
noncomputable def FPM_Phase7_EnergyTerms
    (p : FPM_Phase7_Params) (s : FPM_Phase7_State) :
    Fin 2 → FPM_Real
  | ⟨0, _⟩ => FPM_Phase7_KineticCore p s
  | ⟨1, _⟩ => FPM_Phase7_PotentialCore p s


@[simp] theorem FPM_Phase7_EnergyTerms_zero
    (p : FPM_Phase7_Params) (s : FPM_Phase7_State) :
    FPM_Phase7_EnergyTerms p s ⟨0, by decide⟩ =
      FPM_Phase7_KineticCore p s := by
  simp [FPM_Phase7_EnergyTerms]


@[simp] theorem FPM_Phase7_EnergyTerms_one
    (p : FPM_Phase7_Params) (s : FPM_Phase7_State) :
    FPM_Phase7_EnergyTerms p s ⟨1, by decide⟩ =
      FPM_Phase7_PotentialCore p s := by
  simp [FPM_Phase7_EnergyTerms]


/-- Public linear-cost energy observable: native n-ary sum of the two energy
terms. This is the canonical Phase 7 energy packaging. -/
noncomputable def FPM_Phase7_Energy
    (p : FPM_Phase7_Params) (s : FPM_Phase7_State) : FPM_Real :=
  FPM_sum_nary (n := 2) (FPM_Phase7_EnergyTerms p s)


@[simp] theorem FPM_Phase7_Energy_seq
    (p : FPM_Phase7_Params) (s : FPM_Phase7_State) (n : ℕ+) :
    (FPM_Phase7_Energy p s).seq n =
      (p.mass.seq n) * ((s.vel.seq n) * (s.vel.seq n)) +
      (p.spring.seq n) * ((s.pos.seq n) * (s.pos.seq n)) := by
  rw [FPM_Phase7_Energy, FPM_sum_nary_seq]
  simp only [FPM_Phase7_EnergyTerms]
  exact Fin.sum_univ_two
    (f := fun i : Fin 2 => (FPM_Phase7_EnergyTerms p s i).seq n)

/-- Sequence-level compatibility between the original binary energy core and the
linear-cost n-ary energy packaging. -/
@[simp] theorem FPM_Phase7_Energy_seq_eq_EnergyCore_seq
    (p : FPM_Phase7_Params) (s : FPM_Phase7_State) (n : ℕ+) :
    (FPM_Phase7_Energy p s).seq n =
      (FPM_Phase7_EnergyCore p s).seq n := by
  rw [FPM_Phase7_Energy_seq, FPM_Phase7_EnergyCore_seq]


/-- Explicit bounds assigned to the two energy terms. -/
def FPM_Phase7_EnergyBounds
    (Cmass Cspring Cpos Cvel : ℕ+) : Fin 2 → ℕ+
  | ⟨0, _⟩ => Cmass * (Cvel * Cvel)
  | ⟨1, _⟩ => Cspring * (Cpos * Cpos)


@[simp] theorem FPM_Phase7_EnergyBounds_zero
    (Cmass Cspring Cpos Cvel : ℕ+) :
    FPM_Phase7_EnergyBounds Cmass Cspring Cpos Cvel ⟨0, by decide⟩ =
      Cmass * (Cvel * Cvel) := by
  simp [FPM_Phase7_EnergyBounds]


@[simp] theorem FPM_Phase7_EnergyBounds_one
    (Cmass Cspring Cpos Cvel : ℕ+) :
    FPM_Phase7_EnergyBounds Cmass Cspring Cpos Cvel ⟨1, by decide⟩ =
      Cspring * (Cpos * Cpos) := by
  simp [FPM_Phase7_EnergyBounds]


/-- Kinetic core boundedness. -/
theorem FPM_Phase7_KineticCore_bounded
    (p : FPM_Phase7_Params) (s : FPM_Phase7_State)
    {Cm Cv : ℕ+}
    (hm : FPM_Bounded p.mass Cm)
    (hv : FPM_Bounded s.vel Cv) :
    FPM_Bounded (FPM_Phase7_KineticCore p s) (Cm * (Cv * Cv)) := by
  dsimp [FPM_Phase7_KineticCore]
  exact FPM_Phase7_mul_bounded
    (a := p.mass)
    (b := s.vel * s.vel)
    hm
    (FPM_Phase7_mul_bounded (a := s.vel) (b := s.vel) hv hv)


/-- Potential core boundedness. -/
theorem FPM_Phase7_PotentialCore_bounded
    (p : FPM_Phase7_Params) (s : FPM_Phase7_State)
    {Ck Cx : ℕ+}
    (hk : FPM_Bounded p.spring Ck)
    (hx : FPM_Bounded s.pos Cx) :
    FPM_Bounded (FPM_Phase7_PotentialCore p s) (Ck * (Cx * Cx)) := by
  dsimp [FPM_Phase7_PotentialCore]
  exact FPM_Phase7_mul_bounded
    (a := p.spring)
    (b := s.pos * s.pos)
    hk
    (FPM_Phase7_mul_bounded (a := s.pos) (b := s.pos) hx hx)


/-- Componentwise boundedness of the finite energy family. -/
theorem FPM_Phase7_EnergyTerms_bounded
    (p : FPM_Phase7_Params) (s : FPM_Phase7_State)
    {Cmass Cspring Cpos Cvel : ℕ+}
    (hm : FPM_Bounded p.mass Cmass)
    (hk : FPM_Bounded p.spring Cspring)
    (hx : FPM_Bounded s.pos Cpos)
    (hv : FPM_Bounded s.vel Cvel) :
    ∀ i : Fin 2,
      FPM_Bounded (FPM_Phase7_EnergyTerms p s i)
        (FPM_Phase7_EnergyBounds Cmass Cspring Cpos Cvel i) := by
  intro i
  fin_cases i
  · simpa [FPM_Phase7_EnergyTerms, FPM_Phase7_EnergyBounds] using
      (FPM_Phase7_KineticCore_bounded (p := p) (s := s) hm hv)
  · simpa [FPM_Phase7_EnergyTerms, FPM_Phase7_EnergyBounds] using
      (FPM_Phase7_PotentialCore_bounded (p := p) (s := s) hk hx)


/-- Linear-cost boundedness theorem for the packaged energy observable. -/
theorem FPM_Phase7_Energy_bounded
    (p : FPM_Phase7_Params) (s : FPM_Phase7_State)
    {Cmass Cspring Cpos Cvel : ℕ+}
    (hm : FPM_Bounded p.mass Cmass)
    (hk : FPM_Bounded p.spring Cspring)
    (hx : FPM_Bounded s.pos Cpos)
    (hv : FPM_Bounded s.vel Cvel) :
    FPM_Bounded (FPM_Phase7_Energy p s)
      (Cmass * (Cvel * Cvel) + Cspring * (Cpos * Cpos)) := by
  have hterms :
      ∀ i : Fin 2,
        FPM_Bounded (FPM_Phase7_EnergyTerms p s i)
          (FPM_Phase7_EnergyBounds Cmass Cspring Cpos Cvel i) :=
    FPM_Phase7_EnergyTerms_bounded (p := p) (s := s) hm hk hx hv
  simpa [FPM_Phase7_Energy, FPM_Phase7_EnergyBounds, Fin.sum_univ_two] using
    (FPM_Bounded_sum_nary_sigma
      (n := 2)
      (v := FPM_Phase7_EnergyTerms p s)
      (C := FPM_Phase7_EnergyBounds Cmass Cspring Cpos Cvel)
      hterms)

/-!
  ========================================================================
  SECTION 4: LOCAL TRANSPORT OF OBSERVABLES
  Phase-4/6 style:
  - prove square transport once,
  - reuse it for kinetic/potential transport,
  - package total energy through native n-ary transport.
  ========================================================================
-/


/-- Square transport, specialized for Phase 7 use. -/
theorem FPM_Phase7_sq_substitution
    (ctx : _root_.Context)
    (a a' : FPM_Real) {C : ℕ+}
    (ha : FPM_Bounded a C)
    (ha' : FPM_Bounded a' C)
    (hA : FPM_Eq (shift_context_mul ctx C) a a') :
    FPM_Eq ctx (a * a) (a' * a') := by
  exact FPM_Mul_Substitution_full
    (ctx := ctx) (C := C)
    (a₁ := a)  (a₂ := a')
    (b₁ := a)  (b₂ := a')
    ha ha' ha ha' hA hA


/-- Force transport: `-k x` is stable under local overlap. -/
theorem FPM_Phase7_Force_substitution
    (ctx : _root_.Context)
    (p p' : FPM_Phase7_Params) (s s' : FPM_Phase7_State)
    {C : ℕ+}
    (hk : FPM_Bounded p.spring C)
    (hk' : FPM_Bounded p'.spring C)
    (hx : FPM_Bounded s.pos C)
    (hx' : FPM_Bounded s'.pos C)
    (hK : FPM_Eq (shift_context_mul ctx C) p.spring p'.spring)
    (hX : FPM_Eq (shift_context_mul ctx C) s.pos s'.pos) :
    FPM_Eq ctx (FPM_Phase7_Force p s) (FPM_Phase7_Force p' s') := by
  have hmul :
      FPM_Eq ctx (p.spring * s.pos) (p'.spring * s'.pos) := by
    exact FPM_Mul_Substitution_full
      (ctx := ctx) (C := C)
      (a₁ := p.spring) (a₂ := p'.spring)
      (b₁ := s.pos)    (b₂ := s'.pos)
      hk hk' hx hx' hK hX
  have hmul_shift :
      FPM_Eq (shift_context_unary ctx FPM_Neg)
        (p.spring * s.pos) (p'.spring * s'.pos) := by
    simpa [shift_context_unary, FPM_Neg] using hmul
  simpa [FPM_Phase7_Force] using
    (FPM_Neg_Substitution
      (ctx := ctx)
      (a₁ := p.spring * s.pos)
      (a₂ := p'.spring * s'.pos)
      (hA := hmul_shift))


/-- Kinetic core transport: `m * v^2`. -/
theorem FPM_Phase7_KineticCore_substitution
    (ctx : _root_.Context)
    (p p' : FPM_Phase7_Params) (s s' : FPM_Phase7_State)
    {Cm Cv : ℕ+}
    (hm : FPM_Bounded p.mass Cm)
    (hm' : FPM_Bounded p'.mass Cm)
    (hv : FPM_Bounded s.vel Cv)
    (hv' : FPM_Bounded s'.vel Cv)
    (hM : FPM_Eq (shift_context_mul ctx (max Cm (Cv * Cv))) p.mass p'.mass)
    (hV : FPM_Eq (shift_context_mul (shift_context_mul ctx (max Cm (Cv * Cv))) Cv) s.vel s'.vel) :
    FPM_Eq ctx
      (FPM_Phase7_KineticCore p s)
      (FPM_Phase7_KineticCore p' s') := by
  have hvsq :
      FPM_Eq (shift_context_mul ctx (max Cm (Cv * Cv)))
        (s.vel * s.vel) (s'.vel * s'.vel) := by
    exact FPM_Phase7_sq_substitution
      (ctx := shift_context_mul ctx (max Cm (Cv * Cv)))
      (a := s.vel) (a' := s'.vel)
      (C := Cv) hv hv' hV
  have hvsq_bnd : FPM_Bounded (s.vel * s.vel) (Cv * Cv) :=
    FPM_Phase7_mul_bounded (a := s.vel) (b := s.vel) hv hv
  have hvsq'_bnd : FPM_Bounded (s'.vel * s'.vel) (Cv * Cv) :=
    FPM_Phase7_mul_bounded (a := s'.vel) (b := s'.vel) hv' hv'
  have hm_max : FPM_Bounded p.mass (max Cm (Cv * Cv)) := by
    intro n
    exact le_trans (hm n) (by
      change ((Cm : ℕ+) : ℚ) ≤ ((max Cm (Cv * Cv) : ℕ+) : ℚ)
      exact_mod_cast le_max_left Cm (Cv * Cv))
  have hm'_max : FPM_Bounded p'.mass (max Cm (Cv * Cv)) := by
    intro n
    exact le_trans (hm' n) (by
      change ((Cm : ℕ+) : ℚ) ≤ ((max Cm (Cv * Cv) : ℕ+) : ℚ)
      exact_mod_cast le_max_left Cm (Cv * Cv))
  have hvsq_max : FPM_Bounded (s.vel * s.vel) (max Cm (Cv * Cv)) := by
    intro n
    exact le_trans (hvsq_bnd n) (by
      change (((Cv * Cv : ℕ+) : ℕ) : ℚ) ≤ ((max Cm (Cv * Cv) : ℕ+) : ℚ)
      exact_mod_cast le_max_right Cm (Cv * Cv))
  have hvsq'_max : FPM_Bounded (s'.vel * s'.vel) (max Cm (Cv * Cv)) := by
    intro n
    exact le_trans (hvsq'_bnd n) (by
      change (((Cv * Cv : ℕ+) : ℕ) : ℚ) ≤ ((max Cm (Cv * Cv) : ℕ+) : ℚ)
      exact_mod_cast le_max_right Cm (Cv * Cv))
  simpa [FPM_Phase7_KineticCore] using
    (FPM_Mul_Substitution_full
      (ctx := ctx) (C := max Cm (Cv * Cv))
      (a₁ := p.mass)        (a₂ := p'.mass)
      (b₁ := s.vel * s.vel) (b₂ := s'.vel * s'.vel)
      hm_max hm'_max hvsq_max hvsq'_max hM hvsq)


/-- Potential core transport: `k * x^2`. -/
theorem FPM_Phase7_PotentialCore_substitution
    (ctx : _root_.Context)
    (p p' : FPM_Phase7_Params) (s s' : FPM_Phase7_State)
    {Ck Cx : ℕ+}
    (hk : FPM_Bounded p.spring Ck)
    (hk' : FPM_Bounded p'.spring Ck)
    (hx : FPM_Bounded s.pos Cx)
    (hx' : FPM_Bounded s'.pos Cx)
    (hK : FPM_Eq (shift_context_mul ctx (max Ck (Cx * Cx))) p.spring p'.spring)
    (hX : FPM_Eq (shift_context_mul (shift_context_mul ctx (max Ck (Cx * Cx))) Cx) s.pos s'.pos) :
    FPM_Eq ctx
      (FPM_Phase7_PotentialCore p s)
      (FPM_Phase7_PotentialCore p' s') := by
  have hxsq :
      FPM_Eq (shift_context_mul ctx (max Ck (Cx * Cx)))
        (s.pos * s.pos) (s'.pos * s'.pos) := by
    exact FPM_Phase7_sq_substitution
      (ctx := shift_context_mul ctx (max Ck (Cx * Cx)))
      (a := s.pos) (a' := s'.pos)
      (C := Cx) hx hx' hX
  have hxsq_bnd : FPM_Bounded (s.pos * s.pos) (Cx * Cx) :=
    FPM_Phase7_mul_bounded (a := s.pos) (b := s.pos) hx hx
  have hxsq'_bnd : FPM_Bounded (s'.pos * s'.pos) (Cx * Cx) :=
    FPM_Phase7_mul_bounded (a := s'.pos) (b := s'.pos) hx' hx'
  have hk_max : FPM_Bounded p.spring (max Ck (Cx * Cx)) := by
    intro n
    exact le_trans (hk n) (by
      change ((Ck : ℕ+) : ℚ) ≤ ((max Ck (Cx * Cx) : ℕ+) : ℚ)
      exact_mod_cast le_max_left Ck (Cx * Cx))
  have hk'_max : FPM_Bounded p'.spring (max Ck (Cx * Cx)) := by
    intro n
    exact le_trans (hk' n) (by
      change ((Ck : ℕ+) : ℚ) ≤ ((max Ck (Cx * Cx) : ℕ+) : ℚ)
      exact_mod_cast le_max_left Ck (Cx * Cx))
  have hxsq_max : FPM_Bounded (s.pos * s.pos) (max Ck (Cx * Cx)) := by
    intro n
    exact le_trans (hxsq_bnd n) (by
      change (((Cx * Cx : ℕ+) : ℕ) : ℚ) ≤ ((max Ck (Cx * Cx) : ℕ+) : ℚ)
      exact_mod_cast le_max_right Ck (Cx * Cx))
  have hxsq'_max : FPM_Bounded (s'.pos * s'.pos) (max Ck (Cx * Cx)) := by
    intro n
    exact le_trans (hxsq'_bnd n) (by
      change (((Cx * Cx : ℕ+) : ℕ) : ℚ) ≤ ((max Ck (Cx * Cx) : ℕ+) : ℚ)
      exact_mod_cast le_max_right Ck (Cx * Cx))
  simpa [FPM_Phase7_PotentialCore] using
    (FPM_Mul_Substitution_full
      (ctx := ctx) (C := max Ck (Cx * Cx))
      (a₁ := p.spring)      (a₂ := p'.spring)
      (b₁ := s.pos * s.pos) (b₂ := s'.pos * s'.pos)
      hk_max hk'_max hxsq_max hxsq'_max hK hxsq)


/-- Componentwise transport for the energy term family. -/
theorem FPM_Phase7_EnergyTerms_substitution
    (ctx : _root_.Context)
    (p p' : FPM_Phase7_Params) (s s' : FPM_Phase7_State)
    {Cm Ck Cx Cv : ℕ+}
    (hm : FPM_Bounded p.mass Cm)
    (hm' : FPM_Bounded p'.mass Cm)
    (hk : FPM_Bounded p.spring Ck)
    (hk' : FPM_Bounded p'.spring Ck)
    (hx : FPM_Bounded s.pos Cx)
    (hx' : FPM_Bounded s'.pos Cx)
    (hv : FPM_Bounded s.vel Cv)
    (hv' : FPM_Bounded s'.vel Cv)
    (hM : FPM_Eq (shift_context_mul ctx (max Cm (Cv * Cv))) p.mass p'.mass)
    (hK : FPM_Eq (shift_context_mul ctx (max Ck (Cx * Cx))) p.spring p'.spring)
    (hX : FPM_Eq (shift_context_mul (shift_context_mul ctx (max Ck (Cx * Cx))) Cx) s.pos s'.pos)
    (hV : FPM_Eq (shift_context_mul (shift_context_mul ctx (max Cm (Cv * Cv))) Cv) s.vel s'.vel) :
    ∀ i : Fin 2,
      FPM_Eq ctx
        (FPM_Phase7_EnergyTerms p s i)
        (FPM_Phase7_EnergyTerms p' s' i) := by
  intro i
  fin_cases i
  · simpa [FPM_Phase7_EnergyTerms] using
      (FPM_Phase7_KineticCore_substitution
        (ctx := ctx) (p := p) (p' := p') (s := s) (s' := s')
        hm hm' hv hv' hM hV)
  · simpa [FPM_Phase7_EnergyTerms] using
      (FPM_Phase7_PotentialCore_substitution
        (ctx := ctx) (p := p) (p' := p') (s := s) (s' := s')
        hk hk' hx hx' hK hX)

/-- Packaged energy transport through native linear-cost n-ary addition. -/
theorem FPM_Phase7_Energy_substitution
    (ctx : _root_.Context)
    (p p' : FPM_Phase7_Params) (s s' : FPM_Phase7_State)
    {Cm Ck Cx Cv : ℕ+}
    (hm : FPM_Bounded p.mass Cm)
    (hm' : FPM_Bounded p'.mass Cm)
    (hk : FPM_Bounded p.spring Ck)
    (hk' : FPM_Bounded p'.spring Ck)
    (hx : FPM_Bounded s.pos Cx)
    (hx' : FPM_Bounded s'.pos Cx)
    (hv : FPM_Bounded s.vel Cv)
    (hv' : FPM_Bounded s'.vel Cv)
    (hM : FPM_Eq
      (shift_context_mul
        (shift_context_nary ctx (2 : ℕ+) (FPM_AddNary 2))
        (max Cm (Cv * Cv)))
      p.mass p'.mass)
    (hK : FPM_Eq
      (shift_context_mul
        (shift_context_nary ctx (2 : ℕ+) (FPM_AddNary 2))
        (max Ck (Cx * Cx)))
      p.spring p'.spring)
    (hX : FPM_Eq
      (shift_context_mul
        (shift_context_mul
          (shift_context_nary ctx (2 : ℕ+) (FPM_AddNary 2))
          (max Ck (Cx * Cx)))
        Cx)
      s.pos s'.pos)
    (hV : FPM_Eq
      (shift_context_mul
        (shift_context_mul
          (shift_context_nary ctx (2 : ℕ+) (FPM_AddNary 2))
          (max Cm (Cv * Cv)))
        Cv)
      s.vel s'.vel) :
    FPM_Eq ctx (FPM_Phase7_Energy p s) (FPM_Phase7_Energy p' s') := by
  have hTerms :
      ∀ i : Fin 2,
        FPM_Eq
          (shift_context_nary ctx (2 : ℕ+) (FPM_AddNary 2))
          (FPM_Phase7_EnergyTerms p s i)
          (FPM_Phase7_EnergyTerms p' s' i) := by
    exact FPM_Phase7_EnergyTerms_substitution
      (ctx := shift_context_nary ctx (2 : ℕ+) (FPM_AddNary 2))
      (p := p) (p' := p') (s := s) (s' := s')
      hm hm' hk hk' hx hx' hv hv' hM hK hX hV
  simpa [FPM_Phase7_Energy] using
    (FPM_NaryAdd_Substitution
      (ctx := ctx)
      (n := (2 : ℕ+))
      (v₁ := FPM_Phase7_EnergyTerms p s)
      (v₂ := FPM_Phase7_EnergyTerms p' s')
      hTerms)

/-!
  ========================================================================
  SECTION 5: ARTIFACT FILTRATION AND COMPILER VISIBLE CERTIFICATION
  The first physical model does not accept every formally writable observable.
  It accepts exactly those observables for which the Phase-4/5/6 support data
  exists:
  - boundedness for guarded products,
  - apartness for certified inversion,
  - shifted-context support for transport,
  - native n-ary support for flat finite aggregation.

  In this section an "artifact" is therefore not a new ontology object.
  It is simply a proposed observable that fails certification at the chosen
  local scale.
  ========================================================================
-/


/-- Certified local support package for the first Phase 7 model. -/
structure FPM_Phase7_CertifiedLocal where
  p : FPM_Phase7_Params
  s : FPM_Phase7_State
  Cpos : ℕ+
  Cvel : ℕ+
  Cinv : ℕ+
  pos_bounded : FPM_Bounded s.pos Cpos
  vel_bounded : FPM_Bounded s.vel Cvel
  invMass_bounded : FPM_Bounded (FPM_Phase7_InvMass p) Cinv


/-- Surviving artifact filtration at scale `C` means being certified as bounded
at that local scale. -/
def FPM_Phase7_SurvivesArtifactFiltration
    (x : FPM_Real) (C : ℕ+) : Prop :=
  FPM_Bounded x C


/-- An artifact at scale `C` is an expression that fails the certification
test at that scale. -/
def FPM_Phase7_IsArtifact
    (x : FPM_Real) (C : ℕ+) : Prop :=
  ¬ FPM_Phase7_SurvivesArtifactFiltration x C


@[simp] theorem FPM_Phase7_survives_iff_bounded
    (x : FPM_Real) (C : ℕ+) :
    FPM_Phase7_SurvivesArtifactFiltration x C ↔ FPM_Bounded x C := by
  rfl


@[simp] theorem FPM_Phase7_artifact_iff_not_bounded
    (x : FPM_Real) (C : ℕ+) :
    FPM_Phase7_IsArtifact x C ↔ ¬ FPM_Bounded x C := by
  rfl


/-- Force passes artifact filtration on certified local data. -/
theorem FPM_Phase7_Force_survives_filtration
    (q : FPM_Phase7_CertifiedLocal) :
    FPM_Phase7_SurvivesArtifactFiltration
      (FPM_Phase7_Force q.p q.s)
      (q.p.Cspring * q.Cpos) := by
  exact
    FPM_Phase7_Force_bounded
      (p := q.p) (s := q.s)
      (hK := q.p.spring_bounded)
      (hX := q.pos_bounded)


/-- Acceleration passes artifact filtration once inverse mass is certified. -/
theorem FPM_Phase7_Acceleration_survives_filtration
    (q : FPM_Phase7_CertifiedLocal) :
    FPM_Phase7_SurvivesArtifactFiltration
      (FPM_Phase7_Acceleration q.p q.s)
      (q.Cinv * (q.p.Cspring * q.Cpos)) := by
  exact
    FPM_Phase7_Acceleration_bounded_of_bounds
      (p := q.p) (s := q.s)
      (hm := q.invMass_bounded)
      (hK := q.p.spring_bounded)
      (hX := q.pos_bounded)


/-- Packaged energy passes artifact filtration on certified local data. -/
theorem FPM_Phase7_Energy_survives_filtration
    (q : FPM_Phase7_CertifiedLocal) :
    FPM_Phase7_SurvivesArtifactFiltration
      (FPM_Phase7_Energy q.p q.s)
      (q.p.Cmass * (q.Cvel * q.Cvel) + q.p.Cspring * (q.Cpos * q.Cpos)) := by
  exact
    FPM_Phase7_Energy_bounded
      (p := q.p) (s := q.s)
      (hm := q.p.mass_bounded)
      (hk := q.p.spring_bounded)
      (hx := q.pos_bounded)
      (hv := q.vel_bounded)


/-- Force is therefore not an artifact at the certified local scale. -/
theorem FPM_Phase7_Force_not_artifact
    (q : FPM_Phase7_CertifiedLocal) :
    ¬ FPM_Phase7_IsArtifact
      (FPM_Phase7_Force q.p q.s)
      (q.p.Cspring * q.Cpos) := by
  intro hArt
  exact hArt (FPM_Phase7_Force_survives_filtration q)


/-- Acceleration is therefore not an artifact at the certified local scale. -/
theorem FPM_Phase7_Acceleration_not_artifact
    (q : FPM_Phase7_CertifiedLocal) :
    ¬ FPM_Phase7_IsArtifact
      (FPM_Phase7_Acceleration q.p q.s)
      (q.Cinv * (q.p.Cspring * q.Cpos)) := by
  intro hArt
  exact hArt (FPM_Phase7_Acceleration_survives_filtration q)


/-- Energy is therefore not an artifact at the certified local scale. -/
theorem FPM_Phase7_Energy_not_artifact
    (q : FPM_Phase7_CertifiedLocal) :
    ¬ FPM_Phase7_IsArtifact
      (FPM_Phase7_Energy q.p q.s)
      (q.p.Cmass * (q.Cvel * q.Cvel) + q.p.Cspring * (q.Cpos * q.Cpos)) := by
  intro hArt
  exact hArt (FPM_Phase7_Energy_survives_filtration q)


/-- Artifact filtration respects overlap transport: once two certified local
descriptions are related by the Section 4 support data, the packaged energy
observable is transported across the overlap. -/
theorem FPM_Phase7_Energy_filtration_transport
    (ctx : _root_.Context)
    (p p' : FPM_Phase7_Params) (s s' : FPM_Phase7_State)
    {Cm Ck Cx Cv : ℕ+}
    (hm : FPM_Bounded p.mass Cm)
    (hm' : FPM_Bounded p'.mass Cm)
    (hk : FPM_Bounded p.spring Ck)
    (hk' : FPM_Bounded p'.spring Ck)
    (hx : FPM_Bounded s.pos Cx)
    (hx' : FPM_Bounded s'.pos Cx)
    (hv : FPM_Bounded s.vel Cv)
    (hv' : FPM_Bounded s'.vel Cv)
    (hM : FPM_Eq
      (shift_context_mul
        (shift_context_nary ctx (2 : ℕ+) (FPM_AddNary 2))
        (max Cm (Cv * Cv)))
      p.mass p'.mass)
    (hK : FPM_Eq
      (shift_context_mul
        (shift_context_nary ctx (2 : ℕ+) (FPM_AddNary 2))
        (max Ck (Cx * Cx)))
      p.spring p'.spring)
    (hX : FPM_Eq
      (shift_context_mul
        (shift_context_mul
          (shift_context_nary ctx (2 : ℕ+) (FPM_AddNary 2))
          (max Ck (Cx * Cx)))
        Cx)
      s.pos s'.pos)
    (hV : FPM_Eq
      (shift_context_mul
        (shift_context_mul
          (shift_context_nary ctx (2 : ℕ+) (FPM_AddNary 2))
          (max Cm (Cv * Cv)))
        Cv)
      s.vel s'.vel) :
    FPM_Eq ctx (FPM_Phase7_Energy p s) (FPM_Phase7_Energy p' s') := by
  exact
    FPM_Phase7_Energy_substitution
      (ctx := ctx) (p := p) (p' := p') (s := s) (s' := s')
      hm hm' hk hk' hx hx' hv hv' hM hK hX hV


/-!
  ------------------------------------------------------------------------
  SECTION 5A: COMPILER / AUTOMATION SMOKE TESTS INSIDE PHASE 7
  These theorems are intentionally small.  Their job is to show that Phase 7
  is consuming the earlier compiler-facing infrastructure instead of bypassing
  it by hand.
  ------------------------------------------------------------------------
-/


/-- If the product support has already been produced at the neg-shifted context,
the public exact dispatcher closes force transport automatically. -/
theorem FPM_Phase7_Force_substitution_auto
    (ctx : _root_.Context)
    (p p' : FPM_Phase7_Params) (s s' : FPM_Phase7_State)
    (hmul :
      FPM_Eq (shift_context_unary ctx FPM_Neg)
        (p.spring * s.pos) (p'.spring * s'.pos)) :
    FPM_Eq ctx (FPM_Phase7_Force p s) (FPM_Phase7_Force p' s') := by
  simpa [FPM_Phase7_Force] using
    (by
      fpm :
        FPM_Eq ctx
          (-(p.spring * s.pos))
          (-(p'.spring * s'.pos)))


/-- Native n-ary energy packaging can be closed by the public exact dispatcher
once the shifted family equality is present. -/
theorem FPM_Phase7_Energy_substitution_auto_exact
    (ctx : _root_.Context)
    (p p' : FPM_Phase7_Params) (s s' : FPM_Phase7_State)
    (hTerms : ∀ i : Fin 2,
      FPM_Eq
        (shift_context_nary ctx (2 : ℕ+) (FPM_AddNary 2))
        (FPM_Phase7_EnergyTerms p s i)
        (FPM_Phase7_EnergyTerms p' s' i)) :
    FPM_Eq ctx (FPM_Phase7_Energy p s) (FPM_Phase7_Energy p' s') := by
  unfold FPM_Phase7_Energy
  exact FPM_NaryAdd_Substitution
    (ctx := ctx)
    (n := (2 : ℕ+))
    (v₁ := FPM_Phase7_EnergyTerms p s)
    (v₂ := FPM_Phase7_EnergyTerms p' s')
    hTerms

/- The weakened n-ary front-end can also close packaged energy transport from
a stronger support context. -/

theorem FPM_Phase7_Energy_substitution_auto_from
    (ctx ctxH : _root_.Context)
    (p p' : FPM_Phase7_Params) (s s' : FPM_Phase7_State)
    (hM :
      (shift_context_nary ctx (2 : ℕ+) (FPM_AddNary 2)).M ≤ ctxH.M)
    (hN :
      ctxH.N ≤ (shift_context_nary ctx (2 : ℕ+) (FPM_AddNary 2)).N)
    (hTerms : ∀ i : Fin 2,
      FPM_Eq ctxH
        (FPM_Phase7_EnergyTerms p s i)
        (FPM_Phase7_EnergyTerms p' s' i)) :
    FPM_Eq ctx (FPM_Phase7_Energy p s) (FPM_Phase7_Energy p' s') := by
  unfold FPM_Phase7_Energy
  exact
    FPM_NaryAdd_Substitution_of_weaker
      (ctx := ctx)
      (ctxH := ctxH)
      (n := (2 : ℕ+))
      (v := FPM_Phase7_EnergyTerms p s)
      (w := FPM_Phase7_EnergyTerms p' s')
      hM hN hTerms


/-- Guarded multiplication for the kinetic core can be discharged through the
public multiplication front-end once the square has already been certified. -/
theorem FPM_Phase7_KineticCore_substitution_auto_exact
    (ctx : _root_.Context)
    (p p' : FPM_Phase7_Params) (s s' : FPM_Phase7_State)
    {Cm Cv : ℕ+}
    (hm : FPM_Bounded p.mass Cm)
    (hm' : FPM_Bounded p'.mass Cm)
    (hvsq : FPM_Bounded (s.vel * s.vel) (Cv * Cv))
    (hvsq' : FPM_Bounded (s'.vel * s'.vel) (Cv * Cv))
    (hM :
      FPM_Eq (shift_context_mul ctx (max Cm (Cv * Cv)))
        p.mass p'.mass)
    (hV2 :
      FPM_Eq (shift_context_mul ctx (max Cm (Cv * Cv)))
        (s.vel * s.vel) (s'.vel * s'.vel)) :
    FPM_Eq ctx
      (FPM_Phase7_KineticCore p s)
      (FPM_Phase7_KineticCore p' s') := by
  have hm_max : FPM_Bounded p.mass (max Cm (Cv * Cv)) := by
    intro n
    exact le_trans (hm n) (by
      change ((Cm : ℕ+) : ℚ) ≤ ((max Cm (Cv * Cv) : ℕ+) : ℚ)
      exact_mod_cast le_max_left Cm (Cv * Cv))
  have hm'_max : FPM_Bounded p'.mass (max Cm (Cv * Cv)) := by
    intro n
    exact le_trans (hm' n) (by
      change ((Cm : ℕ+) : ℚ) ≤ ((max Cm (Cv * Cv) : ℕ+) : ℚ)
      exact_mod_cast le_max_left Cm (Cv * Cv))
  have hvsq_max : FPM_Bounded (s.vel * s.vel) (max Cm (Cv * Cv)) := by
    intro n
    exact le_trans (hvsq n) (by
      change (((Cv * Cv : ℕ+) : ℕ) : ℚ) ≤ ((max Cm (Cv * Cv) : ℕ+) : ℚ)
      exact_mod_cast le_max_right Cm (Cv * Cv))
  have hvsq'_max : FPM_Bounded (s'.vel * s'.vel) (max Cm (Cv * Cv)) := by
    intro n
    exact le_trans (hvsq' n) (by
      change (((Cv * Cv : ℕ+) : ℕ) : ℚ) ≤ ((max Cm (Cv * Cv) : ℕ+) : ℚ)
      exact_mod_cast le_max_right Cm (Cv * Cv))
  simpa [FPM_Phase7_KineticCore] using
    (FPM_Mul_Substitution_full
      (ctx := ctx) (C := max Cm (Cv * Cv))
      (a₁ := p.mass) (a₂ := p'.mass)
      (b₁ := s.vel * s.vel) (b₂ := s'.vel * s'.vel)
      hm_max hm'_max hvsq_max hvsq'_max hM hV2)


/-- Small public-facing certification package:
if local support exists, the main observables are filtered in and therefore
not artifacts. -/
theorem FPM_Phase7_CertifiedLocal_main_observables
    (q : FPM_Phase7_CertifiedLocal) :
    FPM_Phase7_SurvivesArtifactFiltration
        (FPM_Phase7_Force q.p q.s) (q.p.Cspring * q.Cpos)
    ∧ FPM_Phase7_SurvivesArtifactFiltration
        (FPM_Phase7_Acceleration q.p q.s) (q.Cinv * (q.p.Cspring * q.Cpos))
    ∧ FPM_Phase7_SurvivesArtifactFiltration
        (FPM_Phase7_Energy q.p q.s)
        (q.p.Cmass * (q.Cvel * q.Cvel) + q.p.Cspring * (q.Cpos * q.Cpos)) := by
  exact
    ⟨ FPM_Phase7_Force_survives_filtration q
    , FPM_Phase7_Acceleration_survives_filtration q
    , FPM_Phase7_Energy_survives_filtration q ⟩


/-!
  ========================================================================
  SECTION 6: LOCAL PHYSICAL CHARTS AND OVERLAP-STABLE OBSERVABLES

  We now lift the Phase 7 oscillator into the Phase 6 local-window/sheaf API.

  Design:
  - a Phase 7 state is encoded as a finite 2-vector `(pos, vel)`,
  - certified local data determines a local chart centered at that state,
  - force, acceleration, and energy become local scalar fields,
  - these fields define chart sections,
  - each section is reflexively overlap-stable via the identity transition,
  - the energy section therefore gives a minimal compatible one-chart atlas.
  ========================================================================
-/

/-!
  ------------------------------------------------------------------------
  SECTION 6A: STATE SPACE AND LOCAL OBSERVABLES

  Freeze point for:
  - state ↔ vector encoding,
  - certified local chart,
  - local force / acceleration / energy fields,
  - chart sections,
  - evaluation and filtration at the certified state.

  This subsection ends at `FPM_Phase7_EnergySection_survives_at_state`.
  Everything after that belongs to the next layer.
  ------------------------------------------------------------------------
-/

/-- Encode a Phase 7 state as the 2-vector `(pos, vel)`. -/
def FPM_Phase7_StateVec (s : FPM_Phase7_State) : FPM_Vector 2
  | ⟨0, _⟩ => s.pos
  | ⟨1, _⟩ => s.vel

@[simp] theorem FPM_Phase7_StateVec_pos
    (s : FPM_Phase7_State) :
    FPM_Phase7_StateVec s ⟨0, by decide⟩ = s.pos := by
  rfl

@[simp] theorem FPM_Phase7_StateVec_vel
    (s : FPM_Phase7_State) :
    FPM_Phase7_StateVec s ⟨1, by decide⟩ = s.vel := by
  rfl


/-- Decode a 2-vector back into a Phase 7 state. -/
def FPM_Phase7_StateOfVec (x : FPM_Vector 2) : FPM_Phase7_State where
  pos := x ⟨0, by decide⟩
  vel := x ⟨1, by decide⟩

@[simp] theorem FPM_Phase7_StateOfVec_pos
    (x : FPM_Vector 2) :
    (FPM_Phase7_StateOfVec x).pos = x ⟨0, by decide⟩ := by
  rfl

@[simp] theorem FPM_Phase7_StateOfVec_vel
    (x : FPM_Vector 2) :
    (FPM_Phase7_StateOfVec x).vel = x ⟨1, by decide⟩ := by
  rfl

@[simp] theorem FPM_Phase7_StateOfVec_StateVec
    (s : FPM_Phase7_State) :
    FPM_Phase7_StateOfVec (FPM_Phase7_StateVec s) = s := by
  cases s
  rfl


/-- Conservative local radius for the state chart. -/
def FPM_Phase7_StateRadius
    (q : FPM_Phase7_CertifiedLocal) : ℕ+ :=
  max q.Cpos q.Cvel


/-- The certified local chart attached to a certified package. -/
def FPM_Phase7_LocalChart
    (q : FPM_Phase7_CertifiedLocal) : FPM_LocalChart 2 where
  center := FPM_Phase7_StateVec q.s
  C := FPM_Phase7_StateRadius q


/-- The certified state lies in its own local chart. -/
theorem FPM_Phase7_state_mem_local_chart
    (q : FPM_Phase7_CertifiedLocal) :
    (FPM_Phase7_LocalChart q).Mem (FPM_Phase7_StateVec q.s) := by
  unfold FPM_LocalChart.Mem
  unfold FPM_Phase7_LocalChart
  unfold FPM_Phase7_StateRadius
  apply FPM_Vector_Window_mk
  intro i
  fin_cases i
  · intro n
    have h0 : (0 : ℚ) ≤ (((max q.Cpos q.Cvel : ℕ+) : ℕ) : ℚ) := by
      positivity
    simp [h0]
  · intro n
    have h0 : (0 : ℚ) ≤ (((max q.Cpos q.Cvel : ℕ+) : ℕ) : ℚ) := by
      positivity
    simp [h0]


/-- Force as a local scalar field on 2-state space. -/
def FPM_Phase7_ForceField
    (p : FPM_Phase7_Params) : FPM_LocalField 2 :=
  fun x => FPM_Phase7_Force p (FPM_Phase7_StateOfVec x)

/-- Acceleration as a local scalar field on 2-state space. -/
def FPM_Phase7_AccelerationField
    (p : FPM_Phase7_Params) : FPM_LocalField 2 :=
  fun x => FPM_Phase7_Acceleration p (FPM_Phase7_StateOfVec x)

/-- Energy as a local scalar field on 2-state space. -/
def FPM_Phase7_EnergyField
    (p : FPM_Phase7_Params) : FPM_LocalField 2 :=
  fun x => FPM_Phase7_Energy p (FPM_Phase7_StateOfVec x)


@[simp] theorem FPM_Phase7_ForceField_on_state
    (p : FPM_Phase7_Params) (s : FPM_Phase7_State) :
    FPM_Phase7_ForceField p (FPM_Phase7_StateVec s) =
      FPM_Phase7_Force p s := by
  simp [FPM_Phase7_ForceField]

@[simp] theorem FPM_Phase7_AccelerationField_on_state
    (p : FPM_Phase7_Params) (s : FPM_Phase7_State) :
    FPM_Phase7_AccelerationField p (FPM_Phase7_StateVec s) =
      FPM_Phase7_Acceleration p s := by
  simp [FPM_Phase7_AccelerationField]

@[simp] theorem FPM_Phase7_EnergyField_on_state
    (p : FPM_Phase7_Params) (s : FPM_Phase7_State) :
    FPM_Phase7_EnergyField p (FPM_Phase7_StateVec s) =
      FPM_Phase7_Energy p s := by
  simp [FPM_Phase7_EnergyField]


/-- Force section over the certified local chart. -/
def FPM_Phase7_ForceSection
    (q : FPM_Phase7_CertifiedLocal) : FPM_ChartSection 2 where
  chart := FPM_Phase7_LocalChart q
  field := FPM_Phase7_ForceField q.p

/-- Acceleration section over the certified local chart. -/
def FPM_Phase7_AccelerationSection
    (q : FPM_Phase7_CertifiedLocal) : FPM_ChartSection 2 where
  chart := FPM_Phase7_LocalChart q
  field := FPM_Phase7_AccelerationField q.p

/-- Energy section over the certified local chart. -/
def FPM_Phase7_EnergySection
    (q : FPM_Phase7_CertifiedLocal) : FPM_ChartSection 2 where
  chart := FPM_Phase7_LocalChart q
  field := FPM_Phase7_EnergyField q.p


/-- The force section, evaluated at the certified state, survives filtration. -/
theorem FPM_Phase7_ForceSection_survives_at_state
    (q : FPM_Phase7_CertifiedLocal) :
    FPM_Phase7_SurvivesArtifactFiltration
      ((FPM_Phase7_ForceSection q).field (FPM_Phase7_StateVec q.s))
      (q.p.Cspring * q.Cpos) := by
  simpa [FPM_Phase7_ForceSection]
    using FPM_Phase7_Force_survives_filtration q

/-- The acceleration section, evaluated at the certified state, survives filtration. -/
theorem FPM_Phase7_AccelerationSection_survives_at_state
    (q : FPM_Phase7_CertifiedLocal) :
    FPM_Phase7_SurvivesArtifactFiltration
      ((FPM_Phase7_AccelerationSection q).field (FPM_Phase7_StateVec q.s))
      (q.Cinv * (q.p.Cspring * q.Cpos)) := by
  simpa [FPM_Phase7_AccelerationSection]
    using FPM_Phase7_Acceleration_survives_filtration q

/-- The energy section, evaluated at the certified state, survives filtration. -/
theorem FPM_Phase7_EnergySection_survives_at_state
    (q : FPM_Phase7_CertifiedLocal) :
    FPM_Phase7_SurvivesArtifactFiltration
      ((FPM_Phase7_EnergySection q).field (FPM_Phase7_StateVec q.s))
      (q.p.Cmass * (q.Cvel * q.Cvel) + q.p.Cspring * (q.Cpos * q.Cpos)) := by
  simpa [FPM_Phase7_EnergySection]
    using FPM_Phase7_Energy_survives_filtration q

/-- Packaged freeze theorem for 7.2:
the certified state lies in its local chart, the three local observables evaluate
to the physical force/acceleration/energy at that state, and all three survive
artifact filtration at the certified local scale. -/
theorem FPM_Phase7_StateSpaceAndLocalObservables_package
    (q : FPM_Phase7_CertifiedLocal) :
    (FPM_Phase7_LocalChart q).Mem (FPM_Phase7_StateVec q.s) ∧
    ((FPM_Phase7_ForceSection q).field (FPM_Phase7_StateVec q.s) =
      FPM_Phase7_Force q.p q.s) ∧
    ((FPM_Phase7_AccelerationSection q).field (FPM_Phase7_StateVec q.s) =
      FPM_Phase7_Acceleration q.p q.s) ∧
    ((FPM_Phase7_EnergySection q).field (FPM_Phase7_StateVec q.s) =
      FPM_Phase7_Energy q.p q.s) ∧
    FPM_Phase7_SurvivesArtifactFiltration
      ((FPM_Phase7_ForceSection q).field (FPM_Phase7_StateVec q.s))
      (q.p.Cspring * q.Cpos) ∧
    FPM_Phase7_SurvivesArtifactFiltration
      ((FPM_Phase7_AccelerationSection q).field (FPM_Phase7_StateVec q.s))
      (q.Cinv * (q.p.Cspring * q.Cpos)) ∧
    FPM_Phase7_SurvivesArtifactFiltration
      ((FPM_Phase7_EnergySection q).field (FPM_Phase7_StateVec q.s))
      (q.p.Cmass * (q.Cvel * q.Cvel) + q.p.Cspring * (q.Cpos * q.Cpos)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact FPM_Phase7_state_mem_local_chart q
  · simpa [FPM_Phase7_ForceSection] using
      (FPM_Phase7_ForceField_on_state q.p q.s)
  · simpa [FPM_Phase7_AccelerationSection] using
      (FPM_Phase7_AccelerationField_on_state q.p q.s)
  · simpa [FPM_Phase7_EnergySection] using
      (FPM_Phase7_EnergyField_on_state q.p q.s)
  · exact FPM_Phase7_ForceSection_survives_at_state q
  · exact FPM_Phase7_AccelerationSection_survives_at_state q
  · exact FPM_Phase7_EnergySection_survives_at_state q

/-!
  ------------------------------------------------------------------------
  SECTION 6B: 7.3 REFLEXIVE OVERLAP AND ONE-CHART ATLAS

  This subsection contains:
  - generic self-overlap for local scalar fields,
  - reflexive overlap of force / acceleration / energy sections,
  - the one-chart energy atlas,
  - compatibility of that one-chart atlas.

  It ends at `FPM_Phase7_local_chart_energy_package`.
  ------------------------------------------------------------------------
-/

/-- Generic self-overlap of any local scalar field at context `(ctx.M * 1, ctx.N)`. -/
theorem FPM_Phase7_field_self_overlap_at_mul1
    (ctx : _root_.Context)
    (f : FPM_LocalField 2)
    (x : FPM_Vector 2) :
    FPM_Eq ({ M := ctx.M * 1, N := ctx.N } : _root_.Context) (f x) (f x) := by
  intro n hn
  refine ⟨(f x).seq n, ?_, ?_⟩ <;> simp [FPM_Interval]

/-- Force section overlaps with itself under the identity transition. -/
theorem FPM_Phase7_ForceSection_overlap_refl
    (ctx : _root_.Context)
    (q : FPM_Phase7_CertifiedLocal) :
    FPM_Sheaf_Overlap ctx
      (FPM_Phase7_ForceSection q)
      (FPM_Phase7_ForceSection q)
      (FPM_ChartTransition.id (FPM_Phase7_LocalChart q)) := by
  apply FPM_Sheaf_Overlap_refl
  intro x
  simpa [FPM_Phase7_ForceSection, FPM_Phase7_ForceField]
    using FPM_Phase7_field_self_overlap_at_mul1 ctx (FPM_Phase7_ForceField q.p) x

/-- Acceleration section overlaps with itself under the identity transition. -/
theorem FPM_Phase7_AccelerationSection_overlap_refl
    (ctx : _root_.Context)
    (q : FPM_Phase7_CertifiedLocal) :
    FPM_Sheaf_Overlap ctx
      (FPM_Phase7_AccelerationSection q)
      (FPM_Phase7_AccelerationSection q)
      (FPM_ChartTransition.id (FPM_Phase7_LocalChart q)) := by
  apply FPM_Sheaf_Overlap_refl
  intro x
  simpa [FPM_Phase7_AccelerationSection, FPM_Phase7_AccelerationField]
    using FPM_Phase7_field_self_overlap_at_mul1 ctx (FPM_Phase7_AccelerationField q.p) x

/-- Energy section overlaps with itself under the identity transition. -/
theorem FPM_Phase7_EnergySection_overlap_refl
    (ctx : _root_.Context)
    (q : FPM_Phase7_CertifiedLocal) :
    FPM_Sheaf_Overlap ctx
      (FPM_Phase7_EnergySection q)
      (FPM_Phase7_EnergySection q)
      (FPM_ChartTransition.id (FPM_Phase7_LocalChart q)) := by
  apply FPM_Sheaf_Overlap_refl
  intro x
  simpa [FPM_Phase7_EnergySection, FPM_Phase7_EnergyField]
    using FPM_Phase7_field_self_overlap_at_mul1 ctx (FPM_Phase7_EnergyField q.p) x


/-- A one-chart atlas carrying the local energy section. -/
def FPM_Phase7_EnergySingleAtlas
    (q : FPM_Phase7_CertifiedLocal) : FPM_SheafAtlas Unit 2 where
  chart _ := FPM_Phase7_LocalChart q
  field _ := FPM_Phase7_EnergyField q.p
  transition _ _ := FPM_ChartTransition.id (FPM_Phase7_LocalChart q)

/-- The one-chart energy atlas is compatible. -/
theorem FPM_Phase7_EnergySingleAtlas_compatible
    (ctx : _root_.Context)
    (q : FPM_Phase7_CertifiedLocal) :
    (FPM_Phase7_EnergySingleAtlas q).Compatible ctx := by
  intro i j
  cases i
  cases j
  simpa [FPM_Phase7_EnergySingleAtlas]
    using FPM_Phase7_EnergySection_overlap_refl ctx q


/-- Small packaged statement for Section 6:
the certified state lies in its chart, the energy section survives filtration at
that state, and the corresponding one-chart atlas is compatible. -/
theorem FPM_Phase7_local_chart_energy_package
    (ctx : _root_.Context)
    (q : FPM_Phase7_CertifiedLocal) :
    (FPM_Phase7_LocalChart q).Mem (FPM_Phase7_StateVec q.s)
    ∧ FPM_Phase7_SurvivesArtifactFiltration
        ((FPM_Phase7_EnergySection q).field (FPM_Phase7_StateVec q.s))
        (q.p.Cmass * (q.Cvel * q.Cvel) + q.p.Cspring * (q.Cpos * q.Cpos))
    ∧ (FPM_Phase7_EnergySingleAtlas q).Compatible ctx := by
  exact
    ⟨ FPM_Phase7_state_mem_local_chart q
    , FPM_Phase7_EnergySection_survives_at_state q
    , FPM_Phase7_EnergySingleAtlas_compatible ctx q ⟩

/-- Freeze theorem for 7.3:
the three basic local sections are reflexively overlap-stable under the identity
transition, and the resulting one-chart energy atlas is compatible. -/
theorem FPM_Phase7_reflexive_overlap_and_single_atlas_package
    (ctx : _root_.Context) (q : FPM_Phase7_CertifiedLocal) :
    FPM_Sheaf_Overlap ctx
      (FPM_Phase7_ForceSection q)
      (FPM_Phase7_ForceSection q)
      (FPM_ChartTransition.id (FPM_Phase7_LocalChart q)) ∧
    FPM_Sheaf_Overlap ctx
      (FPM_Phase7_AccelerationSection q)
      (FPM_Phase7_AccelerationSection q)
      (FPM_ChartTransition.id (FPM_Phase7_LocalChart q)) ∧
    FPM_Sheaf_Overlap ctx
      (FPM_Phase7_EnergySection q)
      (FPM_Phase7_EnergySection q)
      (FPM_ChartTransition.id (FPM_Phase7_LocalChart q)) ∧
    (FPM_Phase7_EnergySingleAtlas q).Compatible ctx := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using FPM_Phase7_ForceSection_overlap_refl ctx q
  · simpa using FPM_Phase7_AccelerationSection_overlap_refl ctx q
  · simpa using FPM_Phase7_EnergySection_overlap_refl ctx q
  · exact FPM_Phase7_EnergySingleAtlas_compatible ctx q


/-!
  ------------------------------------------------------------------------
  SECTION 7.4 TWO-CHART OVERLAP AND SHEAF GLUING

  This subsection contains:
  - identity transitions induced by certified chart inclusion,
  - overlap agreement for force / acceleration / energy under same parameters,
  - the two-chart energy atlas,
  - compatibility and gluing for that atlas.
  ------------------------------------------------------------------------
-/

/-- Identity transition induced by a certified inclusion of local charts. -/
def FPM_Phase7_TransitionOfInclusion
    (q₁ q₂ : FPM_Phase7_CertifiedLocal)
    (hincl :
      ∀ x : FPM_Vector 2,
        (FPM_Phase7_LocalChart q₁).Mem x →
        (FPM_Phase7_LocalChart q₂).Mem x) :
    FPM_ChartTransition 2
      (FPM_Phase7_LocalChart q₁)
      (FPM_Phase7_LocalChart q₂) where
  trans := fun x => x
  K := 1
  map_mem := by
    intro x hx
    exact hincl x hx
  transport := by
    intro ctx x y hxy
    simpa using hxy


/-- Force agrees across an inclusion transition when the oscillator parameters agree. -/
theorem FPM_Phase7_ForceSection_overlap_of_same_params
    (ctx : _root_.Context)
    (q₁ q₂ : FPM_Phase7_CertifiedLocal)
    (hp : q₁.p = q₂.p)
    (hincl :
      ∀ x : FPM_Vector 2,
        (FPM_Phase7_LocalChart q₁).Mem x →
        (FPM_Phase7_LocalChart q₂).Mem x) :
    FPM_Sheaf_Overlap ctx
      (FPM_Phase7_ForceSection q₁)
      (FPM_Phase7_ForceSection q₂)
      (FPM_Phase7_TransitionOfInclusion q₁ q₂ hincl) := by
  intro x hx
  simpa
    [hp,
     FPM_Phase7_ForceSection,
     FPM_Phase7_ForceField,
     FPM_Phase7_TransitionOfInclusion]
    using
      FPM_Phase7_field_self_overlap_at_mul1
        ctx
        (FPM_Phase7_ForceField q₂.p)
        x


/-- Acceleration agrees across an inclusion transition when the oscillator parameters agree. -/
theorem FPM_Phase7_AccelerationSection_overlap_of_same_params
    (ctx : _root_.Context)
    (q₁ q₂ : FPM_Phase7_CertifiedLocal)
    (hp : q₁.p = q₂.p)
    (hincl :
      ∀ x : FPM_Vector 2,
        (FPM_Phase7_LocalChart q₁).Mem x →
        (FPM_Phase7_LocalChart q₂).Mem x) :
    FPM_Sheaf_Overlap ctx
      (FPM_Phase7_AccelerationSection q₁)
      (FPM_Phase7_AccelerationSection q₂)
      (FPM_Phase7_TransitionOfInclusion q₁ q₂ hincl) := by
  intro x hx
  simpa
    [hp,
     FPM_Phase7_AccelerationSection,
     FPM_Phase7_AccelerationField,
     FPM_Phase7_TransitionOfInclusion]
    using
      FPM_Phase7_field_self_overlap_at_mul1
        ctx
        (FPM_Phase7_AccelerationField q₂.p)
        x


/-- Energy agrees across an inclusion transition when the oscillator parameters agree. -/
theorem FPM_Phase7_EnergySection_overlap_of_same_params
    (ctx : _root_.Context)
    (q₁ q₂ : FPM_Phase7_CertifiedLocal)
    (hp : q₁.p = q₂.p)
    (hincl :
      ∀ x : FPM_Vector 2,
        (FPM_Phase7_LocalChart q₁).Mem x →
        (FPM_Phase7_LocalChart q₂).Mem x) :
    FPM_Sheaf_Overlap ctx
      (FPM_Phase7_EnergySection q₁)
      (FPM_Phase7_EnergySection q₂)
      (FPM_Phase7_TransitionOfInclusion q₁ q₂ hincl) := by
  intro x hx
  simpa
    [hp,
     FPM_Phase7_EnergySection,
     FPM_Phase7_EnergyField,
     FPM_Phase7_TransitionOfInclusion]
    using
      FPM_Phase7_field_self_overlap_at_mul1
        ctx
        (FPM_Phase7_EnergyField q₂.p)
        x


/-- A two-chart energy atlas for two certified local oscillator charts.

`false` indexes the first chart and `true` indexes the second.
-/
def FPM_Phase7_TwoChartEnergyAtlas
    (q₁ q₂ : FPM_Phase7_CertifiedLocal)
    (h12 :
      ∀ x : FPM_Vector 2,
        (FPM_Phase7_LocalChart q₁).Mem x →
        (FPM_Phase7_LocalChart q₂).Mem x)
    (h21 :
      ∀ x : FPM_Vector 2,
        (FPM_Phase7_LocalChart q₂).Mem x →
        (FPM_Phase7_LocalChart q₁).Mem x) :
    FPM_SheafAtlas Bool 2 where
  chart
    | false => FPM_Phase7_LocalChart q₁
    | true  => FPM_Phase7_LocalChart q₂
  field
    | false => FPM_Phase7_EnergyField q₁.p
    | true  => FPM_Phase7_EnergyField q₂.p
  transition
    | false, false => FPM_ChartTransition.id (FPM_Phase7_LocalChart q₁)
    | false, true  => FPM_Phase7_TransitionOfInclusion q₁ q₂ h12
    | true, false  => FPM_Phase7_TransitionOfInclusion q₂ q₁ h21
    | true, true   => FPM_ChartTransition.id (FPM_Phase7_LocalChart q₂)


/-- The two-chart energy atlas is compatible when both charts use the same parameters
and each chart includes into the other on overlaps. -/
theorem FPM_Phase7_TwoChartEnergyAtlas_compatible
    (ctx : _root_.Context)
    (q₁ q₂ : FPM_Phase7_CertifiedLocal)
    (hp : q₁.p = q₂.p)
    (h12 :
      ∀ x : FPM_Vector 2,
        (FPM_Phase7_LocalChart q₁).Mem x →
        (FPM_Phase7_LocalChart q₂).Mem x)
    (h21 :
      ∀ x : FPM_Vector 2,
        (FPM_Phase7_LocalChart q₂).Mem x →
        (FPM_Phase7_LocalChart q₁).Mem x) :
    (FPM_Phase7_TwoChartEnergyAtlas q₁ q₂ h12 h21).Compatible ctx := by
  intro i j
  cases i <;> cases j
  ·
    simpa [FPM_Phase7_TwoChartEnergyAtlas]
      using FPM_Phase7_EnergySection_overlap_refl ctx q₁
  ·
    simpa [FPM_Phase7_TwoChartEnergyAtlas]
      using FPM_Phase7_EnergySection_overlap_of_same_params ctx q₁ q₂ hp h12
  ·
    simpa [FPM_Phase7_TwoChartEnergyAtlas]
      using FPM_Phase7_EnergySection_overlap_of_same_params ctx q₂ q₁ hp.symm h21
  ·
    simpa [FPM_Phase7_TwoChartEnergyAtlas]
      using FPM_Phase7_EnergySection_overlap_refl ctx q₂


/-- A compact packaged Section 7 statement:
two certified local charts with the same oscillator parameters glue to a
compatible two-chart energy atlas. -/
theorem FPM_Phase7_two_chart_energy_gluing
    (ctx : _root_.Context)
    (q₁ q₂ : FPM_Phase7_CertifiedLocal)
    (hp : q₁.p = q₂.p)
    (h12 :
      ∀ x : FPM_Vector 2,
        (FPM_Phase7_LocalChart q₁).Mem x →
        (FPM_Phase7_LocalChart q₂).Mem x)
    (h21 :
      ∀ x : FPM_Vector 2,
        (FPM_Phase7_LocalChart q₂).Mem x →
        (FPM_Phase7_LocalChart q₁).Mem x) :
    (FPM_Phase7_TwoChartEnergyAtlas q₁ q₂ h12 h21).Compatible ctx := by
  exact FPM_Phase7_TwoChartEnergyAtlas_compatible ctx q₁ q₂ hp h12 h21

/-- Freeze theorem for 7.4:
if two certified local charts use the same physical parameters and include into
each other on overlaps, then force, acceleration, and energy agree across the
induced transition maps, and the resulting two-chart energy atlas is compatible. -/
theorem FPM_Phase7_two_chart_overlap_and_gluing_package
    (ctx : _root_.Context)
    (q₁ q₂ : FPM_Phase7_CertifiedLocal)
    (hp : q₁.p = q₂.p)
    (h12 : ∀ x : FPM_Vector 2, (FPM_Phase7_LocalChart q₁).Mem x → (FPM_Phase7_LocalChart q₂).Mem x)
    (h21 : ∀ x : FPM_Vector 2, (FPM_Phase7_LocalChart q₂).Mem x → (FPM_Phase7_LocalChart q₁).Mem x) :
    FPM_Sheaf_Overlap ctx
      (FPM_Phase7_ForceSection q₁)
      (FPM_Phase7_ForceSection q₂)
      (FPM_Phase7_TransitionOfInclusion q₁ q₂ h12) ∧
    FPM_Sheaf_Overlap ctx
      (FPM_Phase7_AccelerationSection q₁)
      (FPM_Phase7_AccelerationSection q₂)
      (FPM_Phase7_TransitionOfInclusion q₁ q₂ h12) ∧
    FPM_Sheaf_Overlap ctx
      (FPM_Phase7_EnergySection q₁)
      (FPM_Phase7_EnergySection q₂)
      (FPM_Phase7_TransitionOfInclusion q₁ q₂ h12) ∧
    (FPM_Phase7_TwoChartEnergyAtlas q₁ q₂ h12 h21).Compatible ctx := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact FPM_Phase7_ForceSection_overlap_of_same_params ctx q₁ q₂ hp h12
  · exact FPM_Phase7_AccelerationSection_overlap_of_same_params ctx q₁ q₂ hp h12
  · exact FPM_Phase7_EnergySection_overlap_of_same_params ctx q₁ q₂ hp h12
  · exact FPM_Phase7_TwoChartEnergyAtlas_compatible ctx q₁ q₂ hp h12 h21

/-!
  ------------------------------------------------------------------------
  SECTION 8 PHASE 7 SUMMARY PACKAGE
  ------------------------------------------------------------------------
-/

/-- End-of-phase summary:
Phase 7 provides local state-space encoding, certified local observables,
reflexive overlap stability, and two-chart gluing for the packaged energy field. -/
theorem FPM_Phase7_summary_package
    (ctx : _root_.Context)
    (q : FPM_Phase7_CertifiedLocal)
    (q₁ q₂ : FPM_Phase7_CertifiedLocal)
    (hp : q₁.p = q₂.p)
    (h12 : ∀ x : FPM_Vector 2, (FPM_Phase7_LocalChart q₁).Mem x → (FPM_Phase7_LocalChart q₂).Mem x)
    (h21 : ∀ x : FPM_Vector 2, (FPM_Phase7_LocalChart q₂).Mem x → (FPM_Phase7_LocalChart q₁).Mem x) :
    (FPM_Phase7_LocalChart q).Mem (FPM_Phase7_StateVec q.s) ∧
    FPM_Phase7_SurvivesArtifactFiltration
      ((FPM_Phase7_EnergySection q).field (FPM_Phase7_StateVec q.s))
      (q.p.Cmass * (q.Cvel * q.Cvel) + q.p.Cspring * (q.Cpos * q.Cpos)) ∧
    (FPM_Phase7_EnergySingleAtlas q).Compatible ctx ∧
    (FPM_Phase7_TwoChartEnergyAtlas q₁ q₂ h12 h21).Compatible ctx := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact FPM_Phase7_state_mem_local_chart q
  · exact FPM_Phase7_EnergySection_survives_at_state q
  · exact FPM_Phase7_EnergySingleAtlas_compatible ctx q
  · exact FPM_Phase7_TwoChartEnergyAtlas_compatible ctx q₁ q₂ hp h12 h21

end FPM_Phase7
