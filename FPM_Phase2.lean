import Again.FPM_Phase1
import Mathlib

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
