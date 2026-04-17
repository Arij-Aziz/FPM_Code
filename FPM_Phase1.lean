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
