import Again.FPM_Phase6_Linear
import Mathlib

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
