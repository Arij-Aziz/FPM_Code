import Again.FPM_Phase5_Execution
import Mathlib

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
