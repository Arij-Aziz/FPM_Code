import Again.FPM_Phase6_Topology
import Mathlib

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
