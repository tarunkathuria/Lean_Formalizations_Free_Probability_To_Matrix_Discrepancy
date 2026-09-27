import MatrixSpencer.DyadicSDPCoordinates
import MatrixSpencer.DyadicOwnerSDPIdentity

/-!
# Explicit affine objective and exact coordinate maximizer

The coefficients are the real traces of the actual coordinate matrices.
Every feasible physical SDP triple is represented by these coordinates,
including singular density and auxiliary matrices. Consequently the affine
coordinate objective has an attained maximum equal to the actual dyadic
owner potential. No oracle or matrix-power evaluation is used to define
the objective coefficients or coordinate maps.
-/

open Matrix Set
open scoped BigOperators InnerProductSpace MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.DyadicSDPAffineObjective

open DyadicSDPCoordinates
variable {n ι : Type*} [Fintype n] [LinearOrder n] [Fintype ι]

def valueLinear (m : ℕ) (a : n) (H : Matrix n n ℂ) (θ : ℝ) : Space m a →ₗ[ℝ] ℝ where
  toFun x := realTrace (H * (densityLinear m a (entries m a x) : Matrix n n ℂ)) +
    2 * realTrace (fidelityLinear m a (entries m a x)) +
    (θ * (2 ^ m : ℝ) / ((2 ^ m : ℝ) - 1)) *
      realTrace (chainLinear m a (Fin.last m) (entries m a x))
  map_add' x y := by
    change realTrace (H * (densityLinear m a (entries m a x + entries m a y) : Matrix n n ℂ)) +
      2 * realTrace (fidelityLinear m a (entries m a x + entries m a y)) +
      (θ * (2 ^ m : ℝ) / ((2 ^ m : ℝ) - 1)) *
        realTrace (chainLinear m a (Fin.last m) (entries m a x + entries m a y)) = _
    simp only [map_add]
    change realTrace (H * ((densityLinear m a (entries m a x) : Matrix n n ℂ) +
      (densityLinear m a (entries m a y) : Matrix n n ℂ))) +
      2 * realTrace (fidelityLinear m a (entries m a x) + fidelityLinear m a (entries m a y)) +
      (θ * (2 ^ m : ℝ) / ((2 ^ m : ℝ) - 1)) *
        realTrace (chainLinear m a (Fin.last m) (entries m a x) +
          chainLinear m a (Fin.last m) (entries m a y)) = _
    simp only [Matrix.mul_add, realTrace_add]
    ring
  map_smul' r x := by
    change realTrace (H * (densityLinear m a (r • entries m a x) : Matrix n n ℂ)) +
      2 * realTrace (fidelityLinear m a (r • entries m a x)) +
      (θ * (2 ^ m : ℝ) / ((2 ^ m : ℝ) - 1)) *
        realTrace (chainLinear m a (Fin.last m) (r • entries m a x)) = _
    simp only [map_smul]
    change realTrace (H * (r • (densityLinear m a (entries m a x) : Matrix n n ℂ))) +
      2 * realTrace (r • fidelityLinear m a (entries m a x)) +
      (θ * (2 ^ m : ℝ) / ((2 ^ m : ℝ) - 1)) *
        realTrace (r • chainLinear m a (Fin.last m) (entries m a x)) = _
    simp only [Matrix.mul_smul, realTrace_smul, RingHom.id_apply, smul_eq_mul]
    ring

def coefficient (m : ℕ) (a : n) (H : Matrix n n ℂ) (θ : ℝ) : Space m a :=
  WithLp.toLp 2 (fun i => valueLinear m a H θ (unit m a i))

def offset (m : ℕ) (a : n) (H : Matrix n n ℂ) (θ : ℝ)
    (S₀ : selfAdjoint (Matrix n n ℂ)) : ℝ :=
  DyadicOwnerSDPIdentity.value H m θ S₀ (chain m a 0) 0

def objective (m : ℕ) (a : n) (H : Matrix n n ℂ) (θ : ℝ)
    (S₀ : selfAdjoint (Matrix n n ℂ)) (x : Space m a) : ℝ :=
  offset m a H θ S₀ + ⟪coefficient m a H θ, x⟫_ℝ

omit [Fintype ι] in
theorem coefficient_inner (m : ℕ) (a : n) (H : Matrix n n ℂ) (θ : ℝ) (x : Space m a) :
    ⟪coefficient m a H θ, x⟫_ℝ = valueLinear m a H θ x := by
  have hh := congrArg (valueLinear m a H θ) (sum_units m a x)
  simp only [map_sum, map_smul, smul_eq_mul] at hh
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  change (∑ i, x i * valueLinear m a H θ (unit m a i)) = _
  exact hh

omit [Fintype ι] in
theorem value_eq_affine (m : ℕ) (a : n) (H : Matrix n n ℂ) (θ : ℝ)
    (S₀ : selfAdjoint (Matrix n n ℂ)) (x : Space m a) :
    DyadicOwnerSDPIdentity.value H m θ (density m a S₀ (entries m a x))
      (chain m a (entries m a x)) (fidelityLinear m a (entries m a x)) =
      objective m a H θ S₀ x := by
  have hc := chain_affine m a 0 (entries m a x) (Fin.last m)
  rw [zero_add] at hc
  rw [objective, coefficient_inner]
  change realTrace (H * ((S₀ : Matrix n n ℂ) +
      (densityLinear m a (entries m a x) : Matrix n n ℂ))) +
    2 * realTrace (fidelityLinear m a (entries m a x)) +
    (θ * (2 ^ m : ℝ) / ((2 ^ m : ℝ) - 1)) *
      realTrace (chain m a (entries m a x) (Fin.last m)) = _
  rw [hc]
  simp only [Matrix.mul_add, realTrace_add, offset, DyadicOwnerSDPIdentity.value,
    realTrace_zero, mul_zero, add_zero]
  dsimp [valueLinear]
  ring

/-- Coordinate feasibility for exactly the original matrix constraints. -/
def target (m : ℕ) (a : n) (Ω : Matrix n n ℂ → Matrix n n ℂ)
    (S₀ : selfAdjoint (Matrix n n ℂ)) : Set (Space m a) :=
  {x | DyadicOwnerSDPIdentity.Feasible Ω m (density m a S₀ (entries m a x))
    (chain m a (entries m a x)) (fidelityLinear m a (entries m a x))}

omit [Fintype ι] in
/-- The real coordinates cover every physically feasible triple. -/
theorem feasible_onto (m : ℕ) (a : n) (Ω : Matrix n n ℂ → Matrix n n ℂ)
    (S₀ : selfAdjoint (Matrix n n ℂ)) (htr : realTrace (S₀ : Matrix n n ℂ) = 1)
    {S : Matrix n n ℂ} {X : Fin (m + 1) → Matrix n n ℂ} {Z : Matrix n n ℂ}
    (hf : DyadicOwnerSDPIdentity.Feasible Ω m S X Z) :
    ∃ x : Space m a, x ∈ target m a Ω S₀ ∧
      (density m a S₀ (entries m a x) : Matrix n n ℂ) = S ∧
      chain m a (entries m a x) = X ∧ fidelityLinear m a (entries m a x) = Z := by
  let hs : selfAdjoint (Matrix n n ℂ) := ⟨S, hf.1.1.isHermitian⟩
  let hx : Fin m → selfAdjoint (Matrix n n ℂ) := fun j =>
    ⟨X j.succ, (hf.2.1.2 j).1.isHermitian⟩
  let x := coordinates m a (encode m a S₀ hs hx Z)
  have hS : density m a S₀ (entries m a x) = hs := by
    rw [entries_coordinates]
    exact density_encode m a S₀ hs hx Z (hf.1.2.trans htr.symm)
  have hX : chain m a (entries m a x) = X := by
    funext j
    refine Fin.cases ?_ (fun k => ?_) j
    · exact (chain_zero m a _).trans hf.2.1.1.symm
    · rw [chain_succ, entries_coordinates, auxiliary_encode]
  have hZ : fidelityLinear m a (entries m a x) = Z := by
    rw [entries_coordinates]
    exact fidelity_encode m a S₀ hs hx Z
  refine ⟨x, ?_, ?_, hX, hZ⟩
  · change DyadicOwnerSDPIdentity.Feasible Ω m _ _ _
    rw [hS, hX, hZ]
    exact hf
  · exact congrArg Subtype.val hS

def values (m : ℕ) (a : n) (H : Matrix n n ℂ) (Ω : Matrix n n ℂ → Matrix n n ℂ)
    (θ : ℝ) (S₀ : selfAdjoint (Matrix n n ℂ)) : Set ℝ :=
  objective m a H θ S₀ '' target m a Ω S₀

omit [Fintype ι] in
/-- The affine coordinate SDP and physical SDP have exactly the same set of
feasible objective values, rather than just a common supremum. -/
theorem values_eq (m : ℕ) (a : n) (H : Matrix n n ℂ)
    (Ω : Matrix n n ℂ → Matrix n n ℂ) (θ : ℝ)
    (S₀ : selfAdjoint (Matrix n n ℂ)) (htr : realTrace (S₀ : Matrix n n ℂ) = 1) :
    values m a H Ω θ S₀ = DyadicOwnerSDPIdentity.values H Ω m θ := by
  ext v
  constructor
  · rintro ⟨x, hx, hv⟩
    refine ⟨density m a S₀ (entries m a x), chain m a (entries m a x),
      fidelityLinear m a (entries m a x), hx, ?_⟩
    exact (value_eq_affine m a H θ S₀ x).trans hv
  · rintro ⟨S, X, Z, hf, hv⟩
    obtain ⟨x, hx, hS, hX, hZ⟩ := feasible_onto m a Ω S₀ htr hf
    refine ⟨x, hx, ?_⟩
    rw [← value_eq_affine, hS, hX, hZ]
    exact hv

section Covariance

variable [DecidableEq ι]

/-- The affine coordinate problem has a true maximizer equal to the original
dyadic covariance-owner potential. -/
theorem owner_exists_maximizer (m : ℕ) (a : n) (H : Matrix n n ℂ)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef)
    (S₀ : selfAdjoint (Matrix n n ℂ)) (htr : realTrace (S₀ : Matrix n n ℂ) = 1)
    (hm : 1 ≤ m) {θ : ℝ} (hθ : 0 < θ) :
    ∃ x : Space m a, x ∈ target m a (covarianceSource A C) S₀ ∧
      objective m a H θ S₀ x = dyadicOwnerPotential H A C m θ ∧
      ∀ y ∈ target m a (covarianceSource A C) S₀,
        objective m a H θ S₀ y ≤ objective m a H θ S₀ x := by
  letI : Nonempty n := ⟨a⟩
  obtain ⟨S, X, Z, hf, hv, hmax⟩ := DyadicOwnerSDPIdentity.owner_SDP_exact H A hA hC hm hθ
  obtain ⟨x, hx, hS, hX, hZ⟩ := feasible_onto m a (covarianceSource A C) S₀ htr hf
  have he : objective m a H θ S₀ x = DyadicOwnerSDPIdentity.value H m θ S X Z := by
    rw [← value_eq_affine, hS, hX, hZ]
  refine ⟨x, hx, he.trans hv, ?_⟩
  intro y hy
  rw [he, ← value_eq_affine]
  exact hmax _ _ _ hy

theorem owner_isGreatest (m : ℕ) (a : n) (H : Matrix n n ℂ)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef)
    (S₀ : selfAdjoint (Matrix n n ℂ)) (htr : realTrace (S₀ : Matrix n n ℂ) = 1)
    (hm : 1 ≤ m) {θ : ℝ} (hθ : 0 < θ) :
    IsGreatest (values m a H (covarianceSource A C) θ S₀) (dyadicOwnerPotential H A C m θ) := by
  letI : Nonempty n := ⟨a⟩
  rw [values_eq m a H _ θ S₀ htr]
  exact DyadicOwnerSDPIdentity.owner_isGreatest H A hA hC hm hθ

theorem owner_sSup_eq (m : ℕ) (a : n) (H : Matrix n n ℂ)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef)
    (S₀ : selfAdjoint (Matrix n n ℂ)) (htr : realTrace (S₀ : Matrix n n ℂ) = 1)
    (hm : 1 ≤ m) {θ : ℝ} (hθ : 0 < θ) :
    sSup (values m a H (covarianceSource A C) θ S₀) = dyadicOwnerPotential H A C m θ :=
  (owner_isGreatest m a H A hA hC S₀ htr hm hθ).csSup_eq

end Covariance

end MatrixSpencer.DyadicSDPAffineObjective
