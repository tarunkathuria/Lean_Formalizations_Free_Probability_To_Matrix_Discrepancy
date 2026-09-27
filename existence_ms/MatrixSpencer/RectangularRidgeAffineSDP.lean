import MatrixSpencer.RectangularRidgeSDP
import MatrixSpencer.DyadicOwnerSDP

/-! The ridge potential as an explicit affine real SDP. The constraints and
their polynomial size are literally those of the existing dyadic SDP; only
the objective coefficient of its first auxiliary trace changes. -/
open Matrix Set
open scoped BigOperators InnerProductSpace MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.RectangularRidgeAffineSDP
open DyadicSDPCoordinates
variable {n ι : Type*} [Fintype n] [LinearOrder n] [Fintype ι] [DecidableEq ι]

def ridgeLinear (m : ℕ) (hm : 1 ≤ m) (a : n) (κ : ℝ) : Space m a →ₗ[ℝ] ℝ where
  toFun x := 2 * κ * realTrace (chainLinear m a ⟨1, by omega⟩ (entries m a x))
  map_add' x y := by
    change 2 * κ * realTrace (chainLinear m a ⟨1, by omega⟩
      (entries m a x + entries m a y)) = _
    simp only [map_add, realTrace_add]
    ring
  map_smul' r x := by
    change 2 * κ * realTrace (chainLinear m a ⟨1, by omega⟩ (r • entries m a x)) = _
    simp only [map_smul, realTrace_smul, RingHom.id_apply, smul_eq_mul]
    ring

def valueLinear (m : ℕ) (hm : 1 ≤ m) (a : n) (H : Matrix n n ℂ) (θ κ : ℝ) :
    Space m a →ₗ[ℝ] ℝ :=
  DyadicSDPAffineObjective.valueLinear m a H θ + ridgeLinear m hm a κ

def coefficient (m : ℕ) (hm : 1 ≤ m) (a : n) (H : Matrix n n ℂ) (θ κ : ℝ) : Space m a :=
  WithLp.toLp 2 (fun i => valueLinear m hm a H θ κ (unit m a i))

def offset (m : ℕ) (hm : 1 ≤ m) (a : n) (H : Matrix n n ℂ) (θ κ : ℝ) : ℝ :=
  RectangularRidgeSDP.value H m θ κ hm (DyadicOwnerSDP.center a) (chain m a 0) 0

def objective (m : ℕ) (hm : 1 ≤ m) (a : n) (H : Matrix n n ℂ) (θ κ : ℝ)
    (x : Space m a) : ℝ := offset m hm a H θ κ + ⟪coefficient m hm a H θ κ, x⟫_ℝ

omit [Fintype ι] [DecidableEq ι] in
theorem coefficient_inner (m : ℕ) (hm : 1 ≤ m) (a : n) (H : Matrix n n ℂ)
    (θ κ : ℝ) (x : Space m a) :
    ⟪coefficient m hm a H θ κ, x⟫_ℝ = valueLinear m hm a H θ κ x := by
  have hh := congrArg (valueLinear m hm a H θ κ) (sum_units m a x)
  simp only [map_sum, map_smul, smul_eq_mul] at hh
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  change (∑ i, x i * valueLinear m hm a H θ κ (unit m a i)) = _
  exact hh

omit [Fintype ι] [DecidableEq ι] in
theorem value_eq_affine (m : ℕ) (hm : 1 ≤ m) (a : n) (H : Matrix n n ℂ)
    (θ κ : ℝ) (x : Space m a) :
    RectangularRidgeSDP.value H m θ κ hm
      (density m a (DyadicOwnerSDP.center a) (entries m a x))
      (chain m a (entries m a x)) (fidelityLinear m a (entries m a x)) =
      objective m hm a H θ κ x := by
  have hc := chain_affine m a 0 (entries m a x) (⟨1, by omega⟩ : Fin (m+1))
  rw [zero_add] at hc
  rw [RectangularRidgeSDP.value, DyadicSDPAffineObjective.value_eq_affine,
    objective, coefficient_inner, hc]
  simp only [realTrace_add, DyadicSDPAffineObjective.objective,
    DyadicSDPAffineObjective.coefficient_inner, offset, RectangularRidgeSDP.value,
    valueLinear, LinearMap.add_apply, ridgeLinear, LinearMap.coe_mk, AddHom.coe_mk]
  dsimp [DyadicSDPAffineObjective.offset]
  ring

/-- The affine real SDP exactly attains the ridge potential at its own
optimizer, with no full-rank premise on the covariance. -/
theorem exists_maximizer (m : ℕ) (hm : 1 ≤ m) (a : n) (H : Matrix n n ℂ)
    (A : ι → Matrix n n ℂ) (hA : ∀i, (A i).IsHermitian)
    (C : Matrix ι ι ℝ) (hC : C.PosSemidef) {θ κ : ℝ} (hθ : 0 < θ) (hκ : 0 ≤ κ) :
    ∃ x : Space m a, x ∈ DyadicOwnerSDP.feasible m a A hA C hC ∧
      objective m hm a H θ κ x =
        RectangularRidgePotential.potential H (covarianceKraus A C) m θ κ ∧
      ∀ y ∈ DyadicOwnerSDP.feasible m a A hA C hC,
        objective m hm a H θ κ y ≤ objective m hm a H θ κ x := by
  letI : Nonempty n := ⟨a⟩
  obtain ⟨S, X, Z, hf, hv, hmax⟩ := RectangularRidgeSDP.SDP_exact H
    (covarianceKraus A C) hm hθ hκ
  have hf' := (DyadicOwnerSDPIdentity.covariance_feasible_iff A hA hC).mpr hf
  obtain ⟨x, hx, hS, hX, hZ⟩ := DyadicSDPAffineObjective.feasible_onto m a
    (covarianceSource A C) (DyadicOwnerSDP.center a) (DyadicOwnerSDP.center_trace a) hf'
  have he : objective m hm a H θ κ x = RectangularRidgeSDP.value H m θ κ hm S X Z := by
    rw [← value_eq_affine, hS, hX, hZ]
  refine ⟨x, ?_, he.trans hv, ?_⟩
  · rwa [DyadicOwnerSDP.feasible_eq]
  · intro y hy
    rw [DyadicOwnerSDP.feasible_eq] at hy
    rw [← value_eq_affine, he]
    exact hmax _ _ _ ((DyadicOwnerSDPIdentity.covariance_feasible_iff A hA hC).mp hy)

end MatrixSpencer.RectangularRidgeAffineSDP
