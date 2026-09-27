import MatrixSpencer.KSFullManuscriptAffineData
import MatrixSpencer.KSFullManuscriptRegularizedSDP

/-!
# The numerical affine SDP objective and exact maximum

The objective coefficients are actual traces of the fixed coordinate matrices.
Every maximizing physical SDP triple has coordinates in this numerical pencil;
conversely every feasible coordinate point satisfies the original blocks.
Thus the exact maximum used in the ellipsoid correctness proof is the actual
regularized density potential.
-/

open Matrix
open scoped BigOperators InnerProductSpace MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSFullManuscriptAffineObjective

open KSFullManuscriptSDPCoordinates KSFullManuscriptAffineData KSFullManuscriptSDPIdentity
variable {n ι : Type*} [Fintype n] [LinearOrder n] [Fintype ι]

def coordinates (a : n) (x : Index a → ℝ) : Space a :=
  WithLp.toLp 2 (fun i => x ((KSCanonicalSDPIndex.chart a).symm i))

theorem entries_coordinates (a : n) (x : Index a → ℝ) : entries a (coordinates a x) = x := by
  funext p
  simp [entries, coordinates]

theorem dimension_eq (a : n) : dimension a = 4 * Fintype.card n ^ 2 - 1 := by
  have hn : 1 ≤ Fintype.card n := by letI : Nonempty n := ⟨a⟩; exact Fintype.card_pos
  have hcard : Fintype.card (KSFullManuscriptTraceCoordinates.Index a) = Fintype.card n * Fintype.card n - 1 := by
    simpa only [Fintype.card_prod, Fintype.card_unique] using Fintype.card_subtype_compl (fun p : n × n => p = (a, a))
  simp only [dimension, Index, Fintype.card_sum, hcard, Fintype.card_prod]
  have hsq : 1 ≤ Fintype.card n * Fintype.card n := Nat.mul_pos hn hn
  simp only [pow_two]
  omega

theorem dimension_gt_one (a : n) : 1 < dimension a := by
  have hn : 1 ≤ Fintype.card n := by letI : Nonempty n := ⟨a⟩; exact Fintype.card_pos
  rw [dimension_eq]
  have hsq : 1 ≤ Fintype.card n ^ 2 := one_le_pow₀ hn
  omega

def valueLinear (a : n) (H : Matrix n n ℂ) (θ : ℝ) : Space a →ₗ[ℝ] ℝ where
  toFun x := realTrace (H * ((densityLinear a (entries a x)) : Matrix n n ℂ)) +
    2 * realTrace (fidelityLinear a (entries a x)) + 2 * θ * realTrace ((regularizerLinear a (entries a x)) : Matrix n n ℂ)
  map_add' x y := by
    change realTrace (H * ((densityLinear a (entries a x + entries a y)) : Matrix n n ℂ)) +
      2 * realTrace (fidelityLinear a (entries a x + entries a y)) +
      2 * θ * realTrace ((regularizerLinear a (entries a x + entries a y)) : Matrix n n ℂ) = _
    simp only [map_add]
    change realTrace (H * ((densityLinear a (entries a x) : Matrix n n ℂ) + (densityLinear a (entries a y) : Matrix n n ℂ))) +
      2 * realTrace (fidelityLinear a (entries a x) + fidelityLinear a (entries a y)) +
      2 * θ * realTrace ((regularizerLinear a (entries a x) : Matrix n n ℂ) + (regularizerLinear a (entries a y) : Matrix n n ℂ)) = _
    simp only [Matrix.mul_add, realTrace_add]
    ring
  map_smul' r x := by
    change realTrace (H * ((densityLinear a (r • entries a x)) : Matrix n n ℂ)) +
      2 * realTrace (fidelityLinear a (r • entries a x)) +
      2 * θ * realTrace ((regularizerLinear a (r • entries a x)) : Matrix n n ℂ) = _
    simp only [map_smul]
    change realTrace (H * (r • (densityLinear a (entries a x) : Matrix n n ℂ))) +
      2 * realTrace (r • fidelityLinear a (entries a x)) +
      2 * θ * realTrace (r • (regularizerLinear a (entries a x) : Matrix n n ℂ)) = _
    simp only [Matrix.mul_smul, realTrace_smul, RingHom.id_apply, smul_eq_mul]
    ring

def coefficient (a : n) (H : Matrix n n ℂ) (θ : ℝ) : Space a :=
  WithLp.toLp 2 (fun i => valueLinear a H θ (unit a i))

def offset (H : Matrix n n ℂ) (θ : ℝ) (S₀ Y₀ : selfAdjoint (Matrix n n ℂ)) : ℝ :=
  value H θ S₀ Y₀ 0

theorem coefficient_inner (a : n) (H : Matrix n n ℂ) (θ : ℝ) (x : Space a) :
    ⟪coefficient a H θ, x⟫_ℝ = valueLinear a H θ x := by
  have hh := congrArg (valueLinear a H θ) (sum_units a x)
  simp only [map_sum, map_smul, smul_eq_mul] at hh
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  change (∑ i, x i * valueLinear a H θ (unit a i)) = _
  exact hh

theorem value_eq_affine (a : n) (H : Matrix n n ℂ) (θ : ℝ)
    (S₀ Y₀ : selfAdjoint (Matrix n n ℂ)) (x : Space a) :
    value H θ (density a S₀ (entries a x)) (regularizer a Y₀ (entries a x))
      (fidelityLinear a (entries a x)) = offset H θ S₀ Y₀ + ⟪coefficient a H θ, x⟫_ℝ := by
  rw [coefficient_inner]
  change realTrace (H * ((S₀ : Matrix n n ℂ) + (densityLinear a (entries a x) : Matrix n n ℂ))) +
    2 * realTrace (fidelityLinear a (entries a x)) +
    2 * θ * realTrace ((Y₀ : Matrix n n ℂ) + (regularizerLinear a (entries a x) : Matrix n n ℂ)) = _
  simp only [Matrix.mul_add, realTrace_add, offset, value, realTrace_zero, mul_zero, add_zero]
  dsimp [valueLinear]
  ring

/-- The explicit real affine pencil has a true maximum equal to the actual
regularized potential, with no geometric or numerical oracle hypothesis. -/
theorem exists_maximizer (a : n) (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (S₀ Y₀ : selfAdjoint (Matrix n n ℂ)) (htr : realTrace (S₀ : Matrix n n ℂ) = 1)
    {θ lam : ℝ} (hθ : 0 ≤ θ) (hlam : 0 < lam) :
    ∃ x : Space a, x ∈ KSFullManuscriptAffinePSD.target (data a B S₀ Y₀ lam) ∧
      offset H θ S₀ Y₀ + ⟪coefficient a H θ, x⟫_ℝ = KSFullManuscriptRegularizedSDP.potential H B θ lam ∧
      ∀ y ∈ KSFullManuscriptAffinePSD.target (data a B S₀ Y₀ lam),
        offset H θ S₀ Y₀ + ⟪coefficient a H θ, y⟫_ℝ ≤ offset H θ S₀ Y₀ + ⟪coefficient a H θ, x⟫_ℝ := by
  letI : Nonempty n := ⟨a⟩
  obtain ⟨S,Y,Z,hF,hval,hmax⟩ := KSFullManuscriptRegularizedSDP.regularized_SDP_exact H B hθ hlam
  let hs : selfAdjoint (Matrix n n ℂ) := ⟨S, (feasible_density hF).1.isHermitian⟩
  let hy : selfAdjoint (Matrix n n ℂ) := ⟨Y, hF.2.1.isHermitian⟩
  let x := coordinates a (encode a S₀ Y₀ hs hy Z)
  have hS : density a S₀ (entries a x) = hs := by
    rw [entries_coordinates]
    exact density_encode a S₀ Y₀ hs hy Z (hF.1.trans htr.symm)
  have hY : regularizer a Y₀ (entries a x) = hy := by
    rw [entries_coordinates]
    exact regularizer_encode a S₀ Y₀ hs hy Z
  have hZ : fidelityLinear a (entries a x) = Z := by
    rw [entries_coordinates]
    exact fidelity_encode a S₀ Y₀ hs hy Z
  have hx : x ∈ KSFullManuscriptAffinePSD.target (data a B S₀ Y₀ lam) := by
    rw [target_iff a B S₀ Y₀ htr, hS, hY, hZ]
    exact hF
  have hv : value H θ S Y Z = offset H θ S₀ Y₀ + ⟪coefficient a H θ, x⟫_ℝ := by
    have hh := value_eq_affine a H θ S₀ Y₀ x
    simpa only [hS, hY, hZ, hs, hy] using hh
  refine ⟨x,hx,hv.symm.trans hval, ?_⟩
  intro y hy'
  rw [← value_eq_affine, ← hv]
  exact hmax _ _ _ ((target_iff a B S₀ Y₀ htr lam y).mp hy')

end MatrixSpencer.KSFullManuscriptAffineObjective
