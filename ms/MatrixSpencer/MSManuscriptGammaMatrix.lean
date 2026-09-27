import MatrixSpencer.MSManuscriptGammaDifference
import MatrixSpencer.MSManuscriptGammaTop
import MatrixSpencer.KSMatrixEntryAccuracy

/-!
# Finite reconstruction of the supported covariance response

The diagonal queries are e_i e_iᵀ; mixed queries are
(e_i+e_j)(e_i+e_j)ᵀ/2. Their arithmetic polarization reconstructs the
response matrix. The entry and operator errors below include all three probe
errors, with no exact derivative evaluation in the report definition.
-/

open Matrix Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.MSManuscriptGammaMatrix
set_option maxHeartbeats 1200000
attribute [local irreducible] ownerPotential observedOwnedGram KSNumericalOwnerPotential.report
open KSRayleighAccuracy KSJacobiRayleigh MSManuscriptGammaDifference
variable {k d : ℕ}
local instance : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}

def basis (i : Fin k) : EuclideanSpace ℝ (Fin k) := EuclideanSpace.single i 1
def mixed (i j : Fin k) : EuclideanSpace ℝ (Fin k) :=
  (1/Real.sqrt 2) • (basis i+basis j)

theorem basis_norm (i : Fin k) : ‖basis i‖ = 1 := by simp [basis]
theorem mixed_swap (i j : Fin k) : mixed i j = mixed j i := by simp [mixed, add_comm]

theorem mixed_norm (i j : Fin k) (hij : i ≠ j) : ‖mixed i j‖ = 1 := by
  have he : inner ℝ (basis i) (basis j) = 0 := by
    simp [basis, EuclideanSpace.inner_single_left, EuclideanSpace.single_apply, hij]
  have hs : ‖basis i+basis j‖^2 = 2 := by
    rw [norm_add_sq_real, basis_norm, basis_norm, he]
    norm_num
  have hroot : 0 < Real.sqrt (2:ℝ) := by positivity
  have hn : ‖basis i+basis j‖ = Real.sqrt 2 := by
    nlinarith [norm_nonneg (basis i+basis j), Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
  rw [mixed, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos zero_lt_one hroot), hn]
  exact div_mul_cancel₀ 1 (ne_of_gt hroot)

theorem rayleigh_basis (G : Matrix (Fin k) (Fin k) ℝ) (i : Fin k) :
    realRayleigh G (basis i) = G i i := realRayleigh_single G i

theorem rayleigh_sum_basis (G : Matrix (Fin k) (Fin k) ℝ) (i j : Fin k) :
    realRayleigh G (basis i+basis j) = G i i+G i j+G j i+G j j := by
  rw [realRayleigh_eq_quadratic]
  simp [basis, WithLp.ofLp_add, EuclideanSpace.ofLp_single, add_dotProduct,
    Matrix.mulVec_add, dotProduct_add, single_dotProduct, Matrix.mulVec_single_one]
  ring

theorem rayleigh_mixed (G : Matrix (Fin k) (Fin k) ℝ) (hG : G.IsSymm) (i j : Fin k) :
    realRayleigh G (mixed i j) = (G i i+G j j)/2+G i j := by
  rw [mixed, MSManuscriptGammaTop.rayleigh_smul_vector, rayleigh_sum_basis]
  have he : G j i = G i j := congrFun (congrFun hG i) j
  have hr : Real.sqrt (2:ℝ)^2 = 2 := Real.sq_sqrt (by norm_num)
  rw [he, div_pow, one_pow, hr]
  ring

def reconstruct (q : EuclideanSpace ℝ (Fin k) → ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  fun i j => if i=j then q (basis i) else q (mixed i j)-(q (basis i)+q (basis j))/2

theorem reconstruct_isSymm (q : EuclideanSpace ℝ (Fin k) → ℝ) : (reconstruct q).IsSymm := by
  ext i j
  by_cases hij : i=j
  · subst j
    rfl
  · simp [reconstruct, hij, Ne.symm hij, mixed_swap j i, add_comm]

theorem reconstruct_entry_error (G : Matrix (Fin k) (Fin k) ℝ) (hG : G.IsSymm)
    (q : EuclideanSpace ℝ (Fin k) → ℝ) {η : ℝ} (hη : 0 ≤ η)
    (hq : ∀ u, ‖u‖=1 → |q u-realRayleigh G u| ≤ η) :
    ∀ i j, |G i j-reconstruct q i j| ≤ 2*η := by
  intro i j
  have hi := hq (basis i) (basis_norm i)
  rw [rayleigh_basis] at hi
  by_cases hij : i=j
  · subst j
    simpa only [reconstruct, if_pos rfl, abs_sub_comm] using hi.trans (by linarith : η≤2*η)
  · have hj := hq (basis j) (basis_norm j)
    rw [rayleigh_basis] at hj
    have hm := hq (mixed i j) (mixed_norm i j hij)
    rw [rayleigh_mixed G hG] at hm
    rw [reconstruct, if_neg hij]
    rcases abs_le.mp hi with ⟨hil,hiu⟩
    rcases abs_le.mp hj with ⟨hjl,hju⟩
    rcases abs_le.mp hm with ⟨hml,hmu⟩
    apply abs_le.mpr
    constructor <;> linarith

theorem reconstruct_operator_error (G : Matrix (Fin k) (Fin k) ℝ) (hG : G.IsSymm)
    (q : EuclideanSpace ℝ (Fin k) → ℝ) {η : ℝ} (hη : 0 ≤ η)
    (hq : ∀ u, ‖u‖=1 → |q u-realRayleigh G u| ≤ η) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (G-reconstruct q)‖ ≤ (k:ℝ)*(2*η) :=
  KSMatrixEntryAccuracy.operatorNorm_le_card_mul _ (by positivity)
    (reconstruct_entry_error G hG q hη hq)

/-- The response report uses the actual one-sided numerical owner-value queries. -/
def report (H : Matrix (Fin d) (Fin d) ℂ) (A : Fin k → Matrix (Fin d) (Fin d) ℂ)
    (C : Matrix (Fin k) (Fin k) ℝ) (θ : ℝ) (hd : 0 < d) (δ L η : ℝ) :
    Matrix (Fin k) (Fin k) ℝ :=
  reconstruct (probe H A C θ hd (stepSize δ L η) (valueTolerance δ L η))

theorem report_isSymm (H : Matrix (Fin d) (Fin d) ℂ) (A : Fin k → Matrix (Fin d) (Fin d) ℂ)
    (C : Matrix (Fin k) (Fin k) ℝ) (θ : ℝ) (hd : 0 < d) (δ L η : ℝ) :
    (report H A C θ hd δ L η).IsSymm := reconstruct_isSymm _

/-- Quantitative segment hypotheses for the actual finite-difference queries.
These remain analytic obligations until a supported-floor curvature bound is supplied. -/
def QuerySegments (H : Matrix (Fin d) (Fin d) ℂ)
    (A : Fin k → Matrix (Fin d) (Fin d) ℂ) (C : Matrix (Fin k) (Fin k) ℝ)
    (θ s L : ℝ) : Prop :=
  ∀ u : EuclideanSpace ℝ (Fin k), ‖u‖ = 1 →
    u ∈ LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℝ) C).toLinearMap ∧
    (C-s • realRankOne (WithLp.ofLp u)).PosSemidef ∧
    ContDiffOn ℝ 2 (curve H A C θ u) (Icc 0 s) ∧
    ∀ a ∈ Ioo 0 s, |iteratedDeriv 2 (curve H A C θ u) a| ≤ L

theorem report_accuracy [Nonempty (Fin d)]
    (H : selfAdjoint (Matrix (Fin d) (Fin d) ℂ))
    (A : Fin k → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C : Matrix (Fin k) (Fin k) ℝ} (hC : C.PosSemidef)
    {θ δ L η : ℝ} (hθ : 0 < θ) (hδ : 0 < δ) (hL : 0 ≤ L) (hη : 0 < η)
    (hd : 0 < d)
    (hsegments : QuerySegments (H : Matrix (Fin d) (Fin d) ℂ) A C θ (stepSize δ L η) L) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ)
      (observedOwnedGram H A C θ-report (H : Matrix (Fin d) (Fin d) ℂ) A C θ hd δ L η)‖ ≤
        (k : ℝ)*(2*η) := by
  have hsymm : (observedOwnedGram H A C θ).IsSymm := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (observedOwnedGram_posSemidef H A hA C hθ).isHermitian.eq
  apply reconstruct_operator_error _ hsymm _ hη.le
  intro u hu
  obtain ⟨hrange,hpsd,hcurve,hcurvature⟩ := hsegments u hu
  have h := probe_accuracy H A hA hC u hrange hθ (stepSize_pos hδ hL hη)
    (valueTolerance_pos hδ hL hη) hd hpsd hcurve hcurvature
  rw [realRayleigh_eq_quadratic]
  exact h.trans (error_budget hδ hL hη)


def topPrecision (k : ℕ) (t : ℝ) : ℝ := t/(128*(k : ℝ))

theorem topPrecision_pos {t : ℝ} (hk : 0 < k) (ht : 0 < t) :
    0 < topPrecision k t := by unfold topPrecision; positivity

theorem topPrecision_budget {t : ℝ} (hk : 0 < k) :
    (k : ℝ)*(2*topPrecision k t) = t/64 := by
  have hn : (k : ℝ) ≠ 0 := (Nat.cast_pos.mpr hk).ne'
  unfold topPrecision
  field_simp
  <;> ring

end MatrixSpencer.MSManuscriptGammaMatrix
