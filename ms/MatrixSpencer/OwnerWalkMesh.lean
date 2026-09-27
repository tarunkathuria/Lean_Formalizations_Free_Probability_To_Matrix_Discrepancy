import MatrixSpencer.FixedFaceSampler
import MatrixSpencer.PositiveCovarianceSampler
import MatrixSpencer.CoefficientSupportFrame

/-! Uniform meshes for the actual owner walk, indexed only by its current
coefficient subspace. -/
open Set Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace MatrixSpencer
noncomputable section
set_option maxHeartbeats 800000

/-- Shrinking the analytic mesh also bounds every coefficient displacement.
The added one in the denominator covers zero-dimensional coefficient spaces. -/
theorem exists_positive_mesh_with_rounding {δ b r : ℝ} (hδ : 0 < δ)
    (hb : 0 ≤ b) (hr : 0 < r) :
    ∃ m > 0, m ≤ δ ∧ m * b ≤ r := by
  refine ⟨min δ (r / (b + 1)), lt_min hδ (div_pos hr (by linarith)), min_le_left _ _, ?_⟩
  have hm : min δ (r / (b + 1)) ≤ r / (b + 1) := min_le_right _ _
  have hmul := (le_div_iff₀ (show 0 < b + 1 by linarith)).mp hm
  have hpos : 0 < min δ (r / (b + 1)) := lt_min hδ (div_pos hr (by linarith))
  nlinarith

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n]
local instance ownerWalkMeshCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance ownerWalkMeshPhysicalSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance

/-- The coefficient covariance cap bounds the Euclidean sampler displacement. -/
theorem covarianceSample_increment_norm_le_of_cap {Q : Matrix ι ι ℝ}
    (hQ : Q.PosSemidef) (hcap : Q ≤ 1) (s : ι × Bool) :
    ‖covarianceSampleIncrement hQ s‖ ≤ Real.sqrt (Fintype.card ι) := by
  have htr : realTrace Q ≤ (Fintype.card ι : ℝ) := by
    have h := realTrace_mul_mono Matrix.PosSemidef.one hcap
    simpa only [Matrix.one_mul, realTrace, Matrix.trace_one, RCLike.natCast_re] using h
  have hn : ‖covarianceSampleIncrement hQ s‖ = Real.sqrt (realTrace Q) := by
    rw [← covarianceSample_norm_sq hQ s, Real.sqrt_sq (norm_nonneg _)]
  rw [hn]
  exact Real.sqrt_le_sqrt htr

/-- The mesh rounding bound controls the full coefficient displacement, hence
also every individual coordinate. -/
theorem covarianceSample_step_norm_le {Q : Matrix ι ι ℝ}
    (hQ : Q.PosSemidef) (hcap : Q ≤ 1) {mesh r h : ℝ}
    (hround : mesh * Real.sqrt (Fintype.card ι) ≤ r) (hh : h ∈ Icc (0 : ℝ) mesh)
    (s : ι × Bool) : ‖h • covarianceSampleIncrement hQ s‖ ≤ r := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hh.1]
  exact (mul_le_mul_of_nonneg_left (covarianceSample_increment_norm_le_of_cap hQ hcap s) hh.1).trans
    ((mul_le_mul_of_nonneg_right hh.2 (Real.sqrt_nonneg _)).trans hround)

/-- Every retained sampler branch lies in the owner's actual coefficient range. -/
theorem positive_covarianceSample_mem_owner_range {C Q : Matrix ι ι ℝ}
    (hC : C.PosSemidef) (hQ : Q.PosSemidef) (hQC : Q ≤ C)
    (s : PositiveCovarianceOutcome hQ) : covarianceSampleIncrement hQ s ∈
      LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℝ) C).toLinearMap :=
  posSemidef_range_le_of_le hQ hC hQC (positive_covarianceSample_mem_range hQ s)

/-- The full displacement norm bound implies the required coordinate bound. -/
theorem covarianceSample_step_coordinate_le {Q : Matrix ι ι ℝ}
    (hQ : Q.PosSemidef) (hcap : Q ≤ 1) {mesh r h : ℝ}
    (hround : mesh * Real.sqrt (Fintype.card ι) ≤ r) (hh : h ∈ Icc (0 : ℝ) mesh)
    (s : ι × Bool) (i : ι) : |h * (covarianceSampleIncrement hQ s) i| ≤ r := by
  have hnorm := covarianceSample_step_norm_le hQ hcap hround hh s
  have hi := PiLp.norm_apply_le (h • covarianceSampleIncrement hQ s) i
  simpa only [PiLp.smul_apply, smul_eq_mul, Real.norm_eq_abs] using hi.trans hnorm

/-- The actual finite expected potential increment of a matched owner step. -/
def ownerSamplerDrift (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (θ : ℝ) (H : selfAdjoint (Matrix n n ℂ)) (C : Matrix ι ι ℝ)
    {Q : Matrix ι ι ℝ} (hQ : Q.PosSemidef) (h : ℝ) : ℝ :=
  ∑ s, covarianceSampleWeight hQ s *
    (ownerPotential (H + h • ownerPhysicalIncrement A hA (covarianceSampleIncrement hQ s)) A
      (C - h ^ 2 • Q) θ - ownerPotential H A C θ)

/-- Deleting zero-weight branches preserves the exact actual potential drift. -/
theorem positive_ownerSamplerDrift_eq (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (θ : ℝ) (H : selfAdjoint (Matrix n n ℂ))
    (C : Matrix ι ι ℝ) {Q : Matrix ι ι ℝ} (hQ : Q.PosSemidef)
    (htrace : 0 < realTrace Q) (h : ℝ) :
    (∑ s : PositiveCovarianceOutcome hQ, covarianceSampleWeight hQ s *
      (ownerPotential (H + h • ownerPhysicalIncrement A hA (covarianceSampleIncrement hQ s)) A
        (C - h ^ 2 • Q) θ - ownerPotential H A C θ)) = ownerSamplerDrift A hA θ H C hQ h := by
  simpa only [smul_eq_mul] using sum_positive_weight_smul (covarianceSampleWeight hQ)
    (covarianceSampleWeight_nonneg hQ htrace) (fun s =>
      ownerPotential (H + h • ownerPhysicalIncrement A hA (covarianceSampleIncrement hQ s)) A
        (C - h ^ 2 • Q) θ - ownerPotential H A C θ)

/-- A mesh indexed only by the actual coefficient support. All inputs to its
uniform drift bound are original-coordinate owner conditions: PSD, a unit
covariance cap, a Euclidean spectral floor on the range, and a bounded full
physical center. No reduced-chart or direction-bound assumption is required. -/
theorem exists_ownerWalkMesh [Nonempty n]
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) {θ : ℝ} (hθ : 0 < θ)
    (R : ℝ) {a error roundε : ℝ} (ha : 0 < a) (herror : 0 < error) (hround : 0 < roundε)
    (K : Submodule ℝ (EuclideanSpace ℝ ι)) :
    ∃ mesh > 0, mesh ≤ (1 / 2 : ℝ) ∧ mesh * Real.sqrt (Fintype.card ι) ≤ roundε ∧
      ∀ (H : selfAdjoint (Matrix n n ℂ)) (C : Matrix ι ι ℝ),
      ‖H‖ ≤ R → C.PosSemidef → C ≤ 1 →
      LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℝ) C).toLinearMap = K →
      (∀ u ∈ LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℝ) C).toLinearMap,
        a * ‖u‖ ^ 2 ≤ inner ℝ u (Matrix.toEuclideanCLM (𝕜 := ℝ) C u)) →
      ∀ (Q : Matrix ι ι ℝ) (hQ : Q.PosSemidef), Q ≤ C → 0 < realTrace Q →
      ∀ h ∈ Icc (0 : ℝ) mesh,
        ownerSamplerDrift A hA θ H C hQ h ≤
          h ^ 2 * realTrace (Q * ownerCoefficientResponse A hA C θ H) + error * h ^ 2 := by
  obtain ⟨δ, hδ, hδhalf, hb⟩ := uniform_owner_sampler_drift_on_fixedFace A hA
    (CoefficientSupportFrame.frame K) (CoefficientSupportFrame.frame_isometry K) hθ R ha herror
  obtain ⟨mesh, hm, hmδ, hmround⟩ := exists_positive_mesh_with_rounding hδ
    (Real.sqrt_nonneg (Fintype.card ι)) hround
  refine ⟨mesh, hm, hmδ.trans hδhalf, hmround, ?_⟩
  intro H C hH hC hcap hRange hfloor Q hQ hQC htrace h hh
  let Cred : selfAdjoint (Matrix (CoefficientSupportFrame.FrameIndex K)
      (CoefficientSupportFrame.FrameIndex K) ℝ) :=
    ⟨CoefficientSupportFrame.reduced K C, (CoefficientSupportFrame.reduced_posSemidef K hC).isHermitian⟩
  have hreconstruct : covarianceLift (CoefficientSupportFrame.frame K) (Cred : Matrix (CoefficientSupportFrame.FrameIndex K) (CoefficientSupportFrame.FrameIndex K) ℝ) = C :=
    CoefficientSupportFrame.reconstruct_of_range K hC.isHermitian hRange.le
  have hfloorK : ∀ u ∈ K,
      a * ‖u‖ ^ 2 ≤ inner ℝ u (Matrix.toEuclideanCLM (𝕜 := ℝ) C u) := by
    intro u hu
    apply hfloor u
    rwa [hRange]
  have hCredfloor : a • (1 : Matrix (CoefficientSupportFrame.FrameIndex K)
      (CoefficientSupportFrame.FrameIndex K) ℝ) ≤ (Cred : Matrix (CoefficientSupportFrame.FrameIndex K) (CoefficientSupportFrame.FrameIndex K) ℝ) :=
    CoefficientSupportFrame.reduced_floor_of_quadratic K hC.isHermitian hfloorK
  have hCredcap : (Cred : Matrix (CoefficientSupportFrame.FrameIndex K) (CoefficientSupportFrame.FrameIndex K) ℝ) ≤ 1 := CoefficientSupportFrame.reduced_le_one K hcap
  have hQCred : Q ≤ covarianceLift (CoefficientSupportFrame.frame K) (Cred : Matrix (CoefficientSupportFrame.FrameIndex K) (CoefficientSupportFrame.FrameIndex K) ℝ) := by
    rwa [hreconstruct]
  have hbound := hb H Cred hH hCredfloor hCredcap Q hQ hQCred htrace h ⟨hh.1, hh.2.trans hmδ⟩
  simpa only [hreconstruct] using hbound

end
end MatrixSpencer
