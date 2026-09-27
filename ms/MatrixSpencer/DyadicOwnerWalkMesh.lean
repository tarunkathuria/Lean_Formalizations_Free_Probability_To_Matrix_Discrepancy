import MatrixSpencer.OwnerWalkMesh
import MatrixSpencer.DyadicFixedFaceSampler

/-! A uniform actual dyadic owner mesh indexed only by the current coefficient support. -/
open Set Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace MatrixSpencer
noncomputable section
set_option maxHeartbeats 800000
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n]
local instance dyadicWalkMeshCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance dyadicWalkMeshPhysicalSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance

/-- The actual finite expected potential increment of a matched owner step. -/
def dyadicOwnerSamplerDrift (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (m : ℕ) (θ : ℝ) (H : selfAdjoint (Matrix n n ℂ)) (C : Matrix ι ι ℝ)
    {Q : Matrix ι ι ℝ} (hQ : Q.PosSemidef) (h : ℝ) : ℝ :=
  ∑ s, covarianceSampleWeight hQ s *
    (dyadicOwnerPotential (H + h • ownerPhysicalIncrement A hA (covarianceSampleIncrement hQ s)) A
      (C - h ^ 2 • Q) m θ - dyadicOwnerPotential H A C m θ)

/-- Deleting zero-weight branches preserves the exact actual potential drift. -/
theorem positive_dyadicOwnerSamplerDrift_eq (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (m : ℕ) (θ : ℝ) (H : selfAdjoint (Matrix n n ℂ))
    (C : Matrix ι ι ℝ) {Q : Matrix ι ι ℝ} (hQ : Q.PosSemidef)
    (htrace : 0 < realTrace Q) (h : ℝ) :
    (∑ s : PositiveCovarianceOutcome hQ, covarianceSampleWeight hQ s *
      (dyadicOwnerPotential (H + h • ownerPhysicalIncrement A hA (covarianceSampleIncrement hQ s)) A
        (C - h ^ 2 • Q) m θ - dyadicOwnerPotential H A C m θ)) = dyadicOwnerSamplerDrift A hA m θ H C hQ h := by
  simpa only [smul_eq_mul] using sum_positive_weight_smul (covarianceSampleWeight hQ)
    (covarianceSampleWeight_nonneg hQ htrace) (fun s =>
      dyadicOwnerPotential (H + h • ownerPhysicalIncrement A hA (covarianceSampleIncrement hQ s)) A
        (C - h ^ 2 • Q) m θ - dyadicOwnerPotential H A C m θ)

/-- A mesh indexed only by the actual coefficient support. All inputs to its
uniform drift bound are original-coordinate owner conditions: PSD, a unit
covariance cap, a Euclidean spectral floor on the range, and a bounded full
physical center. No reduced-chart or direction-bound assumption is required. -/
theorem exists_dyadicOwnerWalkMesh [Nonempty n]
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (hθ : 0 < θ)
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
        dyadicOwnerSamplerDrift A hA m θ H C hQ h ≤
          h ^ 2 * realTrace (Q * dyadicOwnerCoefficientResponse A hA C m θ H) + error * h ^ 2 := by
  obtain ⟨δ, hδ, hδhalf, hb⟩ := uniform_dyadicOwner_sampler_drift_on_fixedFace A hA
    (CoefficientSupportFrame.frame K) (CoefficientSupportFrame.frame_isometry K) m hm θ hθ R ha herror
  obtain ⟨mesh, hmesh, hmδ, hmround⟩ := exists_positive_mesh_with_rounding hδ
    (Real.sqrt_nonneg (Fintype.card ι)) hround
  refine ⟨mesh, hmesh, hmδ.trans hδhalf, hmround, ?_⟩
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
