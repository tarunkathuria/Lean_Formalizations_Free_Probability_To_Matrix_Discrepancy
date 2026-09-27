import MatrixSpencer.RealRAMMSCovariance
import MatrixSpencer.MSManuscriptNumericalEpochLedger

/-! The sampler's eigendecomposition acts on an explicitly computed matrix:
twice the materialized walk covariance is the legal high-space projection.
Thus the finite uniform draw uses exactly the computed EVD frame. -/
open Matrix
open scoped BigOperators MatrixOrder
noncomputable section
namespace SimpleMS.MaterializedFrame
open MatrixSpencer
open MSManuscriptNumericalEpochLedger (State samplingSpace)
variable {N : ℕ}

def computedCovariance (s : State N) :=
  RealRAM.MSCovariance.covariance (RealRAM.MSGammaTop.physical s.owner).value s.point

lemma projection_value (s : State N) :
    (2:ℝ) • (computedCovariance s).value = euclideanProjectionMatrix (samplingSpace s) := by
  rw [computedCovariance,RealRAM.MSGammaTop.physical_value,RealRAM.MSCovariance.covariance_value]
  change (2:ℝ) • ((1/2:ℝ) • euclideanProjectionMatrix (samplingSpace s)) = _
  norm_num [smul_smul]

/-- The spectral frame used by the actual sampler is an exact-EVD output on
the matrix computed from the owner's stored entries. -/
theorem frame_evd_execution (s : State N) :
    ∃hP : ((2:ℝ) • (computedCovariance s).value).IsHermitian,
      CountedSpectralSampler.EVDExecutes ((2:ℝ) • (computedCovariance s).value) hP
        (SpectralFrame.hermitian (samplingSpace s)).eigenvalues
        (SpectralFrame.hermitian (samplingSpace s)).eigenvectorUnitary 1 := by
  rw [projection_value]
  exact ⟨SpectralFrame.hermitian (samplingSpace s),.evd⟩

/-- Every retained column has eigenvalue one, so its two signs have exactly
the same mass as those of every other retained column. -/
theorem retained_columns_equal_weight (s : State N) (a b : UniformSampler.Draws (samplingSpace s)) :
    (SpectralFrame.hermitian (samplingSpace s)).eigenvalues a.1.val = 1 ∧
    UniformSampler.weight (samplingSpace s) a = UniformSampler.weight (samplingSpace s) b :=
  ⟨SpectralFrame.eigenvalue_eq_one _ _,rfl⟩

end SimpleMS.MaterializedFrame
