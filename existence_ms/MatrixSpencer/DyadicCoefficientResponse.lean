import MatrixSpencer.DyadicPotentialResponse
import MatrixSpencer.OwnerResponseGeometry

/-! The coefficient response is half of the actual dyadic potential Hessian. -/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
namespace MatrixSpencer
noncomputable section
set_option maxHeartbeats 800000
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n]
local instance dyadicCoefficientCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance dyadicCoefficientSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance

def dyadicKrausObservedResponse (H : selfAdjoint (Matrix n n ℂ))
    (B : ι → Matrix n n ℂ) (hB : ∀ a, (B a).IsHermitian) (m : ℕ) (θ : ℝ) : ℝ :=
  (2 : ℝ)⁻¹ * ∑ a, fderiv ℝ (fun K => fderiv ℝ (hermitianDyadicDensityPotential B m θ) K) H
    (hermitianMatrixFamily B hB a) (hermitianMatrixFamily B hB a)

def dyadicOwnerPotentialAsCenter (A : ι → Matrix n n ℂ) (C : Matrix ι ι ℝ) (m : ℕ) (θ : ℝ)
    (H : selfAdjoint (Matrix n n ℂ)) : ℝ := regularizedOwnerPotential H A C (dyadicTsallisRegularizer m θ)

def dyadicOwnerCenterHessian (A : ι → Matrix n n ℂ) (C : Matrix ι ι ℝ) (m : ℕ) (θ : ℝ)
    (H : selfAdjoint (Matrix n n ℂ)) :
    selfAdjoint (Matrix n n ℂ) →L[ℝ] (selfAdjoint (Matrix n n ℂ) →L[ℝ] ℝ) :=
  fderiv ℝ (fun K => fderiv ℝ (dyadicOwnerPotentialAsCenter A C m θ) K) H

/-- The original coefficient matrix of half the actual optimized center Hessian. -/
def dyadicOwnerCoefficientResponse (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (C : Matrix ι ι ℝ) (m : ℕ) (θ : ℝ) (H : selfAdjoint (Matrix n n ℂ)) : Matrix ι ι ℝ :=
  (2 : ℝ)⁻¹ • responseGram (dyadicOwnerCenterHessian A C m θ H) (hermitianMatrixFamily A hA)

theorem dyadicOwnerPotentialAsCenter_eq (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (m : ℕ) (θ : ℝ) :
    dyadicOwnerPotentialAsCenter A C m θ = hermitianDyadicDensityPotential (covarianceKraus A C) m θ := by
  funext H
  change regularizedOwnerPotential (H : Matrix n n ℂ) A C (dyadicTsallisRegularizer m θ) = dyadicDensityPotential (H : Matrix n n ℂ) (covarianceKraus A C) m θ
  exact regularizedOwnerPotential_eq_dyadicDensityPotential (H : Matrix n n ℂ) A hA hC m θ

/-- The coefficient response trace is exactly the observed response after factoring C. -/
theorem dyadicOwnerCoefficientResponse_trace_eq (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) {C : Matrix ι ι ℝ} (hC : C.PosSemidef)
    (m : ℕ) (θ : ℝ) (H : selfAdjoint (Matrix n n ℂ)) :
    realTrace (C * dyadicOwnerCoefficientResponse A hA C m θ H) =
      dyadicKrausObservedResponse H (covarianceKraus A C) (fun a => covarianceKraus_isHermitian A hA C a) m θ := by
  have hs : CFC.sqrt C * (CFC.sqrt C)ᵀ = C := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial, (CFC.sqrt_nonneg C).posSemidef.isHermitian.eq,
      CFC.sqrt_mul_sqrt_self C hC.nonneg]
  rw [dyadicOwnerCoefficientResponse, Matrix.mul_smul, realTrace_smul, ← hs,
    responseGram_factor_trace]
  rw [hs]
  unfold dyadicKrausObservedResponse
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  have hm : coefficientMix (hermitianMatrixFamily A hA) (CFC.sqrt C) a =
      hermitianMatrixFamily (covarianceKraus A C)
        (fun a => covarianceKraus_isHermitian A hA C a) a := by
    apply Subtype.ext
    exact coefficientMix_hermitian_coe A hA (CFC.sqrt C) a
  rw [hm]
  simp only [dyadicOwnerCenterHessian, dyadicOwnerPotentialAsCenter_eq A hA hC m θ]

theorem dyadicOwnerCenterHessian_symmetric [Nonempty n]
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (hθ : 0 < θ)
    (H X Y : selfAdjoint (Matrix n n ℂ)) :
    dyadicOwnerCenterHessian A C m θ H X Y = dyadicOwnerCenterHessian A C m θ H Y X := by
  simp only [dyadicOwnerCenterHessian, dyadicOwnerPotentialAsCenter_eq A hA hC m θ]
  apply (contDiffAt_hermitianDyadicDensityPotential H
    (covarianceKraus A C) m hm θ hθ).isSymmSndFDerivAt _ |>.eq
  rw [minSmoothness_of_isRCLikeNormedField]
  exact WithTop.coe_le_coe.mpr le_top

theorem dyadicOwnerCenterHessian_quadratic_nonneg [Nonempty n]
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (hθ : 0 < θ)
    (H X : selfAdjoint (Matrix n n ℂ)) : 0 ≤ dyadicOwnerCenterHessian A C m θ H X X := by
  simp only [dyadicOwnerCenterHessian, dyadicOwnerPotentialAsCenter_eq A hA hC m θ]
  exact fderiv_fderiv_hermitianDyadicDensityPotential_quadratic_nonneg
    H X (covarianceKraus A C) m hm θ hθ

/-- The actual coefficient response is PSD at every covariance rank. -/
theorem dyadicOwnerCoefficientResponse_posSemidef [Nonempty n]
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (hθ : 0 < θ)
    (H : selfAdjoint (Matrix n n ℂ)) :
    (dyadicOwnerCoefficientResponse A hA C m θ H).PosSemidef := by
  apply Matrix.PosSemidef.smul
  · exact responseGram_posSemidef _ _ (dyadicOwnerCenterHessian_symmetric A hA hC m hm θ hθ H)
      (dyadicOwnerCenterHessian_quadratic_nonneg A hA hC m hm θ hθ H)
  · norm_num

/-- Restricting the movement covariance cannot increase its actual response charge. -/
theorem dyadicOwnerCoefficientResponse_trace_mono [Nonempty n]
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C Q : Matrix ι ι ℝ} (hC : C.PosSemidef) (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (hθ : 0 < θ)
    (H : selfAdjoint (Matrix n n ℂ)) (hQC : Q ≤ C) :
    realTrace (Q * dyadicOwnerCoefficientResponse A hA C m θ H) ≤
      realTrace (C * dyadicOwnerCoefficientResponse A hA C m θ H) := by
  rw [realTrace_mul_comm Q, realTrace_mul_comm C]
  exact realTrace_mul_mono (dyadicOwnerCoefficientResponse_posSemidef A hA hC m hm θ hθ H) hQC

theorem dyadicOwnerCoefficientResponse_quadratic
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (C : Matrix ι ι ℝ) (m : ℕ) (θ : ℝ) (H : selfAdjoint (Matrix n n ℂ)) (u : ι → ℝ) :
    u ⬝ᵥ (dyadicOwnerCoefficientResponse A hA C m θ H *ᵥ u) =
      (1 / 2 : ℝ) * dyadicOwnerCenterHessian A C m θ H
        (∑ i, u i • hermitianMatrixFamily A hA i)
        (∑ i, u i • hermitianMatrixFamily A hA i) := by
  simp only [dyadicOwnerCoefficientResponse, Matrix.smul_mulVec, dotProduct_smul,
    smul_eq_mul, responseGram_quadratic, one_div]

/-- The spectral sampler contracts the actual half-Hessian to its covariance trace. -/
theorem covarianceSample_dyadicOwner_hessian
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (C : Matrix ι ι ℝ) (m : ℕ) (θ : ℝ) (H : selfAdjoint (Matrix n n ℂ))
    {Q : Matrix ι ι ℝ} (hQ : Q.PosSemidef) (htrace : 0 < realTrace Q) :
    (∑ s, covarianceSampleWeight hQ s * ((1 / 2 : ℝ) * dyadicOwnerCenterHessian A C m θ H
      (∑ i, (covarianceSampleIncrement hQ s) i • hermitianMatrixFamily A hA i)
      (∑ i, (covarianceSampleIncrement hQ s) i • hermitianMatrixFamily A hA i))) =
      realTrace (Q * dyadicOwnerCoefficientResponse A hA C m θ H) := by
  simpa only [dyadicOwnerCoefficientResponse_quadratic] using
    covarianceSample_quadratic hQ htrace (dyadicOwnerCoefficientResponse A hA C m θ H)

end
end MatrixSpencer
