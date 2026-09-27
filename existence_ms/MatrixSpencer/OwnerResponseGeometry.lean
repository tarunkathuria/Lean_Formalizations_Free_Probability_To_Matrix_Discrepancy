import MatrixSpencer.CoefficientResponse
import MatrixSpencer.OptimizerResponseUnrestricted
import MatrixSpencer.CovarianceMovement
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Positivity and sampling of the actual coefficient response

The matrix here is half the Hessian of the actual optimized owner potential.
Its positivity allows the finite walk to use any smaller PSD covariance.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix

noncomputable section
namespace MatrixSpencer

section Bilinear
variable {ι E : Type*} [Fintype ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem responseGram_quadratic (β : E →L[ℝ] (E →L[ℝ] ℝ))
    (A : ι → E) (u : ι → ℝ) :
    u ⬝ᵥ (responseGram β A *ᵥ u) = β (∑ i, u i • A i) (∑ i, u i • A i) := by
  simp only [dotProduct, Matrix.mulVec, responseGram, map_sum, map_smul,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem responseGram_posSemidef (β : E →L[ℝ] (E →L[ℝ] ℝ))
    (A : ι → E) (hsym : ∀ x y, β x y = β y x) (hpos : ∀ x, 0 ≤ β x x) :
    (responseGram β A).PosSemidef := by
  refine ⟨?_, ?_⟩
  · ext i j
    simpa only [Matrix.conjTranspose_apply, star_trivial, responseGram] using hsym (A j) (A i)
  · intro u
    simpa only [star_trivial, responseGram_quadratic] using hpos (∑ i, u i • A i)

end Bilinear

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n]

local instance ownerResponseGeometryCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance ownerResponseGeometryNormedSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance

theorem ownerCenterHessian_symmetric [Nonempty n]
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) {θ : ℝ} (hθ : 0 < θ)
    (H X Y : selfAdjoint (Matrix n n ℂ)) :
    ownerCenterHessian A C θ H X Y = ownerCenterHessian A C θ H Y X := by
  simp only [ownerCenterHessian, ownerPotentialAsCenter_eq A hA hC θ]
  apply (contDiffAt_hermitianDensityPotential_source_unrestricted H
    (covarianceKraus A C) hθ).isSymmSndFDerivAt _ |>.eq
  rw [minSmoothness_of_isRCLikeNormedField]
  exact WithTop.coe_le_coe.mpr le_top

theorem ownerCenterHessian_quadratic_nonneg [Nonempty n]
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) {θ : ℝ} (hθ : 0 < θ)
    (H X : selfAdjoint (Matrix n n ℂ)) : 0 ≤ ownerCenterHessian A C θ H X X := by
  simp only [ownerCenterHessian, ownerPotentialAsCenter_eq A hA hC θ]
  exact fderiv_fderiv_hermitianDensityPotential_quadratic_nonneg_source_unrestricted
    H X (covarianceKraus A C) hθ

/-- The actual coefficient response is PSD at every covariance rank. -/
theorem ownerCoefficientResponse_posSemidef [Nonempty n]
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) {θ : ℝ} (hθ : 0 < θ)
    (H : selfAdjoint (Matrix n n ℂ)) :
    (ownerCoefficientResponse A hA C θ H).PosSemidef := by
  apply Matrix.PosSemidef.smul
  · exact responseGram_posSemidef _ _ (ownerCenterHessian_symmetric A hA hC hθ H)
      (ownerCenterHessian_quadratic_nonneg A hA hC hθ H)
  · norm_num

/-- Restricting the movement covariance cannot increase its actual response charge. -/
theorem ownerCoefficientResponse_trace_mono [Nonempty n]
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C Q : Matrix ι ι ℝ} (hC : C.PosSemidef) {θ : ℝ} (hθ : 0 < θ)
    (H : selfAdjoint (Matrix n n ℂ)) (hQC : Q ≤ C) :
    realTrace (Q * ownerCoefficientResponse A hA C θ H) ≤
      realTrace (C * ownerCoefficientResponse A hA C θ H) := by
  rw [realTrace_mul_comm Q, realTrace_mul_comm C]
  exact realTrace_mul_mono (ownerCoefficientResponse_posSemidef A hA hC hθ H) hQC

theorem ownerCoefficientResponse_quadratic
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (C : Matrix ι ι ℝ) (θ : ℝ) (H : selfAdjoint (Matrix n n ℂ)) (u : ι → ℝ) :
    u ⬝ᵥ (ownerCoefficientResponse A hA C θ H *ᵥ u) =
      (1 / 2 : ℝ) * ownerCenterHessian A C θ H
        (∑ i, u i • hermitianMatrixFamily A hA i)
        (∑ i, u i • hermitianMatrixFamily A hA i) := by
  simp only [ownerCoefficientResponse, Matrix.smul_mulVec, dotProduct_smul,
    smul_eq_mul, responseGram_quadratic, one_div]

/-- The spectral sampler contracts the actual half-Hessian to its covariance trace. -/
theorem covarianceSample_owner_hessian
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (C : Matrix ι ι ℝ) (θ : ℝ) (H : selfAdjoint (Matrix n n ℂ))
    {Q : Matrix ι ι ℝ} (hQ : Q.PosSemidef) (htrace : 0 < realTrace Q) :
    (∑ s, covarianceSampleWeight hQ s * ((1 / 2 : ℝ) * ownerCenterHessian A C θ H
      (∑ i, (covarianceSampleIncrement hQ s) i • hermitianMatrixFamily A hA i)
      (∑ i, (covarianceSampleIncrement hQ s) i • hermitianMatrixFamily A hA i))) =
      realTrace (Q * ownerCoefficientResponse A hA C θ H) := by
  simpa only [ownerCoefficientResponse_quadratic] using
    covarianceSample_quadratic hQ htrace (ownerCoefficientResponse A hA C θ H)

end MatrixSpencer
