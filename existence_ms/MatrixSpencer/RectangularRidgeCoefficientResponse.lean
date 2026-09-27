import MatrixSpencer.RectangularRidgePotentialResponse
import MatrixSpencer.OwnerResponseGeometry

/-! The coefficient response is half of the actual mixed potential Hessian. -/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
namespace MatrixSpencer.RectangularRidgeCalculus
noncomputable section
set_option maxHeartbeats 800000
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n]
local instance dyadicCoefficientCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance dyadicCoefficientSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance

def krausObservedResponse (H : selfAdjoint (Matrix n n ℂ))
    (B : ι → Matrix n n ℂ) (hB : ∀ a, (B a).IsHermitian) (m : ℕ) (θ κ : ℝ) : ℝ :=
  (2 : ℝ)⁻¹ * ∑ a, fderiv ℝ (fun K => fderiv ℝ (hermitianPotential B m θ κ) K) H
    (hermitianMatrixFamily B hB a) (hermitianMatrixFamily B hB a)

def ownerPotentialAsCenter (A : ι → Matrix n n ℂ) (C : Matrix ι ι ℝ) (m : ℕ) (θ κ : ℝ)
    (H : selfAdjoint (Matrix n n ℂ)) : ℝ := hermitianPotential (covarianceKraus A C) m θ κ H

def ownerCenterHessian (A : ι → Matrix n n ℂ) (C : Matrix ι ι ℝ) (m : ℕ) (θ κ : ℝ)
    (H : selfAdjoint (Matrix n n ℂ)) :
    selfAdjoint (Matrix n n ℂ) →L[ℝ] (selfAdjoint (Matrix n n ℂ) →L[ℝ] ℝ) :=
  fderiv ℝ (fun K => fderiv ℝ (ownerPotentialAsCenter A C m θ κ) K) H

/-- The original coefficient matrix of half the actual optimized center Hessian. -/
def ownerCoefficientResponse (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (C : Matrix ι ι ℝ) (m : ℕ) (θ κ : ℝ) (H : selfAdjoint (Matrix n n ℂ)) : Matrix ι ι ℝ :=
  (2 : ℝ)⁻¹ • responseGram (ownerCenterHessian A C m θ κ H) (hermitianMatrixFamily A hA)

theorem ownerPotentialAsCenter_eq (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (m : ℕ) (θ κ : ℝ) :
    ownerPotentialAsCenter A C m θ κ = hermitianPotential (covarianceKraus A C) m θ κ := rfl

/-- The coefficient response trace is exactly the observed response after factoring C. -/
theorem ownerCoefficientResponse_trace_eq (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) {C : Matrix ι ι ℝ} (hC : C.PosSemidef)
    (m : ℕ) (θ κ : ℝ) (H : selfAdjoint (Matrix n n ℂ)) :
    realTrace (C * ownerCoefficientResponse A hA C m θ κ H) =
      krausObservedResponse H (covarianceKraus A C) (fun a => covarianceKraus_isHermitian A hA C a) m θ κ := by
  have hs : CFC.sqrt C * (CFC.sqrt C)ᵀ = C := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial, (CFC.sqrt_nonneg C).posSemidef.isHermitian.eq,
      CFC.sqrt_mul_sqrt_self C hC.nonneg]
  rw [ownerCoefficientResponse, Matrix.mul_smul, realTrace_smul, ← hs,
    responseGram_factor_trace]
  rw [hs]
  unfold krausObservedResponse
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  have hm : coefficientMix (hermitianMatrixFamily A hA) (CFC.sqrt C) a =
      hermitianMatrixFamily (covarianceKraus A C)
        (fun a => covarianceKraus_isHermitian A hA C a) a := by
    apply Subtype.ext
    exact coefficientMix_hermitian_coe A hA (CFC.sqrt C) a
  rw [hm]
  simp only [ownerCenterHessian, ownerPotentialAsCenter_eq A hA hC m θ κ]

theorem ownerCenterHessian_symmetric [Nonempty n]
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (m : ℕ) (hm : 1 ≤ m) (θ κ : ℝ) (hθ : 0 < θ) (hκ : 0 < κ)
    (H X Y : selfAdjoint (Matrix n n ℂ)) :
    ownerCenterHessian A C m θ κ H X Y = ownerCenterHessian A C m θ κ H Y X := by
  simp only [ownerCenterHessian, ownerPotentialAsCenter_eq A hA hC m θ κ]
  apply (contDiffAt_hermitianPotential H
    (covarianceKraus A C) m hm θ κ hθ hκ).isSymmSndFDerivAt _ |>.eq
  rw [minSmoothness_of_isRCLikeNormedField]
  exact WithTop.coe_le_coe.mpr le_top

theorem ownerCenterHessian_quadratic_nonneg [Nonempty n]
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (m : ℕ) (hm : 1 ≤ m) (θ κ : ℝ) (hθ : 0 < θ) (hκ : 0 < κ)
    (H X : selfAdjoint (Matrix n n ℂ)) : 0 ≤ ownerCenterHessian A C m θ κ H X X := by
  simp only [ownerCenterHessian, ownerPotentialAsCenter_eq A hA hC m θ κ]
  exact potential_hessian_nonneg
    H X (covarianceKraus A C) m hm θ κ hθ hκ

/-- The actual coefficient response is PSD at every covariance rank. -/
theorem ownerCoefficientResponse_posSemidef [Nonempty n]
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (m : ℕ) (hm : 1 ≤ m) (θ κ : ℝ) (hθ : 0 < θ) (hκ : 0 < κ)
    (H : selfAdjoint (Matrix n n ℂ)) :
    (ownerCoefficientResponse A hA C m θ κ H).PosSemidef := by
  apply Matrix.PosSemidef.smul
  · exact responseGram_posSemidef _ _ (ownerCenterHessian_symmetric A hA hC m hm θ κ hθ hκ H)
      (ownerCenterHessian_quadratic_nonneg A hA hC m hm θ κ hθ hκ H)
  · norm_num

/-- Restricting the movement covariance cannot increase its actual response charge. -/
theorem ownerCoefficientResponse_trace_mono [Nonempty n]
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C Q : Matrix ι ι ℝ} (hC : C.PosSemidef) (m : ℕ) (hm : 1 ≤ m) (θ κ : ℝ) (hθ : 0 < θ) (hκ : 0 < κ)
    (H : selfAdjoint (Matrix n n ℂ)) (hQC : Q ≤ C) :
    realTrace (Q * ownerCoefficientResponse A hA C m θ κ H) ≤
      realTrace (C * ownerCoefficientResponse A hA C m θ κ H) := by
  rw [realTrace_mul_comm Q, realTrace_mul_comm C]
  exact realTrace_mul_mono (ownerCoefficientResponse_posSemidef A hA hC m hm θ κ hθ hκ H) hQC

theorem ownerCoefficientResponse_quadratic
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (C : Matrix ι ι ℝ) (m : ℕ) (θ κ : ℝ) (H : selfAdjoint (Matrix n n ℂ)) (u : ι → ℝ) :
    u ⬝ᵥ (ownerCoefficientResponse A hA C m θ κ H *ᵥ u) =
      (1 / 2 : ℝ) * ownerCenterHessian A C m θ κ H
        (∑ i, u i • hermitianMatrixFamily A hA i)
        (∑ i, u i • hermitianMatrixFamily A hA i) := by
  simp only [ownerCoefficientResponse, Matrix.smul_mulVec, dotProduct_smul,
    smul_eq_mul, responseGram_quadratic, one_div]

/-- The spectral sampler contracts the actual half-Hessian to its covariance trace. -/
theorem covarianceSample_owner_hessian
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (C : Matrix ι ι ℝ) (m : ℕ) (θ κ : ℝ) (H : selfAdjoint (Matrix n n ℂ))
    {Q : Matrix ι ι ℝ} (hQ : Q.PosSemidef) (htrace : 0 < realTrace Q) :
    (∑ s, covarianceSampleWeight hQ s * ((1 / 2 : ℝ) * ownerCenterHessian A C m θ κ H
      (∑ i, (covarianceSampleIncrement hQ s) i • hermitianMatrixFamily A hA i)
      (∑ i, (covarianceSampleIncrement hQ s) i • hermitianMatrixFamily A hA i))) =
      realTrace (Q * ownerCoefficientResponse A hA C m θ κ H) := by
  simpa only [ownerCoefficientResponse_quadratic] using
    covarianceSample_quadratic hQ htrace (ownerCoefficientResponse A hA C m θ κ H)

end
end MatrixSpencer.RectangularRidgeCalculus
