import MatrixSpencer.OwnerWalkMesh
import MatrixSpencer.OwnerCertificate

/-!
# The actual certificate has the same centered sampled drift

Its anchored supporting-plane term cancels exactly under the concrete
mean-zero sampler, including after restriction to positive-weight branches.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix
noncomputable section
namespace MatrixSpencer

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n] [Nonempty n]
local instance samplerCertificateCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance samplerCertificateSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance

theorem ownerCertificate_mixed_difference (Hstar H H' : Matrix n n ℂ)
    (A : ι → Matrix n n ℂ) (θ : ℝ) (C C' : Matrix ι ι ℝ) :
    ownerCertificate Hstar A θ H' C' - ownerCertificate Hstar A θ H C =
      (ownerPotential H' A C' θ - ownerPotential H A C θ) -
        realTrace (ownerCertificateDensity Hstar θ * (H' - H)) := by
  unfold ownerCertificate
  rw [← ownerCertificateTangent_difference]
  ring

theorem ownerCertificate_sampled_difference
    (Hstar : Matrix n n ℂ) (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (θ : ℝ) (H : selfAdjoint (Matrix n n ℂ))
    (C C' : Matrix ι ι ℝ) (v : EuclideanSpace ℝ ι) (h : ℝ) :
    ownerCertificate Hstar A θ (H + h • ownerPhysicalIncrement A hA v) C' -
      ownerCertificate Hstar A θ H C =
      (ownerPotential (H + h • ownerPhysicalIncrement A hA v) A C' θ - ownerPotential H A C θ) -
        h * tracePairing (ownerCertificateDensity Hstar θ) (ownerPhysicalIncrement A hA v) := by
  rw [ownerCertificate_mixed_difference]
  congr 1
  change realTrace (ownerCertificateDensity Hstar θ *
    (((H : Matrix n n ℂ) + h • (ownerPhysicalIncrement A hA v : Matrix n n ℂ)) -
      (H : Matrix n n ℂ))) = _
  rw [add_sub_cancel_left, Matrix.mul_smul, realTrace_smul]
  rfl

/-- The finite certificate drift equals the actual optimized-potential drift. -/
theorem covarianceSample_certificate_drift_eq
    (Hstar : Matrix n n ℂ) (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (θ : ℝ) (H : selfAdjoint (Matrix n n ℂ))
    (C : Matrix ι ι ℝ) {Q : Matrix ι ι ℝ} (hQ : Q.PosSemidef) (h : ℝ) :
    (∑ s, covarianceSampleWeight hQ s *
      (ownerCertificate Hstar A θ (H + h • ownerPhysicalIncrement A hA
        (covarianceSampleIncrement hQ s)) (C - h ^ 2 • Q) -
          ownerCertificate Hstar A θ H C)) = ownerSamplerDrift A hA θ H C hQ h := by
  let S : selfAdjoint (Matrix n n ℂ) :=
    ⟨ownerCertificateDensity Hstar θ, (ownerCertificateDensity_mem Hstar θ).1.isHermitian⟩
  have hz := covarianceSample_owner_linear_mean A hA hQ S
  simp only [ownerCertificate_sampled_difference, mul_sub, Finset.sum_sub_distrib]
  have he : (∑ s, covarianceSampleWeight hQ s * (h * tracePairing (ownerCertificateDensity Hstar θ)
      (ownerPhysicalIncrement A hA (covarianceSampleIncrement hQ s)))) = 0 := by
    calc
      _ = h * ∑ s, covarianceSampleWeight hQ s * tracePairing S
          (ownerPhysicalIncrement A hA (covarianceSampleIncrement hQ s)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s _
        ring
      _ = 0 := by rw [hz, mul_zero]
  rw [he, sub_zero]
  simp only [ownerSamplerDrift, mul_sub, Finset.sum_sub_distrib]

theorem positive_covarianceSample_certificate_drift_eq
    (Hstar : Matrix n n ℂ) (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (θ : ℝ) (H : selfAdjoint (Matrix n n ℂ))
    (C : Matrix ι ι ℝ) {Q : Matrix ι ι ℝ} (hQ : Q.PosSemidef)
    (htrace : 0 < realTrace Q) (h : ℝ) :
    (∑ s : PositiveCovarianceOutcome hQ, covarianceSampleWeight hQ s *
      (ownerCertificate Hstar A θ (H + h • ownerPhysicalIncrement A hA
        (covarianceSampleIncrement hQ s)) (C - h ^ 2 • Q) -
          ownerCertificate Hstar A θ H C)) = ownerSamplerDrift A hA θ H C hQ h := by
  have hh := sum_positive_weight_smul (covarianceSampleWeight hQ)
    (covarianceSampleWeight_nonneg hQ htrace) (fun s =>
      ownerCertificate Hstar A θ (H + h • ownerPhysicalIncrement A hA
        (covarianceSampleIncrement hQ s)) (C - h ^ 2 • Q) - ownerCertificate Hstar A θ H C)
  simp only [smul_eq_mul] at hh
  exact hh.trans (covarianceSample_certificate_drift_eq Hstar A hA θ H C hQ h)

/-- Actual covariance payment transfers exactly to the anchored certificate. -/
theorem ownerCertificate_covariance_payment (Hstar H : Matrix n n ℂ)
    (A : ι → Matrix n n ℂ) (θ price paid : ℝ) (C C' : Matrix ι ι ℝ)
    (hp : ownerPotential H A C' θ + price * paid ≤ ownerPotential H A C θ) :
    ownerCertificate Hstar A θ H C' + price * paid ≤ ownerCertificate Hstar A θ H C := by
  unfold ownerCertificate
  linarith

/-- Rounding followed by actual paid preparation has at most twice the rounding norm cost. -/
theorem ownerCertificate_rounding_preparation_le
    (Hstar Hmoved Hrounded : Matrix n n ℂ)
    (hHmoved : Hmoved.IsHermitian) (hHrounded : Hrounded.IsHermitian)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (θ price paid r : ℝ) {C C' : Matrix ι ι ℝ} (hC : C.PosSemidef)
    (hp : ownerPotential Hrounded A C' θ + price * paid ≤ ownerPotential Hrounded A C θ)
    (hr : ‖Hrounded - Hmoved‖ ≤ r) :
    ownerCertificate Hstar A θ Hrounded C' + price * paid ≤
      ownerCertificate Hstar A θ Hmoved C + 2 * r := by
  have hpay := ownerCertificate_covariance_payment Hstar Hrounded A θ price paid C C' hp
  have hround := abs_ownerCertificate_center_difference_le Hstar hHmoved hHrounded A hA hC θ
  have hle := (le_abs_self
    (ownerCertificate Hstar A θ Hrounded C - ownerCertificate Hstar A θ Hmoved C)).trans hround
  linarith

end MatrixSpencer
