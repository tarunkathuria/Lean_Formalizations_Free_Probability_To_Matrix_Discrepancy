import MatrixSpencer.RectangularRidgeCertificate
import SimpleMS.UniformCertificate

/-!
# Exact ridge-certificate moments of the actual finite uniform spectral-frame sampler

The retained projection eigenvectors and the two equally weighted signs define the
finite sampler. This module proves its actual certificate cancellation
and tangent second moment. No favorable draw or success probability is supplied.
-/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.RectangularRidgeSamplerMoments
open RectangularRidgeCertificate RectangularRidgeCovarianceCalculus
open SimpleMS.UniformSampler SimpleMS.UniformMoments SimpleMS.UniformCertificate
variable {N d : ℕ} [Nonempty (Fin d)]
local instance ridgeSamplerMomentsCStar : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
local instance ridgeSamplerMomentsRealSpace : NormedSpace ℝ (selfAdjoint (Matrix (Fin d) (Fin d) ℂ)) := inferInstance

lemma sampled_difference (Hstar : Matrix (Fin d) (Fin d) ℂ)
    (A : Fin N → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ i, (A i).IsHermitian)
    (m : ℕ) (θ κ : ℝ) (H : selfAdjoint (Matrix (Fin d) (Fin d) ℂ))
    (C C' : Matrix (Fin N) (Fin N) ℝ) (v : EuclideanSpace ℝ (Fin N)) (h : ℝ) :
    certificate Hstar A m θ κ (H + h • ownerPhysicalIncrement A hA v) C' -
      certificate Hstar A m θ κ H C =
        (RectangularRidgeCovarianceCalculus.ownerPotential m (H + h • ownerPhysicalIncrement A hA v) A C' θ κ -
          RectangularRidgeCovarianceCalculus.ownerPotential m H A C θ κ) -
            h * tracePairing (density Hstar m θ κ) (ownerPhysicalIncrement A hA v) := by
  rw [certificate_mixed_difference]
  congr 1
  change realTrace (density Hstar m θ κ *
    (((H : Matrix (Fin d) (Fin d) ℂ) + h • (ownerPhysicalIncrement A hA v : Matrix (Fin d) (Fin d) ℂ)) -
      (H : Matrix (Fin d) (Fin d) ℂ))) = _
  rw [add_sub_cancel_left, Matrix.mul_smul, realTrace_smul]
  rfl

/-- The exact finite certificate drift equals the actual matched potential drift. -/
theorem certificate_drift_eq (Hstar : Matrix (Fin d) (Fin d) ℂ)
    (A : Fin N → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ i, (A i).IsHermitian) (m : ℕ) (θ κ : ℝ)
    (H : selfAdjoint (Matrix (Fin d) (Fin d) ℂ)) (C : Matrix (Fin N) (Fin N) ℝ) (W : Submodule ℝ (EuclideanSpace ℝ (Fin N))) (h : ℝ) :
    (∑ s, weight W s * (certificate Hstar A m θ κ (H + h • ownerPhysicalIncrement A hA (increment W s))
      (C - h ^ 2 • (covMatrix W)) - certificate Hstar A m θ κ H C)) =
      ∑ s, weight W s * (RectangularRidgeCovarianceCalculus.ownerPotential m
        (H + h • ownerPhysicalIncrement A hA (increment W s)) A (C - h ^ 2 • (covMatrix W)) θ κ -
          RectangularRidgeCovarianceCalculus.ownerPotential m H A C θ κ) := by
  let S : selfAdjoint (Matrix (Fin d) (Fin d) ℂ) :=
    ⟨density Hstar m θ κ, (density_mem Hstar m θ κ).1.isHermitian⟩
  have hz := physical_linear_mean A hA W S
  simp only [sampled_difference, mul_sub, Finset.sum_sub_distrib]
  have he : (∑ s, weight W s * (h * tracePairing (density Hstar m θ κ)
      (ownerPhysicalIncrement A hA (increment W s)))) = 0 := by
    calc
      _ = h * ∑ s, weight W s * tracePairing S (ownerPhysicalIncrement A hA (increment W s)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s _
        ring
      _ = 0 := by rw [hz, mul_zero]
  rw [he, sub_zero]

/-- The saved tangent has exactly zero sampled increment at every current covariance. -/
theorem tangent_increment_mean_zero (Hstar : Matrix (Fin d) (Fin d) ℂ)
    (A : Fin N → Matrix (Fin d) (Fin d) ℂ) (m : ℕ) (θ κ : ℝ)
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin N))) :
    (∑ s, weight W s * (gradient Hstar A m θ κ ⬝ᵥ WithLp.ofLp (increment W s))) = 0 :=
  dot_mean W (gradient Hstar A m θ κ)

/-- The actual saved-gradient variance uses the original unit-contraction family. -/
theorem tangent_square_le (Hstar : Matrix (Fin d) (Fin d) ℂ)
    (A : Fin N → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ i, (A i).IsHermitian)
    (hAn : ∀ i, ‖A i‖ ≤ 1) (m : ℕ) (θ κ : ℝ)
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin N))) (hQ : (covMatrix W).PosSemidef) (hQ1 : (covMatrix W) ≤ 1)
    (hq : 0 < realTrace (covMatrix W)) (M h : ℝ) :
    (∑ s, weight W s * (M + h * (gradient Hstar A m θ κ ⬝ᵥ WithLp.ofLp (increment W s))) ^ 2) ≤
      M ^ 2 + h ^ 2 * N := by
  rw [affine_square W hQ hq]
  have hb := (gradient_covariance_bound Hstar A hA hAn m θ κ hQ hQ1).2
  simp only [Fintype.card_fin] at hb
  exact add_le_add_left (mul_le_mul_of_nonneg_left hb (sq_nonneg h)) _

/-- The same bound, expressed as the expectation of the concrete computed sampler. -/
theorem sampled_tangent_square_le (Hstar : Matrix (Fin d) (Fin d) ℂ)
    (A : Fin N → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ i, (A i).IsHermitian)
    (hAn : ∀ i, ‖A i‖ ≤ 1) (m : ℕ) (θ κ : ℝ)
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin N))) (hQ : (covMatrix W).PosSemidef) (hQ1 : (covMatrix W) ≤ 1)
    (hq : 0 < realTrace (covMatrix W)) (M h : ℝ) :
    (sample W (SimpleMS.UniformMoments.rank_positive W hq)).expectation (fun v => (M + h * (gradient Hstar A m θ κ ⬝ᵥ WithLp.ofLp v)) ^ 2) ≤
      M ^ 2 + h ^ 2 * N :=
  tangent_square_le Hstar A hA hAn m θ κ W hQ hQ1 hq M h

end MatrixSpencer.RectangularRidgeSamplerMoments
