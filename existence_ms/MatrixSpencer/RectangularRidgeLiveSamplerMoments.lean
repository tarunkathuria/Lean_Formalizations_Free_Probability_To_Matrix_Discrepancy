import MatrixSpencer.RectangularRidgeSamplerMoments
import MatrixSpencer.RectangularRidgeLiveDomination

/-! The actual uniform-frame tangent variance is the live count, even though the
saved density gradient and covariance use all original coordinates. -/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.RectangularRidgeLiveSamplerMoments
open RectangularRidgeLiveOwner RectangularRidgeCertificate
open SimpleMS.UniformSampler SimpleMS.UniformMoments
variable {N d : ℕ} [Nonempty (Fin d)]
local instance ridgeLiveSamplerCStar : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}

lemma frame_transpose_mulVec (F₀ : Finset (Fin N)) (g : Fin N → ℝ) :
    (frame F₀)ᵀ *ᵥ g = fun j => g (index F₀ j) := by
  ext j
  simp [Matrix.mulVec, dotProduct, frame, Matrix.submatrix_apply, Matrix.one_apply]

lemma projection_quadratic (F₀ : Finset (Fin N)) (g : Fin N → ℝ) :
    g ⬝ᵥ ((owner F₀).physical *ᵥ g) = ∑ j, g (index F₀ j) ^ 2 := by
  simp only [MSManuscriptSupportedOwner.Owner.physical, owner, Matrix.mul_one]
  rw [← Matrix.mulVec_mulVec, InverseComparison.transpose_pairing, frame_transpose_mulVec]
  simp only [dotProduct, pow_two]

/-- Coordinatewise saved-gradient bounds are charged only on the live projection. -/
theorem gradient_quadratic_le (Hstar : Matrix (Fin d) (Fin d) ℂ)
    (A : Fin N → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ i, (A i).IsHermitian)
    (hAn : ∀ i, ‖A i‖ ≤ 1) (m : ℕ) (θ κ : ℝ)
    (F₀ : Finset (Fin N)) (Q : Matrix (Fin N) (Fin N) ℝ)
    (hQ : Q ≤ (owner F₀).physical) :
    gradient Hstar A m θ κ ⬝ᵥ (Q *ᵥ gradient Hstar A m θ κ) ≤ count F₀ := by
  have hm := InverseComparison.quadratic_mono hQ (gradient Hstar A m θ κ)
  change _ ≤ gradient Hstar A m θ κ ⬝ᵥ ((owner F₀).physical *ᵥ gradient Hstar A m θ κ) at hm
  rw [projection_quadratic] at hm
  have hb : (∑ j, gradient Hstar A m θ κ (index F₀ j) ^ 2) ≤ ∑ _j : Fin (count F₀), (1 : ℝ) := by
    apply Finset.sum_le_sum
    intro j _
    have hh := abs_gradient_le_one Hstar A hA hAn m θ κ (index F₀ j)
    nlinarith [sq_abs (gradient Hstar A m θ κ (index F₀ j)), abs_nonneg (gradient Hstar A m θ κ (index F₀ j))]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hb
  exact hm.trans hb

/-- Actual conditional tangent-square increment with a live-count variance bound. -/
theorem tangent_square_le (Hstar : Matrix (Fin d) (Fin d) ℂ)
    (A : Fin N → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ i, (A i).IsHermitian)
    (hAn : ∀ i, ‖A i‖ ≤ 1) (m : ℕ) (θ κ : ℝ)
    (F₀ : Finset (Fin N)) (W : Submodule ℝ (EuclideanSpace ℝ (Fin N)))
    (hQ : (covMatrix W).PosSemidef) (hQ1 : (covMatrix W) ≤ 1) (hF₀ : ∀ i ∈ F₀, (covMatrix W) *ᵥ Pi.single i 1 = 0)
    (hq : 0 < realTrace (covMatrix W)) (M h : ℝ) :
    (∑ z, weight W z * (M + h * (gradient Hstar A m θ κ ⬝ᵥ WithLp.ofLp (increment W z))) ^ 2) ≤
      M ^ 2 + h ^ 2 * count F₀ := by
  rw [SimpleMS.UniformCertificate.affine_square W hQ hq]
  have hh := gradient_quadratic_le Hstar A hA hAn m θ κ F₀ (covMatrix W)
    (RectangularRidgeLiveDomination.covariance_le_projection (covMatrix W) hQ hQ1 F₀ hF₀)
  exact add_le_add_left (mul_le_mul_of_nonneg_left hh (sq_nonneg h)) _

end MatrixSpencer.RectangularRidgeLiveSamplerMoments
