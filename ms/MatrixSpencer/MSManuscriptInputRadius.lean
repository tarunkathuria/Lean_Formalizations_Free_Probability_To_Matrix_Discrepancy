import MatrixSpencer.MSManuscriptNumericalAcceptance
import MatrixSpencer.KSComplexObjectiveBound

/-!
# Input-derived center and centered-movement radius

The radius used for the saved-density certificate comes from the cube and
actual accumulated rounding displacement. It uses the original matrices'
unit operator-norm bounds and contains no optimized value or spectral-gap
parameter. The cumulative centered movement need not itself stay in the cube.
-/

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.MSManuscriptInputRadius
open KSOwnerInputBounds MSManuscriptNumericalAcceptance
variable {N d : ℕ}

/-- Frobenius energy is at most dimension times the operator-norm square. -/
theorem matrixEnergy_le (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) :
    matrixEnergy A ≤ (d:ℝ)*‖A‖^2 := by
  rw [matrixEnergy_eq_trace_square A hA]
  calc
    realTrace (A*A) ≤ ‖Matrix.trace (A*A)‖ := Complex.re_le_norm _
    _ ≤ (d:ℝ)*‖A‖*‖A‖ := by
      simpa only [Fintype.card_fin] using KSComplexObjectiveBound.norm_trace_mul_le_card_mul_norm A A
    _ = (d:ℝ)*‖A‖^2 := by ring

theorem frobenius_le (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) :
    Real.sqrt (matrixEnergy A) ≤ Real.sqrt (d:ℝ)*‖A‖ := by
  have h := Real.sqrt_le_sqrt (matrixEnergy_le A hA)
  rwa [Real.sqrt_mul (by positivity : (0:ℝ) ≤ d), Real.sqrt_sq_eq_abs,
    abs_of_nonneg (norm_nonneg A)] at h

def combination (A : Fin N → Matrix (Fin d) (Fin d) ℂ) (c : Fin N → ℝ) :
    Matrix (Fin d) (Fin d) ℂ := ∑ i, c i • A i

theorem combination_isHermitian (A : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀ i, (A i).IsHermitian) (c : Fin N → ℝ) : (combination A c).IsHermitian := by
  change (∑ i, c i • A i)ᴴ = ∑ i, c i • A i
  simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, star_trivial, fun i => (hA i).eq]

theorem combination_norm_le (A : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀ i, ‖A i‖ ≤ 1) (c : Fin N → ℝ) : ‖combination A c‖ ≤ ∑ i, |c i| := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [norm_smul, Real.norm_eq_abs]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (hA i) (abs_nonneg (c i))

theorem combination_frobenius_le (A : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀ i, (A i).IsHermitian) (hunit : ∀ i, ‖A i‖ ≤ 1) (c : Fin N → ℝ) :
    Real.sqrt (matrixEnergy (combination A c)) ≤ Real.sqrt (d:ℝ)*(∑ i, |c i|) :=
  (frobenius_le _ (combination_isHermitian A hA c)).trans
    (mul_le_mul_of_nonneg_left (combination_norm_le A hunit c) (Real.sqrt_nonneg _))

/-- Both coefficient vectors lie in the full cube. -/
theorem cube_difference_l1_le (x y : Fin N → ℝ)
    (hx : ∀ i, |x i| ≤ 1) (hy : ∀ i, |y i| ≤ 1) :
    ∑ i, |x i-y i| ≤ 2*(N:ℝ) := by
  calc
    ∑ i, |x i-y i| ≤ ∑ i : Fin N, (2:ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      exact (abs_sub (x i) (y i)).trans (by linarith [hx i,hy i])
    _ = _ := by simp; ring

/-- The centered ledger is controlled by total displacement plus its
actual cumulative rounding error, without summing the number of steps. -/
theorem centered_l1_le (x y centered : Fin N → ℝ)
    (hx : ∀ i, |x i| ≤ 1) (hy : ∀ i, |y i| ≤ 1) {rounding : ℝ}
    (hround : ∑ i, |(x i-y i)-centered i| ≤ rounding) :
    ∑ i, |centered i| ≤ 2*(N:ℝ)+rounding := by
  calc
    ∑ i, |centered i| ≤ ∑ i, (|x i-y i|+|(x i-y i)-centered i|) := by
      apply Finset.sum_le_sum
      intro i _
      have h := abs_sub (x i-y i) ((x i-y i)-centered i)
      simpa only [sub_sub_cancel] using h
    _ = (∑ i, |x i-y i|)+(∑ i, |(x i-y i)-centered i|) := Finset.sum_add_distrib
    _ ≤ 2*(N:ℝ)+rounding := add_le_add (cube_difference_l1_le x y hx hy) hround

/-- One arithmetic radius works for every endpoint in the epoch. -/
def radius (N d : ℕ) (rounding : ℝ) : ℝ := Real.sqrt (d:ℝ)*(2*N+rounding)

theorem radius_nonneg {rounding : ℝ} (hround : 0 ≤ rounding) : 0 ≤ radius N d rounding := by
  unfold radius
  positivity

theorem center_difference_radius (A : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀ i, (A i).IsHermitian) (hunit : ∀ i, ‖A i‖ ≤ 1)
    (H0 : Matrix (Fin d) (Fin d) ℂ) (x y : Fin N → ℝ)
    (hx : ∀ i, |x i| ≤ 1) (hy : ∀ i, |y i| ≤ 1) {rounding : ℝ} (hr : 0 ≤ rounding) :
    Real.sqrt (matrixEnergy ((H0+combination A x)-(H0+combination A y))) ≤ radius N d rounding := by
  have hid : (H0+combination A x)-(H0+combination A y) = combination A (fun i => x i-y i) := by
    simp only [combination, sub_smul, Finset.sum_sub_distrib]
    abel
  rw [hid]
  apply (combination_frobenius_le A hA hunit _).trans
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  exact (cube_difference_l1_le x y hx hy).trans (by linarith)

theorem centered_movement_radius (A : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀ i, (A i).IsHermitian) (hunit : ∀ i, ‖A i‖ ≤ 1)
    (x y centered : Fin N → ℝ) (hx : ∀ i, |x i| ≤ 1) (hy : ∀ i, |y i| ≤ 1)
    {rounding : ℝ} (hround : ∑ i, |(x i-y i)-centered i| ≤ rounding) :
    Real.sqrt (matrixEnergy (combination A centered)) ≤ radius N d rounding :=
  (combination_frobenius_le A hA hunit centered).trans
    (mul_le_mul_of_nonneg_left (centered_l1_le x y centered hx hy hround) (Real.sqrt_nonneg _))

/-- Direct discharge of the acceptance endpoint's geometric validity
from actual cube coordinates and its cumulative rounding discrepancy. -/
theorem endpoint_valid_of_rounding (cfg : Config N d) (e : Endpoint N d)
    (H0 : Matrix (Fin d) (Fin d) ℂ) (hH0 : H0.IsHermitian)
    (x y centered : Fin N → ℝ) (hx : ∀ i, |x i| ≤ 1) (hy : ∀ i, |y i| ≤ 1)
    {rounding : ℝ} (hr : 0 ≤ rounding)
    (hround : ∑ i, |(x i-y i)-centered i| ≤ rounding)
    (hunit : ∀ i, ‖cfg.family i‖ ≤ 1)
    (hsaved : cfg.savedCenter = H0+combination cfg.family y)
    (hcenter : e.center = H0+combination cfg.family x)
    (hmovement : e.movementSum = combination cfg.family centered)
    (hcov : e.covariance.PosSemidef) (hradius : radius N d rounding ≤ cfg.radius) :
    e.Valid cfg := by
  refine ⟨?_,hcov,?_,?_,?_⟩
  · rw [hcenter]
    exact hH0.add (combination_isHermitian cfg.family cfg.family_hermitian x)
  · rw [hmovement]
    exact combination_isHermitian cfg.family cfg.family_hermitian centered
  · rw [hcenter,hsaved]
    exact (center_difference_radius cfg.family cfg.family_hermitian hunit H0 x y hx hy hr).trans hradius
  · rw [hmovement]
    exact (centered_movement_radius cfg.family cfg.family_hermitian hunit x y centered hx hy hround).trans hradius

/-- The same actual coefficient discrepancy pays the missing tangent in
the accepted-epoch potential calculation. It is not assumed centered. -/
theorem rounding_tangent_le (cfg : Config N d) (e : Endpoint N d)
    (H0 : Matrix (Fin d) (Fin d) ℂ) (x y centered : Fin N → ℝ)
    {rounding : ℝ} (hround : ∑ i, |(x i-y i)-centered i| ≤ rounding)
    (hunit : ∀ i, ‖cfg.family i‖ ≤ 1)
    (hsaved : cfg.savedCenter = H0+combination cfg.family y)
    (hcenter : e.center = H0+combination cfg.family x)
    (hmovement : e.movementSum = combination cfg.family centered) :
    |roundingTangent cfg e| ≤ rounding := by
  letI : Nonempty (Fin d) := ⟨⟨0,cfg.dimension_pos⟩⟩
  have hid : e.center-cfg.savedCenter-e.movementSum =
      combination cfg.family (fun i => (x i-y i)-centered i) := by
    rw [hcenter,hsaved,hmovement]
    simp only [combination, sub_smul, Finset.sum_sub_distrib]
    abel
  change |realTrace (ownerCertificateDensity cfg.savedCenter cfg.theta *
    (e.center-cfg.savedCenter-e.movementSum))| ≤ rounding
  rw [hid,realTrace_mul_comm]
  exact (abs_realTrace_mul_density_le_norm
    (combination_isHermitian cfg.family cfg.family_hermitian _)
    (ownerCertificateDensity_mem cfg.savedCenter cfg.theta)).trans
      ((combination_norm_le cfg.family hunit _).trans hround)

end MatrixSpencer.MSManuscriptInputRadius
