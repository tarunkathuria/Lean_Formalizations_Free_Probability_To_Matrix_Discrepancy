import SeamlessKS.Projection
import MatrixSpencer.KSSpinActualDescent

/-!
# Actual transport directions with the smooth-source probe cap

The parameter `x` in this algebraic theorem is a formal slope parameter,
not the actual walk position. For the smooth source it will be instantiated
by `-c′(position)/128`. No relation between `c` and this parameter is assumed.
The general scalar-source moving-majorant theorem must separately compare
its actual second derivative to the baseline acceleration using `c″ ≤ -128`.
-/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace SeamlessKS.PhysicalDescent
open MatrixSpencer MatrixSpencer.KSBalancedSpin MatrixSpencer.KSSpinActualDescent

variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
local instance : CStarAlgebra (Matrix n n ℂ) := {}

/-- Positive source data and bounded slopes yield a nonzero coefficient
and Hermitian transport direction, with legal zero center velocity and a
strictly negative baseline acceleration. The covariance and all Fisher
estimates are constructed internally from the actual source data. -/
theorem exists_transport_descent [Nonempty ι]
    (B : ι → Matrix n n ℂ) (c : ι → ℝ)
    (hB : ∀ i, (B i).PosSemidef) (hBne : ∀ i, B i ≠ 0) (hc : ∀ i, 0 < c i)
    {S Z J : Matrix n n ℂ} (hS : S.PosDef) (hZ : Z.PosDef)
    (htransport : Z * source B c S * Z = S)
    (hJ : J.IsHermitian) (hJJ : J * J = 1)
    (hJZ : J * Z = Z * J) (hJB : ∀ i, J * B i = B i * J) (x : ι → ℝ)
    (hz : ∀ i, |128 * x i * realTrace (Z * B i)| ≤ 1)
    (hsmall : ∀ i, realTrace (atom B c Z i) ^ 2 ≤ (200 / 81 : ℝ) / 64) :
    ∃ h : ι → ℝ, ∃ U : Matrix n n ℂ, h ≠ 0 ∧ U.IsHermitian ∧
      physicalForce B J 64 x h (fun i => realTrace (Z * B i)) - Z⁻¹ * U * Z⁻¹ +
        source B c U = 0 ∧
      realTrace (S * physicalAcceleration B Z U 64 x h
        (fun i => realTrace (Z * B i))) < 0 := by
  let D := atom B c Z
  let P := balancedDensity S Z
  let z := fun i => 128 * x i * realTrace (Z * B i)
  have hD : ∀ i, (D i).PosSemidef := atom_posSemidef B c hB Z
  have hr : ∀ i, 0 < realTrace (D i) := trace_atom_pos B c hB hBne hc hZ
  have hm : ∀ i, 0 < realTrace (P * D i) := mass_pos B c hB hBne hc hS hZ
  have hfix : P = ∑ i, realTrace (P * D i) • D i :=
    balancedDensity_eq_sum B c (fun i => (hc i).le) hZ htransport
  have hcomm : ∀ i, J * D i = D i * J := atom_commute B c hJZ hJB
  obtain ⟨δ, y, hy, hlegal, hnegative⟩ :=
    SeamlessKS.Projection.exists_physical_negative_legal_direction D hD
      (balancedDensity_posDef hS hZ).posSemidef hJ hJJ hcomm hr hm hfix z hz hsmall
  let W := spinCompletion D J z δ y
  let U := liftTransport Z ((1 / 8 : ℝ) • W)
  refine ⟨coefficientDirection c (1 / 8) y, U, ?_, ?_, ?_, ?_⟩
  · intro hzero
    apply hy
    funext i
    have hi := congrFun hzero i
    change (1 / 8 : ℝ) * Real.sqrt (c i) * y i = 0 at hi
    exact (mul_eq_zero.mp hi).resolve_left
      (mul_ne_zero (by norm_num) (Real.sqrt_pos.mpr (hc i)).ne')
  · apply liftTransport_isHermitian Z
    have hW := spinCompletion_isHermitian D (fun i => (hD i).isHermitian) hJ hcomm z δ y
    simp only [Matrix.IsHermitian, Matrix.conjTranspose_smul, star_trivial, W, hW.eq]
  · have hvel := physical_spin_velocity_zero B c (fun i => (hc i).le) hZ hJZ
      64 (1 / 8) x (fun i => realTrace (Z * B i)) δ y (by norm_num at hlegal ⊢; exact hlegal)
    simpa only [show (2 : ℝ) * 64 = 128 by norm_num] using hvel
  · have heq := acceleration_eq_legalUpper B c (fun i => (hc i).le) S hZ J x δ y hr hlegal
    change realTrace (S * physicalAcceleration B Z
      (liftTransport Z ((1 / 8 : ℝ) • spinCompletion D J z δ y)) 64 x
      (coefficientDirection c (1 / 8) y) (fun i => realTrace (Z * B i))) < 0
    rw [heq]
    exact mul_neg_of_pos_of_neg (by norm_num) hnegative


end SeamlessKS.PhysicalDescent
