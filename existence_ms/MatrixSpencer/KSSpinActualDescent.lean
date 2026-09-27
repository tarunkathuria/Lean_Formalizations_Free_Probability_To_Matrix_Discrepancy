import MatrixSpencer.KSBalancedSpin
import MatrixSpencer.KSSpinDrift

/-!
# Concrete spin-source transport descent

The finite negative legal pair is connected to the exact first and second
derivatives of the moving natural-owner majorant on the physical source space.
-/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSSpinActualDescent
open KSBalancedSpin

variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
local instance : CStarAlgebra (Matrix n n ℂ) := {}

theorem acceleration_eq_legalUpper (B : ι → Matrix n n ℂ) (c : ι → ℝ)
    (hc : ∀ i, 0 ≤ c i) (S : Matrix n n ℂ) {Z : Matrix n n ℂ} (hZ : Z.PosDef)
    (J : Matrix n n ℂ) (x δ y : ι → ℝ)
    (hr : ∀ i, 0 < realTrace (atom B c Z i))
    (hlegal : (1 - KSFisher.gram (atom B c Z)) *ᵥ δ =
      (KSFisher.spinGram J (atom B c Z) - KSFisher.gram (atom B c Z) *
        Matrix.diagonal (fun i => 128 * x i * realTrace (Z * B i))) *ᵥ y) :
    let D := atom B c Z
    let P := balancedDensity S Z
    let z := fun i => 128 * x i * realTrace (Z * B i)
    realTrace (S * physicalAcceleration B Z
      (liftTransport Z ((1 / 8 : ℝ) • spinCompletion D J z δ y)) 64 x
      (coefficientDirection c (1 / 8) y) (fun i => realTrace (Z * B i))) =
      2 * KSSpinDrift.legalUpper P J D (KSSpinDrift.fisherWeight P D)
        (fun i => realTrace (D i) ^ 2) z 64 δ y := by
  dsimp only
  rw [normalized_acceleration_pairing B c hc S hZ _ 64 (1 / 8) (by norm_num)]
  simp_rw [spinCompletion_probe (atom B c Z) J _ δ y hlegal]
  have hcross : (∑ i, δ i * KSSpinDrift.fisherWeight (balancedDensity S Z) (atom B c Z) i *
      (128 * x i * realTrace (Z * B i)) * y i) / 64 =
      ∑ i, 2 * x i * realTrace (S * B i) * y i * δ i := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    unfold KSSpinDrift.fisherWeight
    change δ i * (mass B c S Z i / realTrace (atom B c Z i)) *
      (128 * x i * realTrace (Z * B i)) * y i / 64 = _
    field_simp [(hr i).ne']
    rw [trace_atom B c hZ, mass_eq B c S hZ]
    ring
  unfold KSSpinDrift.legalUpper
  rw [← spinCompletion_eq]
  simp_rw [KSSpinDrift.fisherWeight_mul_trace_sq _ _ hr]
  rw [hcross, Finset.sum_add_distrib]
  change 2 * ((1 / 8 : ℝ) ^ 2 * _ - ((∑ i, _ * mass B c S Z i * _) + _)) = _
  unfold mass
  ring

/-- The actual positive trace-and-prepare transport has a nonzero coefficient
direction and a Hermitian physical transport direction with zero first
derivative and strictly negative second derivative. All Fisher, projection,
and response estimates are discharged from the concrete source data. -/
theorem exists_transport_descent [Nonempty ι]
    (B : ι → Matrix n n ℂ) (c : ι → ℝ)
    (hB : ∀ i, (B i).PosSemidef) (hBne : ∀ i, B i ≠ 0) (hc : ∀ i, 0 < c i)
    {S Z J : Matrix n n ℂ} (hS : S.PosDef) (hZ : Z.PosDef)
    (htransport : Z * source B c S * Z = S)
    (hJ : J.IsHermitian) (hJJ : J * J = 1)
    (hJZ : J * Z = Z * J) (hJB : ∀ i, J * B i = B i * J) (x : ι → ℝ)
    (hz : ∀ i, |128 * x i * realTrace (Z * B i)| ≤ 1)
    (hsmall : ∀ i, realTrace (atom B c Z i) ^ 2 ≤ 1 / 64) :
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
    KSSpinDrift.exists_physical_negative_legal_direction D hD
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
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_smul, star_trivial, W, hW.eq]
  · have hvel := physical_spin_velocity_zero B c (fun i => (hc i).le) hZ hJZ
      64 (1 / 8) x (fun i => realTrace (Z * B i)) δ y (by norm_num at hlegal ⊢; exact hlegal)
    simpa only [show (2 : ℝ) * 64 = 128 by norm_num] using hvel
  · have heq := acceleration_eq_legalUpper B c (fun i => (hc i).le) S hZ J x δ y hr hlegal
    change realTrace (S * physicalAcceleration B Z
      (liftTransport Z ((1 / 8 : ℝ) • spinCompletion D J z δ y)) 64 x
      (coefficientDirection c (1 / 8) y) (fun i => realTrace (Z * B i))) < 0
    rw [heq]
    exact mul_neg_of_pos_of_neg (by norm_num) hnegative

end MatrixSpencer.KSSpinActualDescent
