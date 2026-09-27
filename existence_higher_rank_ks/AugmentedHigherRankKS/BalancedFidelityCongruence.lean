import AugmentedHigherRankKS.BalancedFidelityRegularity
import MatrixSpencer.KSArbitraryTransportContact
import MatrixSpencer.KrausContraction

/-! Opposite congruences and relative bounds for balanced fidelity estimates. -/
open Matrix MatrixSpencer
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1000000
namespace AugmentedHigherRankKS.BalancedRegularity
variable {n : Type*} [Fintype n] [DecidableEq n]
local instance balancedCongruenceCStar : CStarAlgebra (Matrix n n ℂ) := {}

theorem posDef_congruence {T S : Matrix n n ℂ} (hT : T.PosDef) (hS : S.PosDef) :
    (T*S*T).PosDef := by
  simpa only [hT.isHermitian.eq] using
    hS.conjTranspose_mul_mul_same (Matrix.mulVec_injective_iff_isUnit.mpr hT.isUnit)

/-- Opposite positive congruences leave the fidelity exactly unchanged. -/
theorem fidelity_opposite_congruence {T S M : Matrix n n ℂ}
    (hT : T.PosDef) (hS : S.PosDef) (hM : M.PosDef) :
    fidelity (T⁻¹*S*T⁻¹) (T*M*T) = fidelity S M := by
  letI : Invertible T := hT.isUnit.invertible
  let Z := transportOptimizer S M
  have hZ : Z.PosDef := transportOptimizer_posDef hS hM
  have hSZ := posDef_congruence hT.inv hS
  have hMZ := posDef_congruence hT hM
  have hW := posDef_congruence hT.inv hZ
  have hs : (T⁻¹*Z*T⁻¹)*(T*M*T)*(T⁻¹*Z*T⁻¹) = T⁻¹*S*T⁻¹ := by
    calc
      _ = T⁻¹*(Z*M*Z)*T⁻¹ := by
        simp only [Matrix.mul_assoc, Matrix.inv_mul_cancel_left_of_invertible,
          Matrix.mul_inv_cancel_left_of_invertible]
      _ = _ := by rw [transportOptimizer_solve hS hM]
  have he := KSArbitraryTransportContact.transport_unique hSZ hMZ hW hs
  rw [← trace_transportOptimizer_eq_fidelity hSZ hMZ, ← he]
  have hprod : (T*M*T)*(T⁻¹*Z*T⁻¹) = T*(M*Z)*T⁻¹ := by
    simp only [Matrix.mul_assoc, Matrix.mul_inv_cancel_left_of_invertible]
  rw [hprod, realTrace_mul_cycle]
  simp only [Matrix.mul_assoc, Matrix.inv_mul_cancel_left_of_invertible]
  exact trace_transportOptimizer_eq_fidelity hS hM

/-- Relative order bounds give relative operator-norm bounds. -/
theorem relative_norm_le {P X : Matrix n n ℂ} (hP : P.PosDef)
    (hX : X.IsHermitian) {b : ℝ} (hb : 0 ≤ b)
    (hlo : -b • P ≤ X) (hhi : X ≤ b • P) : ‖relative P X‖ ≤ b := by
  have hJ := (transportInverseSqrt_posDef hP).isHermitian
  have hrel : (relative P X).IsHermitian := by
    simpa only [relative, hJ.eq] using Matrix.isHermitian_conjTranspose_mul_mul
      (transportInverseSqrt P) hX
  have hl := hJ.isSelfAdjoint.conjugate_le_conjugate hlo
  have hh := hJ.isSelfAdjoint.conjugate_le_conjugate hhi
  change relative P (-b • P) ≤ relative P X at hl
  change relative P X ≤ relative P (b • P) at hh
  rw [relative_smul, relative_base hP] at hl hh
  exact KrausContraction.norm_le_of_order_interval hrel hb hl hh

theorem relative_frob_le {P X : Matrix n n ℂ} (hP : P.PosDef)
    (hX : X.IsHermitian) {b : ℝ} (hb : 0 ≤ b)
    (hlo : -b • P ≤ X) (hhi : X ≤ b • P) :
    frob (relative P X) ≤ Real.sqrt (Fintype.card n : ℝ)*b :=
  (frob_le_sqrt_card_mul_norm _).trans
    (mul_le_mul_of_nonneg_left (relative_norm_le hP hX hb hlo hhi) (Real.sqrt_nonneg _))

end AugmentedHigherRankKS.BalancedRegularity
