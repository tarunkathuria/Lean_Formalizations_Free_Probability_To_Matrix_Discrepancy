import HigherRankKS.CarrierPower
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.IntegralRepresentation
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# First derivatives and the positive trace-factor term

Operator monotonicity makes every positive-direction derivative of the
fractional power positive. Differentiating the concrete carrier then
isolates its trace-factor contribution, which is the term used in the
endpoint certificate.
-/

open Matrix MatrixSpencer Set Filter
open scoped Topology MatrixOrder ComplexOrder Matrix.Norms.L2Operator

noncomputable section
namespace HigherRankKS

variable {n : Type*} [Fintype n] [DecidableEq n]
local instance carrierDerivativeCStar : CStarAlgebra (Matrix n n ℂ) := {}

theorem matrix_derivative_nonneg_of_right_order
    {f : ℝ → Matrix n n ℂ} {V : Matrix n n ℂ}
    (hf : HasDerivAt f V 0) (horder : ∀ t : ℝ, 0 < t → f 0 ≤ f t) :
    V.PosSemidef := by
  apply Matrix.nonneg_iff_posSemidef.mp
  apply ge_of_tendsto hf.tendsto_slope_zero_right
  filter_upwards [self_mem_nhdsWithin] with t ht
  simp only [zero_add]
  exact smul_nonneg (inv_nonneg.mpr ht.le) (sub_nonneg.mpr (horder t ht))

theorem matrix_rpow_derivative_posSemidef
    {M U V : Matrix n n ℂ} {α : ℝ} (hα : α ∈ Icc 0 1)
    (hU : U.PosSemidef)
    (hderiv : HasDerivAt (fun t : ℝ => CFC.rpow (M + t • U) α) V 0) :
    V.PosSemidef := by
  apply matrix_derivative_nonneg_of_right_order hderiv
  intro t ht
  simp only [zero_smul, add_zero]
  exact CFC.rpow_le_rpow hα (le_add_of_nonneg_right (smul_nonneg ht.le hU.nonneg))

theorem hasDerivAt_carrierPower_curve
    {M U V : Matrix n n ℂ} (hp : 0 < realTrace M) {β : ℝ}
    (hderiv : HasDerivAt (fun t : ℝ => CFC.rpow (M + t • U) (1 - β)) V 0) :
    HasDerivAt (fun t : ℝ => carrierPower β (M + t • U))
      ((β * (realTrace M) ^ (β - 1) * realTrace U) • CFC.rpow M (1 - β) +
        (realTrace M) ^ β • V) 0 := by
  have ht : HasDerivAt (fun t : ℝ => realTrace (M + t • U)) (realTrace U) 0 := by
    simp only [realTrace_add, realTrace_smul]
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (realTrace U)).const_add (realTrace M)
  have hp' : realTrace (M + (0 : ℝ) • U) ≠ 0 := by simpa using hp.ne'
  have hr := (ht.rpow_const (p := β) (Or.inl hp')).smul hderiv
  simpa [carrierPower, Pi.smul_apply, add_comm, mul_assoc, mul_left_comm, mul_comm]
    using hr

/-- After removing its explicit trace-factor contribution, the carrier's
positive-direction derivative is still PSD. -/
theorem carrierPower_derivative_lower
    {M U V D : Matrix n n ℂ} {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (hp : 0 < realTrace M) (hU : U.PosSemidef)
    (hpower : HasDerivAt (fun t : ℝ => CFC.rpow (M + t • U) (1 - β)) V 0)
    (hcarrier : HasDerivAt (fun t : ℝ => carrierPower β (M + t • U)) D 0) :
    (β * (realTrace M) ^ (β - 1) * realTrace U) • CFC.rpow M (1 - β) ≤ D := by
  have heq := hcarrier.unique (hasDerivAt_carrierPower_curve hp hpower)
  rw [heq]
  exact le_add_of_nonneg_right
    (smul_nonneg (Real.rpow_nonneg hp.le _)
      (matrix_rpow_derivative_posSemidef ⟨by linarith, by linarith⟩ hU hpower).nonneg)

end HigherRankKS
