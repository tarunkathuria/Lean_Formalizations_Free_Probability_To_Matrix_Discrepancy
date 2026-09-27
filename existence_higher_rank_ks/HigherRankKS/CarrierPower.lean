import MatrixSpencer.DensityDomain
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import HigherRankKS.MatrixPowerContinuity

/-! The concrete nonlinear carrier used in Part III. Its trace factor is
evaluated at the same matrix as its fractional power. -/

open Matrix MatrixSpencer
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

noncomputable section
namespace HigherRankKS

variable {n : Type*} [Fintype n] [DecidableEq n]
local instance carrierPowerCStar : CStarAlgebra (Matrix n n ℂ) := {}

/-- The homogeneous power source Fβ(M) = (Tr M)^β M^(1-β). -/
def carrierPower (β : ℝ) (M : Matrix n n ℂ) : Matrix n n ℂ :=
  (Real.rpow (realTrace M) β) • CFC.rpow M (1 - β)

theorem carrierPower_posSemidef (β : ℝ) {M : Matrix n n ℂ}
    (hM : M.PosSemidef) : (carrierPower β M).PosSemidef := by
  apply Matrix.nonneg_iff_posSemidef.mp
  exact smul_nonneg (Real.rpow_nonneg (realTrace_nonneg hM) β) CFC.rpow_nonneg

theorem carrierPower_isHermitian (β : ℝ) {M : Matrix n n ℂ}
    (hM : M.PosSemidef) : (carrierPower β M).IsHermitian :=
  (carrierPower_posSemidef β hM).isHermitian

@[simp] theorem carrierPower_zero {β : ℝ} (hβ : 0 < β) :
    carrierPower β (0 : Matrix n n ℂ) = 0 := by
  simp [carrierPower, realTrace, Real.zero_rpow hβ.ne']

/-- Continuity also holds when the carrier becomes singular. -/
theorem continuous_carrierPower_of_psd {X : Type*} [TopologicalSpace X]
    {M : X → Matrix n n ℂ} (hM : Continuous M)
    (hpos : ∀ x, (M x).PosSemidef) {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1) :
    Continuous (fun x => carrierPower β (M x)) := by
  have ht : Continuous (fun x => Real.rpow (realTrace (M x)) β) :=
    (continuous_realTrace.comp hM).rpow_const (fun _ => Or.inr hβ)
  exact ht.smul (continuous_matrix_rpow_of_psd hM hpos (sub_nonneg.mpr hβ1))

end HigherRankKS
