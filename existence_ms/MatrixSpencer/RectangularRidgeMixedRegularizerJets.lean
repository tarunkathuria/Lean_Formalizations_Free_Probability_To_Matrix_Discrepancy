import MatrixSpencer.RectangularRidgeActualTracePowerJets
import MatrixSpencer.RectangularRidgeCovarianceCalculus

/-!
# Actual mixed-regularizer line estimates

Both terms of the ridge regularizer are the existing actual functions. Their
first four line derivatives satisfy a common polynomial bound in root degree,
dimension, and inverse density floor.
-/
open Matrix Filter Topology
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
noncomputable section
namespace MatrixSpencer.RectangularRidgeMixedRegularizerJets
open RectangularRidgeActualRootJets RectangularRidgeActualTracePowerJets
variable {n : Type*} [Fintype n] [DecidableEq n]
local instance ridgeMixedRegularizerJetsCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance ridgeMixedRegularizerJetsRealSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance

/-- The density-only part of the actual mixed objective, on Hermitian matrices. -/
def regularizer (m : ℕ) (θ κ : ℝ) (S : Herm (n := n)) : ℝ :=
  dyadicTsallisPotential m θ S + tsallisPotential κ S

lemma regularizer_eq (m : ℕ) (θ κ : ℝ) (S : Herm (n := n)) :
    regularizer m θ κ S = RectangularRidgeCovarianceCalculus.regularizer m θ κ (S : Matrix n n ℂ) := rfl

lemma contDiffAt_regularizer (m : ℕ) (θ κ : ℝ) (S : Herm (n := n))
    (hS : (S : Matrix n n ℂ).PosDef) : ContDiffAt ℝ ∞ (regularizer m θ κ) S :=
  (contDiffAt_dyadicTsallisPotential m θ S hS).add (contDiffAt_tsallisPotential κ S hS)

variable [Nonempty n]

lemma sqrtRidge_jet_abs_le {κ : ℝ} (hκ : 0 ≤ κ)
    (S X : Herm (n := n)) (hS : (S : Matrix n n ℂ).PosDef) (hS1 : (S : Matrix n n ℂ) ≤ 1)
    {μ : ℝ} (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (hfloor : μ • (1 : Matrix n n ℂ) ≤ (S : Matrix n n ℂ)) (hX : ‖X‖ ≤ 1)
    (r : ℕ) (hr1 : 1 ≤ r) (hr4 : r ≤ 4) :
    |iteratedDeriv r (fun t => tsallisPotential κ (line S X t)) 0| ≤
      2 * κ * (Fintype.card n : ℝ) * (16 * (120 / μ) ^ 4) := by
  have h := dyadicTsallisPotential_jet_abs_le 1 (by norm_num) hκ S X hS hS1
    hμ hμ1 hfloor hX r hr1 hr4
  simpa only [dyadicTsallisPotential_one, pow_one, show (2 : ℝ)^4 = 16 from by norm_num] using h

/-- No derivative or symmetry bounds are assumptions of this actual line theorem. -/
theorem regularizer_jet_abs_le (m : ℕ) (hm : 1 ≤ m) {θ κ : ℝ} (hθ : 0 ≤ θ) (hκ : 0 ≤ κ)
    (S X : Herm (n := n)) (hS : (S : Matrix n n ℂ).PosDef) (hS1 : (S : Matrix n n ℂ) ≤ 1)
    {μ : ℝ} (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (hfloor : μ • (1 : Matrix n n ℂ) ≤ (S : Matrix n n ℂ)) (hX : ‖X‖ ≤ 1)
    (r : ℕ) (hr1 : 1 ≤ r) (hr4 : r ≤ 4) :
    |iteratedDeriv r (fun t => regularizer m θ κ (line S X t)) 0| ≤
      2 * (θ + κ) * (Fintype.card n : ℝ) * ((2 ^ m : ℝ) ^ 4 * (120 / μ) ^ 4) := by
  have hθc : ContDiffAt ℝ ∞ (fun t => dyadicTsallisPotential m θ (line S X t)) 0 := by
    exact ((show ContDiffAt ℝ ∞ (dyadicTsallisPotential m θ) (line S X 0) from
      by simpa only [line, zero_smul, add_zero] using contDiffAt_dyadicTsallisPotential m θ S hS).comp 0 (contDiff_line S X).contDiffAt)
  have hκc : ContDiffAt ℝ ∞ (fun t => tsallisPotential κ (line S X t)) 0 := by
    exact ((show ContDiffAt ℝ ∞ (tsallisPotential κ) (line S X 0) from
      by simpa only [line, zero_smul, add_zero] using contDiffAt_tsallisPotential κ S hS).comp 0 (contDiff_line S X).contDiffAt)
  have hp : 2 ≤ (2 : ℝ) ^ m := by
    simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hm
  have hp4 : (16 : ℝ) ≤ ((2 : ℝ) ^ m) ^ 4 := by
    simpa only [show (2 : ℝ) ^ 4 = 16 from by norm_num] using
      pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hp 4
  have ht := dyadicTsallisPotential_jet_abs_le m hm hθ S X hS hS1 hμ hμ1 hfloor hX r hr1 hr4
  have hk := sqrtRidge_jet_abs_le hκ S X hS hS1 hμ hμ1 hfloor hX r hr1 hr4
  change |iteratedDeriv r ((fun t => dyadicTsallisPotential m θ (line S X t)) +
    (fun t => tsallisPotential κ (line S X t))) 0| ≤ _
  rw [iteratedDeriv_add (hθc.of_le
    (WithTop.coe_le_coe.mpr (show (r : ℕ∞) ≤ ⊤ from le_top))) (hκc.of_le
    (WithTop.coe_le_coe.mpr (show (r : ℕ∞) ≤ ⊤ from le_top)))]
  apply (abs_add_le _ _).trans
  apply (add_le_add ht hk).trans
  have hscale := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hp4
    (by positivity : 0 ≤ (120 / μ) ^ 4))
    (by positivity : 0 ≤ 2 * κ * (Fintype.card n : ℝ))
  nlinarith [hscale]

end MatrixSpencer.RectangularRidgeMixedRegularizerJets
