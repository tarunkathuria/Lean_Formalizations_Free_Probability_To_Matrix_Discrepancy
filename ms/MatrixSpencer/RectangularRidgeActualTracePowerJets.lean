import MatrixSpencer.RectangularRidgeRootJetsInverseFloor
import MatrixSpencer.RectangularRidgePowerJetBounds
import MatrixSpencer.DyadicTsallisHessian
import MatrixSpencer.KSComplexObjectiveBound

/-!
# Explicit derivatives of the actual dyadic Tsallis trace power

The function here is the existing iterated positive square root raised to its
actual integer power. All bounds concern real affine perturbations of a positive
density. There is no binomial-series identification or derivative-bound premise.
-/
open Matrix Filter Topology
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
noncomputable section
namespace MatrixSpencer.RectangularRidgeActualTracePowerJets
open RectangularRidgeActualRootJets RectangularRidgeRootJetsInverseFloor
variable {n : Type*} [Fintype n] [DecidableEq n]
local instance ridgeActualTracePowerJetsCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance ridgeActualTracePowerJetsRealSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance

lemma realTrace_abs_le (A : Matrix n n ℂ) : |realTrace A| ≤ (Fintype.card n : ℝ) * ‖A‖ :=
  (Complex.abs_re_le_norm (Matrix.trace A)).trans (KSComplexObjectiveBound.norm_trace_le_card_mul_norm A)

lemma iteratedDeriv_realTrace {f : ℝ → Matrix n n ℂ} {t : ℝ}
    (hf : ContDiffAt ℝ ∞ f t) (r : ℕ) :
    iteratedDeriv r (fun u => realTrace (f u)) t = realTrace (iteratedDeriv r f t) := by
  rw [iteratedDeriv_eq_iteratedFDeriv]
  change iteratedFDeriv ℝ r ((realTraceCLM (n := n)) ∘ f) t (fun _ => 1) = _
  rw [(realTraceCLM (n := n)).iteratedFDeriv_comp_left hf
    (WithTop.coe_le_coe.mpr (show (r : ℕ∞) ≤ ⊤ from le_top))]
  rfl

variable [Nonempty n]

lemma matrix_power_jet_norm_le (m : ℕ) (S X : Herm (n := n))
    (hS : (S : Matrix n n ℂ).PosDef) (hS1 : (S : Matrix n n ℂ) ≤ 1)
    {μ : ℝ} (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (hfloor : μ • (1 : Matrix n n ℂ) ≤ (S : Matrix n n ℂ)) (hX : ‖X‖ ≤ 1)
    (r : ℕ) (hr1 : 1 ≤ r) (hr4 : r ≤ 4) :
    ‖iteratedDeriv r (fun t => matrixPath m S X t ^ (2 ^ m - 1)) 0‖ ≤
      (2 ^ m : ℝ) ^ 4 * (120 / μ) ^ 4 := by
  have hbound := matrixPath_jet_bounds m S X hS hμ hμ1 hfloor hX
  have hnorm : ‖matrixPath m S X 0‖ ≤ 1 := by
    rw [matrixPath_zero]
    exact root_norm_le_one m hS.posSemidef hS1
  have ha : 1 ≤ 120 / μ := (le_div_iff₀ hμ).mpr (by linarith)
  have hp : (2 ^ m - 1 : ℕ) + 1 = 2 ^ m := Nat.sub_add_cancel (one_le_pow₀ (by norm_num : (1 : ℕ) ≤ 2))
  have hh := RectangularRidgePowerJetBounds.power_jet_norm_le
    ((contDiffAt_matrixPath m S X hS).of_le
      (WithTop.coe_le_coe.mpr (show (4 : ℕ∞) ≤ ⊤ from le_top))) ha hnorm
    (by simpa only [pow_one] using hbound.1) hbound.2.1 hbound.2.2.1 hbound.2.2.2
    (2 ^ m - 1) r hr1 hr4
  simpa only [hp, Nat.cast_pow, Nat.cast_ofNat] using hh

lemma trace_power_jet_abs_le (m : ℕ) (S X : Herm (n := n))
    (hS : (S : Matrix n n ℂ).PosDef) (hS1 : (S : Matrix n n ℂ) ≤ 1)
    {μ : ℝ} (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (hfloor : μ • (1 : Matrix n n ℂ) ≤ (S : Matrix n n ℂ)) (hX : ‖X‖ ≤ 1)
    (r : ℕ) (hr1 : 1 ≤ r) (hr4 : r ≤ 4) :
    |iteratedDeriv r (fun t => realTrace (matrixPath m S X t ^ (2 ^ m - 1))) 0| ≤
      (Fintype.card n : ℝ) * ((2 ^ m : ℝ) ^ 4 * (120 / μ) ^ 4) := by
  rw [iteratedDeriv_realTrace ((contDiffAt_matrixPath m S X hS).pow _) r]
  exact (realTrace_abs_le _).trans (mul_le_mul_of_nonneg_left
    (matrix_power_jet_norm_le m S X hS hS1 hμ hμ1 hfloor hX r hr1 hr4) (Nat.cast_nonneg _))

lemma weight_abs_le (m : ℕ) (hm : 1 ≤ m) {θ : ℝ} (hθ : 0 ≤ θ) :
    |θ * (2 ^ m : ℝ) / ((2 ^ m : ℝ) - 1)| ≤ 2 * θ := by
  have hp : 2 ≤ (2 : ℝ) ^ m := by
    simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hm
  have hd : 0 < (2 : ℝ) ^ m - 1 := by linarith
  rw [abs_of_nonneg (div_nonneg (mul_nonneg hθ (by positivity)) hd.le)]
  apply (div_le_iff₀ hd).mpr
  nlinarith

/-- The actual dyadic regularizer has a uniform polynomial fourth-order line bound. -/
theorem dyadicTsallisPotential_jet_abs_le (m : ℕ) (hm : 1 ≤ m) {θ : ℝ} (hθ : 0 ≤ θ)
    (S X : Herm (n := n)) (hS : (S : Matrix n n ℂ).PosDef) (hS1 : (S : Matrix n n ℂ) ≤ 1)
    {μ : ℝ} (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (hfloor : μ • (1 : Matrix n n ℂ) ≤ (S : Matrix n n ℂ)) (hX : ‖X‖ ≤ 1)
    (r : ℕ) (hr1 : 1 ≤ r) (hr4 : r ≤ 4) :
    |iteratedDeriv r (fun t => dyadicTsallisPotential m θ (line S X t)) 0| ≤
      2 * θ * (Fintype.card n : ℝ) * ((2 ^ m : ℝ) ^ 4 * (120 / μ) ^ 4) := by
  have he : (fun t => dyadicTsallisPotential m θ (line S X t)) =
      (fun t => (θ * (2 ^ m : ℝ) / ((2 ^ m : ℝ) - 1)) *
        realTrace (matrixPath m S X t ^ (2 ^ m - 1))) := by
    funext t
    simp only [dyadicTsallisPotential, dyadicTsallisRegularizer, matrixPath, path,
      hermitianDyadicRoot_coe]
  have hc : ContDiffAt ℝ ∞ (fun t => realTrace (matrixPath m S X t ^ (2 ^ m - 1))) 0 := by
    simpa only [Function.comp_def, realTraceCLM_apply] using
      (realTraceCLM (n := n)).contDiff.contDiffAt.comp 0
        ((contDiffAt_matrixPath m S X hS).pow (2 ^ m - 1))
  rw [he, iteratedDeriv_const_mul (hc.of_le
    (WithTop.coe_le_coe.mpr (show (r : ℕ∞) ≤ ⊤ from le_top))), abs_mul]
  have hh := mul_le_mul (weight_abs_le m hm hθ)
    (trace_power_jet_abs_le m S X hS hS1 hμ hμ1 hfloor hX r hr1 hr4)
    (abs_nonneg _) (mul_nonneg (by norm_num) hθ)
  exact hh.trans_eq (by ring)

end MatrixSpencer.RectangularRidgeActualTracePowerJets
