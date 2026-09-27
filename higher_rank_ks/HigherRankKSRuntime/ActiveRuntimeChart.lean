import HigherRankKSRuntime.ActiveChart
import HigherRankKSRuntime.RuntimeCurvature

/-! The finite numeric Hessian chart is exactly the original-owner state potential. -/
noncomputable section
open Matrix MatrixSpencer
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace HigherRankKSRuntime.ActiveEnumeration
open AugmentedHigherRankKS
variable {N : ℕ} {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

theorem runtime_chart_eq (A : Fin N → Matrix n n ℂ) (β θ : ℝ)
    (x₀ : Fin N → ℝ) {a R : ℝ} {z : EpochState (Fin N)} (hz : z ∈ epochDomain a R)
    (v : EuclideanSpace ℝ (Fin (count z))) :
    RuntimeCurvature.chart (augmentedCenter (discrepancy A x₀ z) (budgetCenter A x₀ z))
      (restrictedAtoms A z) β θ a (restrictedPosition z) (restrictedReserve z) v =
      epochPotential A β θ x₀ (movement a z (extend z v) 1) := by
  have hh := movement_chart_eq A β θ x₀ hz v 1
  simpa only [one_smul,one_pow,mul_one,RuntimeCurvature.chart,Frames.coefficientForce] using hh.symm

theorem runtime_scaled_chart_eq (A : Fin N → Matrix n n ℂ) (β θ : ℝ)
    (x₀ : Fin N → ℝ) {a R : ℝ} {z : EpochState (Fin N)} (hz : z ∈ epochDomain a R)
    (v : EuclideanSpace ℝ (Fin (count z))) (t : ℝ) :
    RuntimeCurvature.chart (augmentedCenter (discrepancy A x₀ z) (budgetCenter A x₀ z))
      (restrictedAtoms A z) β θ a (restrictedPosition z) (restrictedReserve z) (t • v) =
      epochPotential A β θ x₀ (movement a z (extend z v) t) := by
  have hh := movement_chart_eq A β θ x₀ hz v t
  have hl := RuntimeCurvature.chart_line
    (augmentedCenter (discrepancy A x₀ z) (budgetCenter A x₀ z))
    (restrictedAtoms A z) β θ a (restrictedPosition z) (restrictedReserve z) v t
  change RuntimeCurvature.chart _ _ _ _ _ _ _ (t • v) = _ at hl
  rw [hl]
  exact hh.symm
end HigherRankKSRuntime.ActiveEnumeration
