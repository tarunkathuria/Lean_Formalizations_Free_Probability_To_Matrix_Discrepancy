import HigherRankKSRuntime.StateCharts
import HigherRankKSRuntime.RuntimeStateBounds
import HigherRankKSRuntime.WalkExecution

/-! Every numerical Hessian and endpoint report is a legal value query on
nonnegative original reserves. The SDP accuracy theorem therefore applies. -/
noncomputable section
open Matrix MatrixSpencer Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace HigherRankKSRuntime.QueryBall
open AugmentedHigherRankKS ActiveEnumeration RuntimeParameters
open MatrixSpencer.RealRAM.JacobiIteration (Counted)
variable {N : ℕ} {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

theorem movement_reserves_nonnegative (p : Dimensions) (hp : p ∈ Domain)
    (A : Fin N → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef) (hsum : ∑ i, A i ≤ 1)
    (x₀ : Fin N → ℝ) (hx₀ : ∀ i, |x₀ i| ≤ 1)
    {z : EpochState (Fin N)} (hz : z ∈ epochDomain (a p) 4)
    (hc : NextEvent.Clean z (rho p) (zeta p))
    (u : EuclideanSpace ℝ (Fin (count z))) (hu : ‖u‖ ≤ radius p) :
    ∀ i, 0 ≤ reserve (movement (a p) z (extend z u) 1) i := by
  have hb := (RuntimeStateBounds.state_quadratic_query_domain p hp A hA hsum x₀ hx₀ hz hc u hu).2
  intro i
  by_cases hi : 0 < reserve z i
  · let ai : ActiveOwners z := ⟨i,(mem_positiveReserves z i).mpr hi⟩
    let j := (activeEquiv z).symm ai
    have hj := (hb j).1
    have he : activeEquiv z j = ai := (activeEquiv z).apply_symm_apply ai
    change zeta p ≤ reserve z (activeEquiv z j)-a p*(u j)^2 at hj
    rw [he] at hj
    change 0 ≤ reserve z i-a p*(1:ℝ)^2*(extend z u i)^2
    rw [one_pow,mul_one,show extend z u i = u j from extend_active z u ai]
    exact (theta_poly.positive p hp).le.trans hj
  · have hzi : reserve z i=0 := reserve_zero_of_not_positive hz i (by simpa using hi)
    change 0 ≤ reserve z i-a p*(1:ℝ)^2*(extend z u i)^2
    rw [extend_inactive z u i hi,hzi]
    simp

theorem report_accuracy (p : Dimensions) (hp : p ∈ Domain)
    (A : Fin N → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef) (hsum : ∑ i, A i ≤ 1)
    (β θ : ℝ) (x₀ : Fin N → ℝ) (hx₀ : ∀ i, |x₀ i| ≤ 1)
    (query : EpochState (Fin N) → Counted ℝ)
    (hquery : ∀ y, (∀ i, 0 ≤ reserve y i) →
      |(query y).value-epochPotential A β θ x₀ y| ≤ accuracy p)
    {z : EpochState (Fin N)} (hz : z ∈ epochDomain (a p) 4)
    (hc : NextEvent.Clean z (rho p) (zeta p))
    (u : EuclideanSpace ℝ (Fin (count z))) (hu : ‖u‖ ≤ radius p) :
    |(NextEvent.chartReport query (a p) z u).value-
      RuntimeCurvature.chart (center A x₀ z) (restrictedAtoms A z) β θ (a p)
        (restrictedPosition z) (restrictedReserve z) u| ≤ accuracy p := by
  rw [NextEvent.chartReport_value,← movement_runtime_chart_eq A β θ x₀ hz u]
  exact hquery _ (movement_reserves_nonnegative p hp A hA hsum x₀ hx₀ hz hc u hu)

end HigherRankKSRuntime.QueryBall

namespace HigherRankKSRuntime.NumericHessian
open MatrixSpencer KSNumericalHessian
variable {m : ℕ}

theorem queryAccuracy_of_ball (f report : Space m → ℝ) {t ν : ℝ}
    (hball : ∀ u, ‖u‖ ≤ 2*|t| → |report u-f u| ≤ ν) :
    KSFullManuscriptHessian.QueryAccuracy f report 0 t ν := by
  have hn (i : Fin m) : ‖coordinate i‖ = 1 := by simp [coordinate,EuclideanSpace.norm_single]
  have hsmul (v : Space m) (hv : ‖v‖ ≤ 2) : ‖t • v‖ ≤ 2*|t| := by
    rw [norm_smul,Real.norm_eq_abs]
    nlinarith [mul_le_mul_of_nonneg_left hv (abs_nonneg t)]
  have hneg (v : Space m) (hv : ‖v‖ ≤ 2) : ‖-(t • v)‖ ≤ 2*|t| := by
    rw [norm_neg]; exact hsmul v hv
  refine ⟨hball 0 (by simp),?_,?_⟩
  · intro i
    have hi : ‖coordinate i‖ ≤ 2 := by rw [hn]; norm_num
    simpa only [zero_add,zero_sub] using And.intro
      (hball _ (hsmul _ hi)) (hball _ (hneg _ hi))
  · intro i j hij
    have hp : ‖coordinate i+coordinate j‖ ≤ 2 :=
      (norm_add_le _ _).trans (by rw [hn,hn]; norm_num)
    have hm : ‖coordinate i-coordinate j‖ ≤ 2 :=
      (norm_sub_le _ _).trans (by rw [hn,hn]; norm_num)
    simpa only [zero_add,zero_sub] using And.intro (hball _ (hsmul _ hp))
      (And.intro (hball _ (hsmul _ hm)) (And.intro (hball _ (hneg _ hm)) (hball _ (hneg _ hp))))
end HigherRankKSRuntime.NumericHessian
