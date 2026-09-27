import HigherRankKSRuntime.QueryBall
import HigherRankKSRuntime.CleanMovement
import HigherRankKSRuntime.RuntimeHessianBounds

/-! The rejected-preparation branch executes the actual numerical tangent
step. Its feasibility and strict potential decrease follow from the source
response and proved value regularity, with no supplied Hessian witness. -/
noncomputable section
open Matrix MatrixSpencer Set
open scoped BigOperators Topology ContDiff MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace HigherRankKSRuntime.RuntimeMove
open AugmentedHigherRankKS ActiveEnumeration RuntimeParameters ControllerLoop
open MatrixSpencer.RealRAM.JacobiIteration (Counted)
variable {N : ℕ} {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
set_option maxHeartbeats 800000

theorem good (p : Dimensions) (hp : p ∈ Domain) (hNp : p.N = N)
    (hd : (Fintype.card n : ℝ) ≤ p.D)
    (A : Fin N → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef) (hsum : ∑ i, A i ≤ 1)
    {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hN : ∀ i, ‖A i‖ ≤ ε)
    {r : ℕ} (hrank : ∀ i, (A i).rank ≤ r) (k : ℕ) (hk : 1 ≤ k) (hq : p.q=2^k)
    (hrβ : (r:ℝ)^((1:ℝ)/2^k) ≤ 2)
    (x₀ : Fin N → ℝ) (hx₀ : ∀ i, |x₀ i| ≤ 1)
    (query : EpochState (Fin N) → Counted ℝ)
    (hquery : ∀ y, (∀ i, 0 ≤ reserve y i) →
      |(query y).value-epochPotential A ((1:ℝ)/2^k) (theta p) x₀ y| ≤ accuracy p)
    {z : EpochState (Fin N)} (hz : z ∈ epochDomain (a p) 4) (hm : count z ≠ 0)
    (hclean : NextEvent.Clean z (rho p) (zeta p))
    (hlarge : ∀ i, 0 < reserve z i → eta p ≤ ‖A i‖)
    (hreject : ∀ i, -(p0 p/(2*a p)) < deriv (RuntimeCurvature.prepCurve
      (center A x₀ z) (restrictedAtoms A z) ((1:ℝ)/2^k) (theta p) (a p)
        (restrictedReserve z) i) 0) :
    (NextEvent.afterRejection query (a p) (stencil p) (walk p) z).value.Valid
      (a p) 4 (prep p) (walk p) z ∧
    epochPotential A ((1:ℝ)/2^k) (theta p) x₀
      ((NextEvent.afterRejection query (a p) (stencil p) (walk p) z).value.apply
        (a p) (prep p) (walk p) z) ≤ epochPotential A ((1:ℝ)/2^k) (theta p) x₀ z := by
  let f := RuntimeCurvature.chart (center A x₀ z) (restrictedAtoms A z)
    ((1:ℝ)/2^k) (theta p) (a p) (restrictedPosition z) (restrictedReserve z)
  let R := NextEvent.chartReport query (a p) z
  obtain ⟨g,hg,ho,hcurv⟩ := RuntimeStateBounds.state_negative_tangent_witness p hp hd
    A hA hsum hε hε1 hN hrank k hk hq hrβ x₀ hx₀ hz hm hlarge hreject
  have hg0 : g≠0 := by intro hh; rw [hh,norm_zero] at hg; norm_num at hg
  have htangent := Tangent.Frame.rank_pos_of_nonzero
    (Tangent.Frame.canonical (count z) (restrictedPosition z)) g hg0 ho
  let v := (WalkExecution.compute R (restrictedPosition z) (stencil p) (walk p) htangent).value
  have hv : ‖v‖=1 := WalkExecution.compute_unit _ _ _ _ _
  have ha := a_poly.positive p hp
  have hwalk := walk_poly.positive p hp
  have ht := stencil_poly.positive p hp
  have hρ : 0 ≤ rho p := (theta_poly.positive p hp).le
  have hζ : 0 ≤ zeta p := (theta_poly.positive p hp).le
  have hwr := walk_query_radius p hp
  have hfeas : movement (a p) z (extend z v) (walk p) ∈ epochDomain (a p) 4 :=
    NextEvent.clean_movement_feasible ha hρ
      (by rw [abs_of_pos hwalk]; linarith [hwr.2.1])
      (by linarith [hwr.2.2]) hz hclean v hv.le
  refine ⟨NextEvent.afterRejection_valid query (a p) 4 (prep p) (stencil p) (walk p)
    z htangent hfeas,?_⟩
  have hNpos : 0<N := by
    have hh := hp.1
    rw [hNp] at hh
    exact_mod_cast (show (0:ℝ)<N by linarith)
  have hH := RuntimeStateBounds.state_center_hermitian A hA x₀ z
  have hH5 := RuntimeStateBounds.state_center_bound A hA hsum x₀ hx₀ hz
  have hsum' := restricted_atoms_subisotropic A hA hsum z
  have hx := RuntimeStateBounds.active_position_cube hz
  have hc := (RuntimeStateBounds.active_clean hclean).2
  have hcu := RuntimeStateBounds.active_reserve_upper hz
  have hf : ContDiffAt ℝ 2 f 0 :=
    (RuntimeCurvature.chart_smooth (center A x₀ z) (restrictedAtoms A z) (fun i => hA _)
      k hk (theta_poly.positive p hp) (a p) (restrictedPosition z) (restrictedReserve z)
      (RuntimeStateBounds.active_positive z)).of_le
        (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have hline := RuntimeHessianBounds.chart_numeric_line_bounds p hp hd _ hH hH5
    (restrictedAtoms A z) (fun i => hA _) hsum' hε hε1 (fun i => hN _) (fun i => hrank _)
    k hk hrβ (restrictedPosition z) (restrictedReserve z) hx hc hcu
  have hball (u : KSNumericalHessian.Space (count z)) (hu : ‖u‖ ≤ radius p) :
      |(R u).value-f u| ≤ accuracy p :=
    QueryBall.report_accuracy p hp A hA hsum ((1:ℝ)/2^k) (theta p) x₀ hx₀ query hquery hz hclean u hu
  have hqst : KSFullManuscriptHessian.QueryAccuracy f (fun u => (R u).value) 0
      (stencil p) (accuracy p) := by
    apply NumericHessian.queryAccuracy_of_ball
    intro u hu
    apply hball u
    rw [abs_of_pos ht] at hu
    exact hu.trans (stencil_query_radius p hp).1
  have hlines := fun v hv => RuntimeHessianBounds.chart_walk_line_bounds p hp hd _ hH hH5
    (restrictedAtoms A z) (fun i => hA _) hsum' hε hε1 (fun i => hN _) (fun i => hrank _)
    k hk hrβ (restrictedPosition z) (restrictedReserve z) hx hc hcu v hv
  have hd := WalkExecution.potential_descent R (restrictedPosition z) (stencil p) (walk p)
    htangent f (count_le z) hNpos (M_poly.positive p hp) (gamma_poly.positive p hp)
    (accuracy_poly.positive p hp).le ht hwalk hf hline hqst
    (fun u hu => hball u (hu.trans hwr.1))
    (by simpa only [hNp] using stencil_le p)
    (by simpa only [hNp] using accuracy_le_stencil p)
    (walk_product p hp) (accuracy_le_walk p) hlines g hg ho hcurv
  have hzero : f 0 = epochPotential A ((1:ℝ)/2^k) (theta p) x₀ z := by
    dsimp only [f,ActiveEnumeration.center]
    rw [ActiveEnumeration.runtime_chart_eq A ((1:ℝ)/2^k) (theta p) x₀ hz]
    have he : extend z (0 : KSNumericalHessian.Space (count z))=0 := by
      apply norm_eq_zero.mp
      rw [extend_norm,norm_zero]
    rw [he]
    congr 1
    apply Prod.ext
    · funext i; simp [movement,position]
    · apply Prod.ext <;> funext i <;> simp [movement,spent,reserve]
  have hvalue : f (walk p • v) = epochPotential A ((1:ℝ)/2^k) (theta p) x₀
      (movement (a p) z (extend z v) (walk p)) :=
    runtime_scaled_chart_eq A ((1:ℝ)/2^k) (theta p) x₀ hz v (walk p)
  rw [NextEvent.afterRejection_value query (a p) (stencil p) (walk p) z htangent]
  change epochPotential A ((1:ℝ)/2^k) (theta p) x₀ (movement (a p) z (extend z v) (walk p)) ≤ _
  change f (walk p • v) ≤ f 0-gamma p*(walk p)^2/2 at hd
  rw [hvalue,hzero] at hd
  have hgamma := gamma_poly.positive p hp
  have hdec : 0 ≤ gamma p*(walk p)^2/2 := by positivity
  linarith
end HigherRankKSRuntime.RuntimeMove
