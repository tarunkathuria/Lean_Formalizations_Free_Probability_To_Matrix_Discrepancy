import HigherRankKSRuntime.RuntimeHessianBounds

/-! The actual feasible clean controller state satisfies all numerical Hessian
and signed-walk regularity hypotheses. These are conclusions, not oracle inputs. -/
noncomputable section
open Matrix MatrixSpencer Set
open scoped BigOperators Topology ContDiff MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace HigherRankKSRuntime.RuntimeStateRegularity
open AugmentedHigherRankKS RuntimeParameters ActiveEnumeration RuntimeStateBounds RuntimeHessianBounds
variable {N : ℕ} {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- Ordinary twice differentiability of the actual full coefficient chart. -/
theorem state_chart_smooth
    (p : Dimensions) (hp : p ∈ Domain)
    (A : Fin N → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (k : ℕ) (hk : 1 ≤ k) (x₀ : Fin N → ℝ) (z : EpochState (Fin N)) :
    ContDiffAt ℝ 2 (RuntimeCurvature.chart
      (augmentedCenter (discrepancy A x₀ z) (budgetCenter A x₀ z))
      (restrictedAtoms A z) ((1:ℝ)/2^k) (theta p) (a p)
      (restrictedPosition z) (restrictedReserve z)) 0 := by
  exact (RuntimeCurvature.chart_smooth _ _ (fun i => hA _) k hk
    (theta_poly.positive p hp) (a p) _ _ (active_positive z)).of_le
      (WithTop.coe_le_coe.mpr (show (2:ℕ∞) ≤ ⊤ from le_top))

/-- All actual coordinate and mixed finite-difference query lines have the
proved derivative cap, including the unnormalized mixed directions. -/
theorem state_numeric_line_bounds
    (p : Dimensions) (hp : p ∈ Domain) (hd : (Fintype.card n : ℝ) ≤ p.D)
    (A : Fin N → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef) (hsum : ∑ i, A i ≤ 1)
    {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hN : ∀ i, ‖A i‖ ≤ ε)
    {r : ℕ} (hr : ∀ i, (A i).rank ≤ r) (k : ℕ) (hk : 1 ≤ k)
    (hrβ : (r:ℝ)^((1:ℝ)/2^k) ≤ 2)
    (x₀ : Fin N → ℝ) (hx₀ : ∀ i, |x₀ i| ≤ 1)
    {z : EpochState (Fin N)} (hz : z ∈ epochDomain (a p) 4)
    (hc : NextEvent.Clean z (rho p) (zeta p)) :
    NumericHessian.LineBounds (RuntimeCurvature.chart
      (augmentedCenter (discrepancy A x₀ z) (budgetCenter A x₀ z))
      (restrictedAtoms A z) ((1:ℝ)/2^k) (theta p) (a p)
      (restrictedPosition z) (restrictedReserve z)) 0 (stencil p) (M p) :=
  chart_numeric_line_bounds p hp hd _ (state_center_hermitian A hA x₀ z)
    (state_center_bound A hA hsum x₀ hx₀ hz) _ (fun i => hA _)
    (restricted_atoms_subisotropic A hA hsum z) hε hε1 (fun i => hN _) (fun i => hr _)
    k hk hrβ _ _ (active_position_cube hz) (active_clean hc).2 (active_reserve_upper hz)

/-- The norm-one direction actually returned by the tangent eigensolver
satisfies the scalar smoothness and remainder bound used by signed selection. -/
theorem state_walk_line_bounds
    (p : Dimensions) (hp : p ∈ Domain) (hd : (Fintype.card n : ℝ) ≤ p.D)
    (A : Fin N → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef) (hsum : ∑ i, A i ≤ 1)
    {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hN : ∀ i, ‖A i‖ ≤ ε)
    {r : ℕ} (hr : ∀ i, (A i).rank ≤ r) (k : ℕ) (hk : 1 ≤ k)
    (hrβ : (r:ℝ)^((1:ℝ)/2^k) ≤ 2)
    (x₀ : Fin N → ℝ) (hx₀ : ∀ i, |x₀ i| ≤ 1)
    {z : EpochState (Fin N)} (hz : z ∈ epochDomain (a p) 4)
    (hc : NextEvent.Clean z (rho p) (zeta p))
    (g : EuclideanSpace ℝ (Fin (count z))) (hg : ‖g‖ = 1) :
    ContDiffOn ℝ 3 (fun s : ℝ => RuntimeCurvature.chart
      (augmentedCenter (discrepancy A x₀ z) (budgetCenter A x₀ z))
      (restrictedAtoms A z) ((1:ℝ)/2^k) (theta p) (a p)
      (restrictedPosition z) (restrictedReserve z) (s•g)) (Icc (-(walk p)) (walk p)) ∧
    ∀ s ∈ Icc (-(walk p)) (walk p), |iteratedDeriv 3 (fun w : ℝ => RuntimeCurvature.chart
      (augmentedCenter (discrepancy A x₀ z) (budgetCenter A x₀ z))
      (restrictedAtoms A z) ((1:ℝ)/2^k) (theta p) (a p)
      (restrictedPosition z) (restrictedReserve z) (w•g)) s| ≤ M p :=
  chart_walk_line_bounds p hp hd _ (state_center_hermitian A hA x₀ z)
    (state_center_bound A hA hsum x₀ hx₀ hz) _ (fun i => hA _)
    (restricted_atoms_subisotropic A hA hsum z) hε hε1 (fun i => hN _) (fun i => hr _)
    k hk hrβ _ _ (active_position_cube hz) (active_clean hc).2 (active_reserve_upper hz) g hg

end HigherRankKSRuntime.RuntimeStateRegularity
