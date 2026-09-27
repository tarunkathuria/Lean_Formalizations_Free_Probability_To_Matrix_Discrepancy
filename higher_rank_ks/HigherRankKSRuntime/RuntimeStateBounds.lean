import HigherRankKSRuntime.ActiveRuntimeChart
import HigherRankKSRuntime.NextEvent
import AugmentedHigherRankKS.EpochBounds

/-! Ordinary feasible-state invariants discharge the input and query-domain
hypotheses of the actual local curvature theorem. Active labels are retained
original owners, with the exact original four-block center. -/
noncomputable section
open Matrix MatrixSpencer Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace HigherRankKSRuntime.RuntimeStateBounds
open AugmentedHigherRankKS ActiveEnumeration RuntimeParameters
variable {N : ℕ} {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

theorem active_positive (z : EpochState (Fin N)) (i : Fin (count z)) :
    0 < restrictedReserve z i :=
  (mem_positiveReserves z _).mp (activeEquiv z i).property

theorem active_position_cube {a : ℝ} {z : EpochState (Fin N)}
    (hz : z ∈ epochDomain a 4) : ∀ i, |restrictedPosition z i| ≤ 1 := by
  intro i
  exact abs_le.mpr ⟨(hz (activeEquiv z i)).1,(hz (activeEquiv z i)).2.1⟩

theorem active_reserve_upper {a : ℝ} {z : EpochState (Fin N)}
    (hz : z ∈ epochDomain a 4) : ∀ i, restrictedReserve z i ≤ 4*a := by
  intro i
  have hi := (hz (activeEquiv z i)).2.2.2.2.2.1
  simpa only [mul_comm] using hi

theorem active_clean {z : EpochState (Fin N)} {ρ ζ : ℝ}
    (hc : NextEvent.Clean z ρ ζ) :
    (∀ i, ρ < 1-|restrictedPosition z i|) ∧
      (∀ i, 2*ζ ≤ restrictedReserve z i) := by
  constructor
  · intro i
    exact (hc (activeEquiv z i) (active_positive z i)).1
  · intro i
    exact (hc (activeEquiv z i) (active_positive z i)).2

theorem active_atom_nonzero (p : Dimensions) (hp : p ∈ Domain)
    (A : Fin N → Matrix n n ℂ) (z : EpochState (Fin N))
    (hlarge : ∀ i, 0 < reserve z i → eta p ≤ ‖A i‖) :
    ∀ i, restrictedAtoms A z i ≠ 0 := by
  intro i hi
  have hb := hlarge (activeEquiv z i) (active_positive z i)
  change eta p ≤ ‖restrictedAtoms A z i‖ at hb
  rw [hi,norm_zero] at hb
  exact (not_le_of_gt (theta_poly.positive p hp)) hb

theorem active_count_bound (p : Dimensions) (hN : (N:ℝ) ≤ p.N)
    (z : EpochState (Fin N)) : (count z : ℝ) ≤ p.N := by
  have hh : (count z : ℝ) ≤ (N : ℝ) := by exact_mod_cast count_le z
  exact hh.trans hN

theorem state_center_hermitian (A : Fin N → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) (x₀ : Fin N → ℝ) (z : EpochState (Fin N)) :
    (augmentedCenter (discrepancy A x₀ z) (budgetCenter A x₀ z)).IsHermitian :=
  augmentedCenter_isHermitian (discrepancy_isHermitian A hA x₀ z)
    (budgetCenter_isHermitian A hA x₀ z)

theorem state_center_bound (A : Fin N → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) (hsum : ∑ i, A i ≤ 1)
    (x₀ : Fin N → ℝ) (hx₀ : ∀ i, |x₀ i| ≤ 1)
    {a : ℝ} {z : EpochState (Fin N)} (hz : z ∈ epochDomain a 4) :
    ‖augmentedCenter (discrepancy A x₀ z) (budgetCenter A x₀ z)‖ ≤ 5 :=
  epoch_center_norm_le_five A hA hsum x₀ hx₀ hz

/-- Center and reserve bounds hold on every finite-difference or walk query in
the prescribed ball, as consequences of the clean feasible state. -/
theorem state_quadratic_query_domain (p : Dimensions) (hp : p ∈ Domain)
    (A : Fin N → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef) (hsum : ∑ i, A i ≤ 1)
    (x₀ : Fin N → ℝ) (hx₀ : ∀ i, |x₀ i| ≤ 1)
    {z : EpochState (Fin N)} (hz : z ∈ epochDomain (a p) 4)
    (hc : NextEvent.Clean z (rho p) (zeta p))
    (u : EuclideanSpace ℝ (Fin (count z))) (hu : ‖u‖ ≤ radius p) :
    ‖augmentedCenter (discrepancy A x₀ z) (budgetCenter A x₀ z)+
      Frames.coefficientForce (restrictedAtoms A z) (restrictedPosition z) u‖ ≤ 8 ∧
    (∀ i, zeta p ≤ restrictedReserve z i-a p*(u i)^2 ∧
      restrictedReserve z i-a p*(u i)^2 ≤ 8*a p) := by
  exact runtime_quadratic_query_domain p hp (restrictedAtoms A z)
    (fun i => hA _) (restricted_atoms_subisotropic A hA hsum z)
    _ (state_center_bound A hA hsum x₀ hx₀ hz)
    (restrictedPosition z) (active_position_cube hz)
    (restrictedReserve z) (active_clean hc).2 (active_reserve_upper hz) u hu

/-- The preparation query has the same uniform input domain. -/
theorem state_preparation_query_domain (p : Dimensions) (hp : p ∈ Domain)
    (A : Fin N → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef) (hsum : ∑ i, A i ≤ 1)
    (hN : ∀ i, ‖A i‖ ≤ 1)
    (x₀ : Fin N → ℝ) (hx₀ : ∀ i, |x₀ i| ≤ 1)
    {z : EpochState (Fin N)} (hz : z ∈ epochDomain (a p) 4)
    (hc : NextEvent.Clean z (rho p) (zeta p))
    (i : Fin (count z)) {t : ℝ} (ht : 0 ≤ t) (htu : t ≤ prep p) :
    ‖augmentedCenter (discrepancy A x₀ z) (budgetCenter A x₀ z)+
      augmentedCenter 0 ((t/a p) • restrictedAtoms A z i)‖ ≤ 8 ∧
    (∀ j, zeta p ≤ restrictedReserve z j-(Pi.single i t : Fin (count z) → ℝ) j ∧
      restrictedReserve z j-(Pi.single i t : Fin (count z) → ℝ) j ≤ 8*a p) := by
  exact runtime_preparation_query_domain p hp (restrictedAtoms A z) (fun i => hA _)
    (fun i => hN _) _ (state_center_bound A hA hsum x₀ hx₀ hz)
    (restrictedReserve z) (active_clean hc).2 (active_reserve_upper hz) i ht htu

/-- At the actual state, rejection of all actual preparation derivatives
produces the quantitative tangent witness used by the numerical eigensolver.
All matrix, reserve, center and optimizer hypotheses come from input/state
invariants; no favorable response is assumed. -/
theorem state_negative_tangent_witness
    (p : Dimensions) (hp : p ∈ Domain) (hd : (Fintype.card n : ℝ) ≤ p.D)
    (A : Fin N → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef) (hsum : ∑ i, A i ≤ 1)
    {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hN : ∀ i, ‖A i‖ ≤ ε)
    {r : ℕ} (hr : ∀ i, (A i).rank ≤ r) (k : ℕ) (hk : 1 ≤ k) (hq : p.q=2^k)
    (hrβ : (r:ℝ)^((1:ℝ)/2^k) ≤ 2)
    (x₀ : Fin N → ℝ) (hx₀ : ∀ i, |x₀ i| ≤ 1)
    {z : EpochState (Fin N)} (hz : z ∈ epochDomain (a p) 4) (hm : count z ≠ 0)
    (hlarge : ∀ i, 0 < reserve z i → eta p ≤ ‖A i‖)
    (hreject : ∀ i, -(p0 p/(2*a p)) < deriv (RuntimeCurvature.prepCurve
      (augmentedCenter (discrepancy A x₀ z) (budgetCenter A x₀ z))
      (restrictedAtoms A z) ((1:ℝ)/2^k) (theta p) (a p) (restrictedReserve z) i) 0) :
    ∃ g : EuclideanSpace ℝ (Fin (count z)), ‖g‖=1 ∧
      inner ℝ (restrictedPosition z) g=0 ∧
      KSRayleighAccuracy.realRayleigh (KSNumericalHessian.hessian
        (RuntimeCurvature.chart
          (augmentedCenter (discrepancy A x₀ z) (budgetCenter A x₀ z))
          (restrictedAtoms A z) ((1:ℝ)/2^k) (theta p) (a p)
          (restrictedPosition z) (restrictedReserve z)) 0) g ≤ -4*gamma p := by
  apply RuntimeCurvature.runtime_negative_tangent_witness (Nat.pos_of_ne_zero hm) p hp hd
    _ (state_center_hermitian A hA x₀ z)
    ((state_center_bound A hA hsum x₀ hx₀ hz).trans (by norm_num))
    (restrictedAtoms A z) (fun i => hA _) (restricted_atoms_subisotropic A hA hsum z)
    hε hε1 (fun i => hN _) (fun i => hr _) k hk hq hrβ
    (restrictedPosition z) (active_position_cube hz) (restrictedReserve z)
    (active_positive z) (active_reserve_upper hz)
  · intro i
    exact hlarge (activeEquiv z i) (active_positive z i)
  · exact hreject

end HigherRankKSRuntime.RuntimeStateBounds
