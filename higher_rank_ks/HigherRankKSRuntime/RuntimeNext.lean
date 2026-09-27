import HigherRankKSRuntime.RuntimeMove
import HigherRankKSRuntime.RuntimePreparationScan
import HigherRankKSRuntime.RuntimeInvariant
import HigherRankKSRuntime.RuntimeStateReport
import HigherRankKSRuntime.NextEventCost

/-! Source-specific correctness of the complete local controller. Numerical
value accuracy is the only computational condition in the intermediate
query version; the solver version below discharges it using the explicit
finite SDP and cached EVD factors. -/
noncomputable section
open Matrix MatrixSpencer Set
open scoped BigOperators Topology ContDiff MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace HigherRankKSRuntime.RuntimeNext
open AugmentedHigherRankKS ActiveEnumeration RuntimeParameters ControllerLoop
open MatrixSpencer.RealRAM.JacobiIteration (Counted)
variable {N : ℕ} {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
set_option maxHeartbeats 800000

theorem good (p : Dimensions) (hp : p ∈ Domain) (hNp : p.N=N)
    (hd : (Fintype.card n : ℝ) ≤ p.D)
    (A : Fin N → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef) (hsum : ∑ i, A i ≤ 1)
    {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hN : ∀ i, ‖A i‖ ≤ ε)
    {r : ℕ} (hrank : ∀ i, (A i).rank ≤ r) (k : ℕ) (hk : 1 ≤ k) (hq : p.q=2^k)
    (hrβ : (r:ℝ)^((1:ℝ)/2^k) ≤ 2)
    (x₀ : Fin N → ℝ) (hx₀ : ∀ i, |x₀ i| ≤ 1)
    (query : EpochState (Fin N) → Counted ℝ)
    (hquery : ∀ y, (∀ i, 0 ≤ reserve y i) →
      |(query y).value-epochPotential A ((1:ℝ)/2^k) (theta p) x₀ y| ≤ accuracy p)
    {z : EpochState (Fin N)} (hz : z ∈ epochDomain (a p) 4)
    (hlarge : NextEvent.LargeOwners A (eta p) z) :
    let e := (NextEvent.compute query (a p) (prep p) (walk p) (stencil p) (p0 p) (rho p) (zeta p) z).value
    e.Valid (a p) 4 (prep p) (walk p) z ∧
      epochPotential A ((1:ℝ)/2^k) (theta p) x₀ (e.apply (a p) (prep p) (walk p) z) ≤
        epochPotential A ((1:ℝ)/2^k) (theta p) x₀ z+
          (e.cleanups:ℝ)*(2*ε*(rho p+zeta p/a p)) := by
  let E := epochPotential A ((1:ℝ)/2^k) (theta p) x₀
  have ha := a_poly.positive p hp
  have hζ := theta_poly.positive p hp
  have hρ : 0 ≤ rho p := hζ.le
  have hβ : 0 ≤ (1:ℝ)/2^k := by positivity
  have hβ1 : (1:ℝ)/2^k ≤ 1 := (div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num))
  have hmoves (hclean : NextEvent.Clean z (rho p) (zeta p)) (hm : count z ≠ 0)
      (hreject : NextEvent.Rejected query (a p) (prep p) (p0 p) z) :=
    RuntimeMove.good p hp hNp hd A hA hsum hε hε1 hN hrank k hk hq hrβ x₀ hx₀ query
      hquery hz hm hclean hlarge
      (RuntimePreparationScan.rejected_derivatives p hp hd A hA hsum hε hε1 hN hrank
        k hk hrβ x₀ hx₀ query hquery hz hclean hreject)
  constructor
  · apply NextEvent.valid query ha (prep_poly.positive p hp).le
      ((prep_le_zeta p).trans (by change zeta p ≤ 2*zeta p; linarith)) hz
    intro hclean hm hreject
    exact (hmoves hclean hm hreject).1
  · apply NextEvent.potential_le query E z
    · intro e he
      cases e with
      | round i =>
        have hb := roundOwner_potential_cost A (fun j => (hA j).isHermitian) hβ hβ1
          (theta p) x₀ hz i (hN i) he.2
        have haux : 0 ≤ zeta p/a p := div_nonneg hζ.le ha.le
        change E (roundOwner z i) ≤ E z+2*ε*(rho p+zeta p/a p)
        dsimp only [E]
        nlinarith [mul_nonneg hε haux]
      | exhaust i =>
        have hb := exhaustOwner_potential_cost A (fun j => (hA j).isHermitian) hβ hβ1
          (theta p) x₀ hz ha i (hN i) he.2.le
        change E (exhaustOwner (a p) z i) ≤ E z+2*ε*(rho p+zeta p/a p)
        dsimp only [E]
        have heq : 2*zeta p*ε/a p = 2*ε*(zeta p/a p) := by ring
        rw [heq] at hb
        nlinarith [mul_nonneg hε hρ]
    · intro hclean i hi haccept
      exact PreparationAnalysis.accepted_state_descent p hp query E hz hclean hquery i hi haccept
    · intro hclean hm hreject
      exact (hmoves hclean hm hreject).2


/-- The factor array is a stored input to every report in this controller.
Its construction is charged once by the outer input program. -/
def nextCached {d : ℕ} (O : SDPValue.Solver) (A B : Fin N → SDPValue.Mat d)
    (k : ℕ) (p : Dimensions) (x₀ : Fin N → ℝ) :
    EpochState (Fin N) → Counted (Event (Fin N)) :=
  NextEvent.compute
    (RuntimeStateReport.report O A B k x₀ (theta p) (accuracy p))
    (a p) (prep p) (walk p) (stencil p) (p0 p) (rho p) (zeta p)

/-- Mathematical specialization used by the analytic local theorems. -/
def next {d : ℕ} (O : SDPValue.Solver) (A : Fin N → SDPValue.Mat d)
    (k : ℕ) (p : Dimensions) (x₀ : Fin N → ℝ) :
    EpochState (Fin N) → Counted (Event (Fin N)) :=
  nextCached O A (InputFactors.factors A).value k p x₀

theorem nextCached_eq {d : ℕ} (O : SDPValue.Solver) (A B : Fin N → SDPValue.Mat d)
    (hB : B=(InputFactors.factors A).value) (k : ℕ) (p : Dimensions)
    (x₀ : Fin N → ℝ) : nextCached O A B k p x₀ = next O A k p x₀ := by
  rw [hB]
  rfl

theorem solver_good {d : ℕ} (O : SDPValue.Solver) (hdpos : 0 < d)
    (p : Dimensions) (hp : p ∈ Domain) (hNp : p.N=N) (hd : (d:ℝ) ≤ p.D)
    (A : Fin N → SDPValue.Mat d) (hA : ∀ i, (A i).PosSemidef) (hsum : ∑ i, A i ≤ 1)
    {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hN : ∀ i, ‖A i‖ ≤ ε)
    {r : ℕ} (hrank : ∀ i, (A i).rank ≤ r) (k : ℕ) (hk : 1 ≤ k) (hq : p.q=2^k)
    (hrβ : (r:ℝ)^((1:ℝ)/2^k) ≤ 2)
    (x₀ : Fin N → ℝ) (hx₀ : ∀ i, |x₀ i| ≤ 1)
    {z : EpochState (Fin N)} (hz : z ∈ epochDomain (a p) 4)
    (hlarge : NextEvent.LargeOwners A (eta p) z) :
    (next O A k p x₀ z).value.Valid (a p) 4 (prep p) (walk p) z ∧
      epochPotential A ((1:ℝ)/2^k) (theta p) x₀
        ((next O A k p x₀ z).value.apply (a p) (prep p) (walk p) z) ≤
        epochPotential A ((1:ℝ)/2^k) (theta p) x₀ z+
          ((next O A k p x₀ z).value.cleanups:ℝ)*(2*ε*(rho p+zeta p/a p)) := by
  letI : Nonempty (Fin d) := ⟨⟨0,hdpos⟩⟩
  exact good p hp hNp (by simpa using hd) A hA hsum hε hε1 hN hrank k hk hq hrβ x₀ hx₀
    (RuntimeStateReport.report O A (InputFactors.factors A).value k x₀ (theta p) (accuracy p))
    (fun y hy => RuntimeStateReport.report_accuracy O A hA k x₀ hdpos hk
      (theta_poly.positive p hp) (accuracy_poly.positive p hp) y hy) hz hlarge

def reportWork {d : ℕ} (O : SDPValue.Solver) (N : ℕ) (k : ℕ) (p : Dimensions) : ℕ :=
  O.coefficient*(SDPValue.dataSize N d k+⌈(accuracy p)⁻¹⌉₊+1)^O.degree +1004*(N+1)*(d+1)^2

theorem next_cost {d : ℕ} (O : SDPValue.Solver) (A : Fin N → SDPValue.Mat d)
    (k : ℕ) (p : Dimensions) (hp : p ∈ Domain) (x₀ : Fin N → ℝ)
    (z : EpochState (Fin N)) :
    (next O A k p x₀ z).cost ≤ NextEvent.eventWork N (reportWork (d:=d) O N k p) := by
  apply NextEvent.compute_work
  intro y
  exact RuntimeStateReport.report_cost O A (InputFactors.factors A).value k x₀ (theta p)
    (accuracy_poly.positive p hp) y

theorem next_largeOwners {d : ℕ} (O : SDPValue.Solver) (A : Fin N → SDPValue.Mat d)
    (k : ℕ) (p : Dimensions) (x₀ : Fin N → ℝ) {z : EpochState (Fin N)}
    (hz : z ∈ epochDomain (a p) 4) (hl : NextEvent.LargeOwners A (eta p) z) :
    NextEvent.LargeOwners A (eta p)
      ((next O A k p x₀ z).value.apply (a p) (prep p) (walk p) z) :=
  NextEvent.compute_largeOwners A (eta p) _ (a p) 4 (prep p) (walk p) (stencil p)
    (p0 p) (rho p) (zeta p) hz hl

end HigherRankKSRuntime.RuntimeNext
