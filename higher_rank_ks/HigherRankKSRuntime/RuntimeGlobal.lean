import HigherRankKSRuntime.RuntimeNext
import HigherRankKSRuntime.GlobalInvariant

/-! The actual solver-driven controller is composed through all epochs.
`Context` collects already verified input preprocessing and scalar recipes;
the public input theorem constructs it from the matrix assumptions. -/
open Matrix MatrixSpencer Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace HigherRankKSRuntime.RuntimeGlobal
open AugmentedHigherRankKS RuntimeParameters GlobalEpochs
open MatrixSpencer.RealRAM.JacobiIteration (Counted)
variable {N d : ℕ}
local instance globalCStar : CStarAlgebra (SDPValue.Mat d) := {}
set_option maxHeartbeats 1000000

structure Context (N d : ℕ) where
  A : Fin N → SDPValue.Mat d
  factor : Fin N → SDPValue.Mat d
  factor_eq : factor = (InputFactors.factors A).value
  rank : ℕ
  p : Dimensions
  k : ℕ
  ε : ℝ
  dpos : 0 < d
  domain : p ∈ Domain
  N_eq : p.N=N
  D_eq : p.D=d
  kpos : 1 ≤ k
  dyadic : p.q=2^k
  psd : ∀ i,(A i).PosSemidef
  subisotropic : ∑ i,A i ≤ 1
  epsilon_nonneg : 0 ≤ ε
  epsilon_one : ε ≤ 1
  epsilon_lower : 1/p.N ≤ ε
  norm_bound : ∀ i,‖A i‖ ≤ ε
  rank_bound : ∀ i,(A i).rank ≤ rank
  rank_power : (rank:ℝ)^((1:ℝ)/2^k) ≤ 2

def fuel (p : Dimensions) : ℕ := ⌈eventBound p⌉₊+1

theorem fuel_sufficient (c : Context N d) :
    (N:ℝ)/walk c.p^2+(N:ℝ)*(a c.p*4)/prep c.p+N < fuel c.p := by
  have hh : eventBound c.p ≤ (⌈eventBound c.p⌉₊:ℝ) := Nat.le_ceil _
  dsimp [fuel,eventBound] at *
  rw [c.N_eq] at hh
  push_cast
  rw [c.N_eq]
  have hN := c.domain.1
  rw [c.N_eq] at hN
  simp only [mul_assoc] at *
  linarith

def next (c : Context N d) (O : SDPValue.Solver) (x : CubePoint (Fin N)) :=
  RuntimeNext.nextCached O c.A c.factor c.k c.p x.val

theorem next_eq (c : Context N d) (O : SDPValue.Solver) (x : CubePoint (Fin N)) :
    next c O x = RuntimeNext.next O c.A c.k c.p x.val :=
  RuntimeNext.nextCached_eq O c.A c.factor c.factor_eq c.k c.p x.val

theorem sound (c : Context N d) (O : SDPValue.Solver) (x : CubePoint (Fin N))
    {z : EpochState (Fin N)} (hz : z ∈ epochDomain (a c.p) 4)
    (hl : NextEvent.LargeOwners c.A (eta c.p) z) :
    (next c O x z).value.Valid (a c.p) 4 (prep c.p) (walk c.p) z := by
  rw [next_eq]
  exact (RuntimeNext.solver_good O c.dpos c.p c.domain c.N_eq c.D_eq.ge c.A c.psd
    c.subisotropic c.epsilon_nonneg c.epsilon_one c.norm_bound c.rank_bound c.k c.kpos
    c.dyadic c.rank_power x.val x.property hz hl).1

theorem safe (c : Context N d) (O : SDPValue.Solver) (x : CubePoint (Fin N))
    {z : EpochState (Fin N)} (hz : z ∈ epochDomain (a c.p) 4)
    (hl : NextEvent.LargeOwners c.A (eta c.p) z) :
    epochPotential c.A ((1:ℝ)/2^c.k) (theta c.p) x.val
      ((next c O x z).value.apply (a c.p) (prep c.p) (walk c.p) z) ≤
      epochPotential c.A ((1:ℝ)/2^c.k) (theta c.p) x.val z+
        ((next c O x z).value.cleanups:ℝ)*cleanupCharge c.p c.ε := by
  rw [next_eq]
  exact (RuntimeNext.solver_good O c.dpos c.p c.domain c.N_eq c.D_eq.ge c.A c.psd
    c.subisotropic c.epsilon_nonneg c.epsilon_one c.norm_bound c.rank_bound c.k c.kpos
    c.dyadic c.rank_power x.val x.property hz hl).2

theorem closed (c : Context N d) (O : SDPValue.Solver) (x : CubePoint (Fin N))
    {z : EpochState (Fin N)} (hz : z ∈ epochDomain (a c.p) 4)
    (hl : NextEvent.LargeOwners c.A (eta c.p) z) :
    NextEvent.LargeOwners c.A (eta c.p)
      ((next c O x z).value.apply (a c.p) (prep c.p) (walk c.p) z) := by
  rw [next_eq]
  exact RuntimeNext.next_largeOwners O c.A c.k c.p x.val hz hl

def epoch (c : Context N d) (O : SDPValue.Solver)
    (x : CubePoint (Fin N)) (hx : LargeCube c.A (eta c.p) x) : Counted (CubePoint (Fin N)) :=
  executedEpochOn (a c.p) (prep c.p) (walk c.p) (a_poly.positive c.p c.domain)
    (NextEvent.LargeOwners c.A (eta c.p)) (next c O x)
    (fun _ hz hl => sound c O x hz hl) (fun _ hz hl => closed c O x hz hl)
    (fuel c.p) x (largeCube_reset c.A (eta c.p) (a c.p) 4 x hx)

theorem epoch_frozen (c : Context N d) (O : SDPValue.Solver)
    (x : CubePoint (Fin N)) (hx : LargeCube c.A (eta c.p) x) :
    ∀ i,i ∉ cubeLive x → (epoch c O x hx).value.val i = x.val i := by
  apply executedEpochOn_frozen
  intro z hz
  exact NextEvent.compute_preservesFrozen _ (a c.p) (prep c.p) (walk c.p) (stencil c.p)
    (p0 c.p) (rho c.p) (zeta c.p) (theta_poly.positive c.p c.domain).le z

theorem epoch_closed (c : Context N d) (O : SDPValue.Solver)
    (x : CubePoint (Fin N)) (hx : LargeCube c.A (eta c.p) x) :
    LargeCube c.A (eta c.p) (epoch c O x hx).value :=
  largeCube_frozen c.A (eta c.p) hx (epoch_frozen c O x hx)

def eventBudget (c : Context N d) (O : SDPValue.Solver) : ℕ :=
  NextEvent.eventWork N (RuntimeNext.reportWork (d:=d) O N c.k c.p)

def epochBudget (c : Context N d) (O : SDPValue.Solver) : ℕ :=
  fuel c.p*eventBudget c O+10*N+1

theorem epoch_spec (c : Context N d) (O : SDPValue.Solver)
    (x : CubePoint (Fin N)) (hx : LargeCube c.A (eta c.p) x)
    (hl : (delta c.p c.ε)^2 < ‖cubeMass c.A x‖) :
    (∀ i,i ∉ cubeLive x → (epoch c O x hx).value.val i = x.val i) ∧
    ‖cubeMass c.A (epoch c O x hx).value‖ ≤ ‖cubeMass c.A x‖/2 ∧
    ‖cubeCenter c.A (epoch c O x hx).value-cubeCenter c.A x‖ ≤
      delta c.p c.ε*Real.sqrt ‖cubeMass c.A x‖ ∧
    (epoch c O x hx).cost ≤ epochBudget c O := by
  letI : NeZero d := ⟨c.dpos.ne'⟩
  have hβ : 0 < (1:ℝ)/2^c.k := by positivity
  have hβ1 : (1:ℝ)/2^c.k < 1 := by
    have hh : (2:ℝ) ≤ 2^c.k := by
      simpa using pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) c.kpos
    exact (div_lt_one (by positivity)).2 (by linarith)
  have hδ : 0 ≤ delta c.p c.ε := by unfold delta; positivity
  have hinit := initial_numeric_budget c.A c.psd x c.p c.domain c.N_eq.symm c.D_eq.symm
    c.epsilon_nonneg c.epsilon_one c.epsilon_lower c.norm_bound c.rank_bound
    hβ hβ1 c.rank_power hl
  have hs := executedEpochOn_spec c.A c.psd (a c.p) (prep c.p) (walk c.p)
    (a_poly.positive c.p c.domain) (prep_poly.positive c.p c.domain)
    (walk_poly.positive c.p c.domain).ne'
    (NextEvent.LargeOwners c.A (eta c.p)) (next c O x)
    (fun _ hz hi => sound c O x hz hi) (fun _ hz hi => closed c O x hz hi)
    (fuel c.p) (by simpa using fuel_sufficient c) x
    (largeCube_reset c.A (eta c.p) (a c.p) 4 x hx)
    hβ.le hβ1.le (theta_poly.positive c.p c.domain).le hδ
    (cleanupCharge_nonneg c.p c.domain c.epsilon_nonneg) hl
    (fun _ hz hi => safe c O x hz hi) (by simpa using hinit)
    (epoch_frozen c O x hx)
    (Q:=eventBudget c O) (fun z _ _ => by
      rw [next_eq]
      exact RuntimeNext.next_cost O c.A c.k c.p c.domain x.val z)
  simpa only [Fintype.card_fin] using hs

def execute (c : Context N d) (O : SDPValue.Solver) (testWork roundWork : ℕ) :
    Counted (CubePoint (Fin N)) :=
  runOn c.A (delta c.p c.ε) (LargeCube c.A (eta c.p)) (epoch c O)
    (epoch_closed c O) testWork roundWork N
    (RuntimeInputNormalization.discardCube c.A (eta c.p))
    (largeCube_discard c.A c.psd (eta c.p))

theorem execute_spec (c : Context N d) (O : SDPValue.Solver) (testWork roundWork : ℕ) :
    cubeTerminal (execute c O testWork roundWork).value ∧
    ‖cubeCenter c.A (execute c O testWork roundWork).value‖ ≤
      3000*Real.sqrt (c.ε*c.p.q) ∧
    (execute c O testWork roundWork).cost ≤ N*(epochBudget c O+testWork)+roundWork := by
  letI : NeZero d := ⟨c.dpos.ne'⟩
  have hδ : 0 ≤ delta c.p c.ε := by unfold delta; positivity
  let x := RuntimeInputNormalization.discardCube c.A (eta c.p)
  have hs := runOn_spec c.A c.psd hδ (LargeCube c.A (eta c.p)) (epoch c O)
    (epoch_closed c O) testWork roundWork (epochBudget c O) (epoch_spec c O)
    N x (largeCube_discard c.A c.psd (eta c.p))
    (show (cubeLive x).card≤N by simpa using Finset.card_le_card (Finset.subset_univ (cubeLive x)))
  have hm : ‖cubeMass c.A x‖ ≤ 1 := by
    have hh := (RuntimeInputNormalization.discard_mass_le c.A c.psd (eta c.p)).trans c.subisotropic
    simpa only [norm_one] using CStarAlgebra.norm_le_norm_of_nonneg_of_le
      (cubeMass_nonneg c.A c.psd x) hh
  have hms : Real.sqrt ‖cubeMass c.A x‖ ≤ 1 := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hm
  have hcenter := RuntimeInputNormalization.discard_center_bound c.A
    (fun i => (c.psd i).isHermitian) (theta_poly.positive c.p c.domain).le
  have htri : ‖cubeCenter c.A (execute c O testWork roundWork).value‖ ≤
      ‖cubeCenter c.A (execute c O testWork roundWork).value-cubeCenter c.A x‖+
        ‖cubeCenter c.A x‖ := by
    simpa only [sub_add_cancel] using norm_add_le
      (cubeCenter c.A (execute c O testWork roundWork).value-cubeCenter c.A x)
      (cubeCenter c.A x)
  have hbound := htri.trans (add_le_add hs.2.1 hcenter)
  have he : 4*delta c.p c.ε*Real.sqrt ‖cubeMass c.A x‖ ≤ 4*delta c.p c.ε := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hms (show 0 ≤ 4*delta c.p c.ε by positivity)
  refine ⟨hs.1,?_,hs.2.2⟩
  have hn := final_rank_bound c.p c.domain c.epsilon_nonneg c.epsilon_one c.epsilon_lower
  rw [c.N_eq] at hn
  exact hbound.trans (by linarith)

end HigherRankKSRuntime.RuntimeGlobal
