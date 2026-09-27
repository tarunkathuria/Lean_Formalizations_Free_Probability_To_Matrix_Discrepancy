import HigherRankKSRuntime.RuntimeGlobal
import HigherRankKSRuntime.RuntimeFuel
import HigherRankKSRuntime.RuntimeParameterSetup
import HigherRankKSRuntime.RuntimeScalarRecipe

/-! The global solver-driven execution and every input/parameter stage have
one uniform polynomial work bound in the original input dimensions. -/
noncomputable section
namespace HigherRankKSRuntime.RuntimeGlobalWork
open AugmentedHigherRankKS.RuntimeParameters RuntimeWork
variable {N d : ℕ}

theorem setup_budget_le (N d k : ℕ) : 20*d+18≤scalarWork N d k := by
  have hb : 1≤N+d+k+1 := by omega
  have hd : d+1≤N+d+k+1 := by omega
  have hp : N+d+k+1≤(N+d+k+1)^6 := Nat.le_self_pow (by omega) _
  unfold scalarWork
  omega

theorem test_budget_le (N d k : ℕ) :
    5600*(d+1)^3+100*(N+1)*(d+1)^2+4≤scalarWork N d k := by
  let b := N+d+k+1
  have hb : 1≤b := by dsimp [b]; omega
  have hd : d+1≤b := by dsimp [b]; omega
  have hN : N+1≤b := by dsimp [b]; omega
  have hD3 : (d+1)^3≤b^3 := Nat.pow_le_pow_left hd 3
  have hp : (N+1)*(d+1)^2≤b^3 := by
    calc _ ≤ b*b^2 := by gcongr
         _ = _ := by ring
  have h36 : b^3≤b^6 := Nat.pow_le_pow_right hb (by omega)
  have h1 : 1≤b^6 := Nat.one_le_pow 6 b hb
  unfold scalarWork
  change _≤100000*b^6
  nlinarith

theorem round_budget_le (N d k : ℕ) : 13*N+1≤scalarWork N d k := by
  have hb : 1≤N+d+k+1 := by omega
  have hN : N+1≤N+d+k+1 := by omega
  have hp : N+d+k+1≤(N+d+k+1)^6 := Nat.le_self_pow (by omega) _
  unfold scalarWork
  omega

/-- The list of charged stages uses cached factors for every value report. -/
def fullCost (c : RuntimeGlobal.Context N d) (O : SDPValue.Solver)
    (r testWork roundWork : ℕ) : ℕ :=
  (RuntimeGlobal.execute c O testWork roundWork).cost+
  (InputFactors.factors c.A).cost+(RuntimeInputNormalization.epsilon c.A).cost+
  (RuntimeInputNormalization.discard c.A (eta c.p)).cost+
  (RuntimeParameterSetup.setup N d r).cost+RuntimeScalarRecipe.parameterWork+
  (RuntimeFuel.compute RuntimeFuel.defaultCap N d c.p).cost

/-- Actual execution costs fit the explicit controller budget, plus the
counted fuel program and the fixed scalar recipe. -/
theorem fullCost_le (c : RuntimeGlobal.Context N d) (O : SDPValue.Solver)
    {r testWork roundWork : ℕ} (hr : 1≤r)
    (htest : testWork≤scalarWork N d c.k) (hround : roundWork≤scalarWork N d c.k) :
    fullCost c O r testWork roundWork ≤
      RuntimeWork.totalWork O N d c.k c.p+
      (RuntimeFuel.compute RuntimeFuel.defaultCap N d c.p).cost+
      RuntimeScalarRecipe.parameterWork := by
  have hN : 1≤N := by exact_mod_cast (show (1:ℝ)≤N by simpa only [c.N_eq] using c.domain.1)
  have hd : 1≤d := c.dpos
  have hrun := (RuntimeGlobal.execute_spec c O testWork roundWork).2.2
  have hpre := RuntimeWork.preprocessing_cost c.A (eta c.p) c.k
  have hsetup := (RuntimeParameterSetup.setup_spec hN hd hr).2.2.2.2.2.2.2.2.2
  have hs := setup_budget_le N d c.k
  have hreset := reset_cost_le N d c.k
  have hsp : scalarWork N d c.k≤N*scalarWork N d c.k := by
    simpa using Nat.mul_le_mul_right (scalarWork N d c.k) hN
  change (RuntimeGlobal.execute c O testWork roundWork).cost ≤
    N*(RuntimeWork.fuel c.p*NextEvent.eventWork N (reportBudget O N d c.k c.p)+10*N+1+testWork)+roundWork at hrun
  unfold fullCost RuntimeWork.totalWork
  nlinarith

/-- Only the permitted solver influences the fixed coefficient and degree.
No numerical conditioning or iteration hypothesis occurs in this bound. -/
theorem uniform_polynomial (O : SDPValue.Solver) :
    ∃ C : ℝ, ∃ e : ℕ, 0<C ∧ ∀ {N d : ℕ} (c : RuntimeGlobal.Context N d)
      (r testWork roundWork : ℕ), 1≤r → (c.k:ℝ)≤c.p.q → c.p.q≤4*c.p.D →
      testWork≤scalarWork N d c.k → roundWork≤scalarWork N d c.k →
      (fullCost c O r testWork roundWork:ℝ)≤C*(1+N+d)^e := by
  obtain ⟨C,e,hC,hb⟩ := RuntimeFuel.total_with_fuel_polynomial O RuntimeFuel.defaultCap
  refine ⟨C+RuntimeScalarRecipe.parameterWork+1,e,by positivity,?_⟩
  intro N d c r testWork roundWork hr hk hq htest hround
  have hh := hb N d c.k c.p c.domain c.N_eq.symm c.D_eq.symm hk hq
  have hfull : (fullCost c O r testWork roundWork:ℝ) ≤
      ((RuntimeWork.totalWork O N d c.k c.p+
      (RuntimeFuel.compute RuntimeFuel.defaultCap N d c.p).cost):ℝ)+RuntimeScalarRecipe.parameterWork := by
    exact_mod_cast fullCost_le c O hr htest hround
  have hbase : (1:ℝ)≤1+N+d := by
    linarith [Nat.cast_nonneg (α:=ℝ) N,Nat.cast_nonneg (α:=ℝ) d]
  have hp := one_le_pow₀ hbase (n:=e)
  have hparam := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg (α:=ℝ) RuntimeScalarRecipe.parameterWork)
  nlinarith

end HigherRankKSRuntime.RuntimeGlobalWork
