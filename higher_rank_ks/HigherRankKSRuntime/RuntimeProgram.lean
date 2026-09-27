import HigherRankKSRuntime.RuntimeInputContext
import HigherRankKSRuntime.RuntimeGlobalArithmetic
import HigherRankKSRuntime.RuntimeGlobalWork

/-! The counted program uses the actual mass/EVD stopping tests, scalar
rounding, cached SDP factors, and all verified preprocessing stages. -/
open Matrix MatrixSpencer Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace HigherRankKSRuntime.RuntimeProgram
open AugmentedHigherRankKS RuntimeParameters GlobalEpochs RuntimeGlobal
open MatrixSpencer.RealRAM.JacobiIteration (Counted)
variable {N d r : ℕ}
set_option maxHeartbeats 800000

def core (c : Context N d) (O : SDPValue.Solver) : Counted (CubePoint (Fin N)) :=
  runArithmeticOn c.A (delta c.p c.ε) (LargeCube c.A (eta c.p))
    (epoch c O) (epoch_closed c O) N
    (RuntimeInputNormalization.discardCube c.A (eta c.p))
    (largeCube_discard c.A c.psd (eta c.p))

theorem core_value (c : Context N d) (O : SDPValue.Solver) :
    (core c O).value=(RuntimeGlobal.execute c O (massWork N d) (roundingWork N)).value :=
  runArithmeticOn_value c.A (fun i => (c.psd i).isHermitian) _ _ _ _ _ _ _ _ _

theorem core_cost (c : Context N d) (O : SDPValue.Solver) :
    (core c O).cost≤(RuntimeGlobal.execute c O (massWork N d) (roundingWork N)).cost := by
  apply runArithmeticOn_cost_le_semantic c.A (fun i => (c.psd i).isHermitian)
  · intro x
    have hh := RuntimeCubeArithmetic.massNorm_cost c.A x
    unfold massWork
    omega
  · intro x
    exact RuntimeCubeArithmetic.round_cost x

def charged (c : Context N d) (O : SDPValue.Solver) (r : ℕ) : Counted (Fin N → ℝ) :=
  let out := core c O
  ⟨out.value.val,out.cost+
    (InputFactors.factors c.A).cost+(RuntimeInputNormalization.epsilon c.A).cost+
    (RuntimeInputNormalization.discard c.A (eta c.p)).cost+
    (RuntimeParameterSetup.setup N d r).cost+RuntimeScalarRecipe.parameterWork+
    (RuntimeFuel.compute RuntimeFuel.defaultCap N d c.p).cost⟩

theorem charged_cost (c : Context N d) (O : SDPValue.Solver) (r : ℕ) :
    (charged c O r).cost ≤ RuntimeGlobalWork.fullCost c O r (massWork N d) (roundingWork N) := by
  have hh := core_cost c O
  dsimp only [charged,RuntimeGlobalWork.fullCost]
  omega

/-- Bind the EVD factors once, before any value query, and place that
cache in the context passed to every local and global epoch. -/
def positive (O : SDPValue.Solver) (A : Fin N → SDPValue.Mat d)
    (hN : 0<N) (hd : 0<d) (hr : 1≤r) (hA : ∀ i,(A i).PosSemidef)
    (hs : ∑ i,A i=1) (hrank : ∀ i,(A i).rank≤r) : Counted (Fin N → ℝ) :=
  let cache := InputFactors.factors A
  let c := RuntimeInputContext.makeWithFactors A cache.value rfl hN hd hr hA hs hrank
  charged c O r

theorem positive_eq (O : SDPValue.Solver) (A : Fin N → SDPValue.Mat d)
    (hN : 0<N) (hd : 0<d) (hr : 1≤r) (hA : ∀ i,(A i).PosSemidef)
    (hs : ∑ i,A i=1) (hrank : ∀ i,(A i).rank≤r) :
    positive O A hN hd hr hA hs hrank =
      charged (RuntimeInputContext.make A hN hd hr hA hs hrank) O r := rfl

theorem positive_correct (O : SDPValue.Solver) (A : Fin N → SDPValue.Mat d)
    (hN : 0<N) (hd : 0<d) (hr : 1≤r) (hA : ∀ i,(A i).PosSemidef)
    (hs : ∑ i,A i=1) (hrank : ∀ i,(A i).rank≤r)
    {ε : ℝ} (hε : 0≤ε) (hb : ∀ i,‖A i‖≤ε) :
    let out := positive O A hN hd hr hA hs hrank
    (∀ i,out.value i=1 ∨ out.value i= -1) ∧
    ‖∑ i,out.value i • A i‖ ≤ min 1 (10000*Real.sqrt (ε*Real.log (2*(r:ℝ)))) := by
  rw [positive_eq]
  simp only [charged,core_value]
  exact RuntimeInputContext.execute_discrepancy O A hN hd hr hA hs hrank hε hb
    (massWork N d) (roundingWork N)

theorem positive_polynomial (O : SDPValue.Solver) :
    ∃ C : ℝ, ∃ e : ℕ, 0<C ∧ ∀ (N d r : ℕ) (A : Fin N → SDPValue.Mat d)
      (hN : 0<N) (hd : 0<d) (hr : 1≤r) (hA : ∀ i,(A i).PosSemidef)
      (hs : ∑ i,A i=1) (hrank : ∀ i,(A i).rank≤r),
      ((positive O A hN hd hr hA hs hrank).cost:ℝ) ≤ C*(1+N+d)^e := by
  obtain ⟨C,e,hC,hb⟩ := RuntimeGlobalWork.uniform_polynomial O
  refine ⟨C,e,hC,fun N d r A hN hd hr hA hs hrank => ?_⟩
  let c := RuntimeInputContext.make A hN hd hr hA hs hrank
  have hc : ((charged c O r).cost:ℝ) ≤
      RuntimeGlobalWork.fullCost c O r (massWork N d) (roundingWork N) := by
    exact_mod_cast charged_cost c O r
  have hp := hb c r (massWork N d) (roundingWork N) hr
    (RuntimeInputContext.make_k_bound A hN hd hr hA hs hrank)
    (RuntimeInputContext.make_rank_dimension A hN hd hr hA hs hrank)
    (RuntimeGlobalWork.test_budget_le N d c.k) (RuntimeGlobalWork.round_budget_le N d c.k)
  rw [positive_eq]
  exact hc.trans hp

end HigherRankKSRuntime.RuntimeProgram
