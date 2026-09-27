import MatrixSpencer.KSEighthConvexController
import MatrixSpencer.KSRetirementRuntime
import MatrixSpencer.RealRAMKSCappedSimplex

/-!
# Counted query interface and exact eighth-cube preparation

This is an intermediate composition layer. The query record must be populated
by a counted implementation of the direct owner SDP, including its construction
and solver calls. Its value fields are required to equal the specified solver
reports; no accuracy or probability hypothesis is added here. Costs are kept
separate and will be instantiated by the input compiler.

Snapping is an explicit safe scalar program, and preparation then runs the
already counted endpoint scan with exactly the original fuel and scan order.
-/
open Set
open scoped BigOperators
noncomputable section
namespace MatrixSpencer.KSEighthCountedPreparation
open RealRAM RealRAM.JacobiIteration
variable {N d : ℕ}
attribute [local instance] Classical.propDecidable

structure Queries (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ)
    (θ : ℝ) (hd : 0<d) where
  state : ℝ → (Fin N → ℝ) → Counted ℝ
  state_value : ∀ν x,(state ν x).value=KSEighthConvexValue.stateReport O v θ hd ν x
  retained : Finset (Fin N) → ℝ → (Fin N → ℝ) → Counted ℝ
  retained_value : ∀L ν x,(retained L ν x).value=KSEighthConvexValue.retainedReport O v θ hd L ν x

inductive Reg where
  | radius | margin | coordinate | absolute | result
  deriving DecidableEq, Fintype

def snapProgram : Program Reg :=
  .seq
    (.branchLE (.constant 0) (.input .coordinate)
      (.assign .absolute (.input .coordinate))
      (.assign .absolute (.sub (.constant 0) (.input .coordinate))))
    (.branchLE (.sub (.input .radius) (.input .absolute)) (.input .margin)
      (.branchLE (.constant 0) (.input .coordinate)
        (.assign .result (.input .radius))
        (.assign .result (.sub (.constant 0) (.input .radius))))
      (.assign .result (.input .coordinate)))

def input (a ρ t : ℝ) : Reg → ℝ
  | .radius => a
  | .margin => ρ
  | .coordinate => t
  | _ => 0

theorem snapProgram_safe (v : Reg → ℝ) : snapProgram.Safe v := by
  simp [snapProgram, Program.Safe, Expr.Valid]

theorem snapProgram_bound : snapProgram.bound≤30 := by
  norm_num [snapProgram, Program.bound, Expr.cost]

theorem snapProgram_value (a ρ t : ℝ) :
    snapProgram.run (input a ρ t) .result=
      if a-|t|≤ρ then KSCubePreparation.endpoint a t else t := by
  by_cases ht : 0≤t
  · simp [snapProgram, Program.run, Expr.eval, input, ht, abs_of_nonneg ht,
      KSCubePreparation.endpoint]
    split_ifs <;> simp
  · simp [snapProgram, Program.run, Expr.eval, input, ht, abs_of_neg (lt_of_not_ge ht),
      KSCubePreparation.endpoint]
    split_ifs <;> simp

def snap (a ρ : ℝ) (x : Fin N → ℝ) : Counted (Fin N → ℝ) :=
  ⟨fun i => snapProgram.run (input a ρ (x i)) .result,
    (∑i,(snapProgram.cost (input a ρ (x i))+8))+1⟩

theorem snap_value (a ρ : ℝ) (x : Fin N → ℝ) :
    (snap a ρ x).value=KSCubePreparation.snap a ρ x := by
  funext i
  exact snapProgram_value a ρ (x i)

theorem snap_cost (a ρ : ℝ) (x : Fin N → ℝ) : (snap a ρ x).cost≤38*N+1 := by
  have hs : (∑i,(snapProgram.cost (input a ρ (x i))+8))≤38*N := by
    calc
      _ ≤ ∑_i : Fin N,38 := by
        apply Finset.sum_le_sum
        intro i _
        have h := (snapProgram.cost_le_bound (input a ρ (x i))).trans snapProgram_bound
        omega
      _ = _ := by simp; omega
  dsimp only [snap]
  omega

theorem snap_coordinate_execution (a ρ : ℝ) (x : Fin N → ℝ) (i : Fin N) :
    ∃k≤30,Program.Executes snapProgram (input a ρ (x i))
      (snapProgram.run (input a ρ (x i))) k ∧
      snapProgram.run (input a ρ (x i)) .result=(snap a ρ x).value i := by
  obtain ⟨k,hk,he⟩ := Program.safe_execution_bounded snapProgram
    (input a ρ (x i)) (snapProgram_safe _)
  exact ⟨k,hk.trans snapProgram_bound,he,rfl⟩

def prepare (a ρ τ : ℝ) (report : KSRetirementRuntime.Report N)
    (x : Fin N → ℝ) : Counted (Fin N → ℝ) :=
  let s := snap a ρ x
  let p := KSRetirementRuntime.prepare a τ report N s.value
  ⟨p.value,s.cost+p.cost+2⟩

theorem prepare_value (a ρ τ : ℝ) (report : KSRetirementRuntime.Report N)
    (x : Fin N → ℝ) :
    (prepare a ρ τ report x).value=
      KSEighthPreparedState.prepareState a τ ρ (fun y => (report y).value) x := by
  simp only [prepare,KSRetirementRuntime.prepare_value,snap_value,
    KSEighthPreparedState.prepareState]

theorem prepare_cost {a ρ τ : ℝ} (ha : 0≤a) (report : KSRetirementRuntime.Report N)
    {Q : ℕ} (hQ : ∀x∈ksCube a,(report x).cost≤Q)
    {x : Fin N → ℝ} (hx : x∈ksCube a) :
    (prepare a ρ τ report x).cost≤50*(N+1)^3*(Q+20) := by
  have hs := snap_cost a ρ x
  have hp := KSRetirementRuntime.preparation_cost (τ:=τ) ha report hQ
    (KSCubePreparation.snap_mem_cube (ρ:=ρ) ha hx)
  rw [←snap_value a ρ x] at hp
  dsimp only [prepare]
  have hN : N≤(N+1)^3 := by nlinarith [Nat.zero_le (N^2),Nat.zero_le (N^3)]
  have h1 : 1≤(N+1)^3 := Nat.one_le_pow 3 _ (by omega)
  nlinarith

def statePreparation (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ)
    (θ : ℝ) (hd : 0<d) (q : Queries O v θ hd) (ρ : ℝ) (x : Fin N → ℝ) :=
  prepare (1/8) ρ ρ (q.state (ρ/8)) x

theorem statePreparation_value (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ)
    (θ : ℝ) (hd : 0<d) (q : Queries O v θ hd) (ρ : ℝ) (x : Fin N → ℝ) :
    (statePreparation O v θ hd q ρ x).value=
      KSEighthPreparedState.prepareState (1/8) ρ ρ
        (KSEighthConvexValue.stateReport O v θ hd (ρ/8)) x := by
  simp only [statePreparation,prepare_value,q.state_value]

end MatrixSpencer.KSEighthCountedPreparation
