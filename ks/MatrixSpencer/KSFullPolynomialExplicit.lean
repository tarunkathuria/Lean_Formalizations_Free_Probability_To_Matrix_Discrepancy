import MatrixSpencer.KSFullPolynomialAlgorithmRuntime
import MatrixSpencer.KSFullConvexOracleExplicit

/-! All-dimensional end-to-end specification for the full-cube KS walk with
the permitted polynomial convex solver. The same actual output has a counted
execution, full original-label signing correctness, and its stated success
probability. Dimension zero is handled before any scalar division. -/
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSFullPolynomialExplicit
open KSPolynomialConvexSolver
variable {N d : ℕ}

def zeroCircuit (N : ℕ) : RealRAM.Circuit Unit (Fin N) where
  output _ := .constant 1

def zeroOutput (N : ℕ) : RealRAM.JacobiIteration.Counted (Fin N → ℝ) :=
  ⟨(zeroCircuit N).eval (fun _ => 0),(zeroCircuit N).cost+N+1⟩

theorem zeroOutput_value (N : ℕ) : (zeroOutput N).value=fun _ => (1:ℝ) := by
  funext i
  norm_num [zeroOutput,zeroCircuit,RealRAM.Circuit.eval,RealRAM.Expr.eval]
theorem zeroOutput_cost (N : ℕ) : (zeroOutput N).cost=3*N+1 := by
  simp [zeroOutput,zeroCircuit,RealRAM.Circuit.cost,RealRAM.Expr.cost]
  omega

def totalCost (P : PolynomialSolver) (N d r : ℕ) : ℕ :=
  KSFullPolynomialAlgorithmRuntime.totalCost P N d r+3*N+10

def Executes (P : PolynomialSolver) : {d : ℕ} → (v : Fin N → Fin d → ℂ) →
    (hp : (∑i,KSRankOne.atom (v i))=1) → (r : ℕ) →
    KSFullConvexOracleExplicit.Draws P.solver v hp r → Option (Fin N → ℝ) → ℕ → ℕ → Prop
  | 0,_,_,_,_,result,cost,draws =>
      result=some (zeroOutput N).value ∧ cost=(zeroOutput N).cost+2 ∧ draws=0
  | d+1,v,hp,r,z,result,cost,draws =>
      letI : Nonempty (Fin (d+1)) := ⟨⟨0,Nat.succ_pos d⟩⟩
      ∃ k, KSFullPolynomialAlgorithmRuntime.Executes P v (Nat.succ_pos d) hp r z result k draws ∧
        cost=k+2

theorem execution_result (P : PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (hp : (∑i,KSRankOne.atom (v i))=1) (r : ℕ)
    (z : KSFullConvexOracleExplicit.Draws P.solver v hp r)
    (result : Option (Fin N → ℝ)) (cost draws : ℕ)
    (h : Executes P v hp r z result cost draws) :
    result=KSFullConvexOracleExplicit.output P.solver v hp r z := by
  cases d with
  | zero => simpa only [zeroOutput_value,KSFullConvexOracleExplicit.output] using h.1
  | succ d =>
    letI : Nonempty (Fin (d+1)) := ⟨⟨0,Nat.succ_pos d⟩⟩
    obtain ⟨k,he,hk⟩ := h
    exact KSFullPolynomialAlgorithmRuntime.execution_result P v (Nat.succ_pos d) hp r z result k draws he

theorem exists_execution_bounded (P : PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (hp : (∑i,KSRankOne.atom (v i))=1) (r : ℕ)
    (z : KSFullConvexOracleExplicit.Draws P.solver v hp r) :
    ∃ cost draws, Executes P v hp r z (KSFullConvexOracleExplicit.output P.solver v hp r z) cost draws ∧
      cost≤totalCost P N d r ∧ draws≤r*KSConvexQueryBudgets.fullHorizon N d := by
  cases d with
  | zero =>
    refine ⟨(zeroOutput N).cost+2,0,⟨?_,rfl,rfl⟩,?_,Nat.zero_le _⟩
    · simp only [KSFullConvexOracleExplicit.output,zeroOutput_value]
    · rw [zeroOutput_cost]
      unfold totalCost
      omega
  | succ d =>
    letI : Nonempty (Fin (d+1)) := ⟨⟨0,Nat.succ_pos d⟩⟩
    obtain ⟨cost,draws,he,hc,hr⟩ :=
      KSFullPolynomialAlgorithmRuntime.exists_execution_bounded P v (Nat.succ_pos d) hp r z
    refine ⟨cost+2,draws,⟨cost,he,rfl⟩,?_,hr⟩
    unfold totalCost
    omega

/-- No derivative, tolerance, iteration, or per-query budget is an input
premise. The only computational exception is the explicit polynomial solver
contract. Random draws are fair finite draws, counted separately. -/
theorem algorithm (P : PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (hp : (∑i,KSRankOne.atom (v i))=1) {ε : ℝ} (hε : 0≤ε)
    (hsize : ∀i,‖KSRankOne.atom (v i)‖≤ε) (r : ℕ) :
    (∀z : KSFullConvexOracleExplicit.Draws P.solver v hp r,
      ∃ cost draws, Executes P v hp r z (KSFullConvexOracleExplicit.output P.solver v hp r z) cost draws ∧
        cost≤totalCost P N d r ∧ draws≤r*KSConvexQueryBudgets.fullHorizon N d) ∧
    (∀z : KSFullConvexOracleExplicit.Draws P.solver v hp r, ∀σ : Fin N → ℝ,
      KSFullConvexOracleExplicit.output P.solver v hp r z=some σ →
        (∀i,IsSign (σ i)) ∧ ‖∑i,σ i • KSRankOne.atom (v i)‖≤9*(16*Real.sqrt 2+5)*Real.sqrt ε) ∧
    1-((15:ℝ)/56)^r≤∑z : KSFullConvexOracleExplicit.Draws P.solver v hp r,
      KSFullConvexOracleExplicit.drawWeight P.solver v hp r z*
        (if (KSFullConvexOracleExplicit.output P.solver v hp r z).isSome then 1 else 0) :=
  ⟨exists_execution_bounded P v hp r,
    fun z σ hout => KSFullConvexOracleExplicit.output_sound P.solver v hp hε hsize r z σ hout,
    KSFullConvexOracleExplicit.output_event_probability_ge P.solver v hp r⟩

end MatrixSpencer.KSFullPolynomialExplicit
