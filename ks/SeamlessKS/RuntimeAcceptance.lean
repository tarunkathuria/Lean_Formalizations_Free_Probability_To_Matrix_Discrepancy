import SeamlessKS.RuntimeDirection
import SeamlessKS.Run
import MatrixSpencer.RealRAMKSFullStateData

/-! The actual completion and norm test, with all matrix formation,
exact-EVD calls, scalar comparisons, and output copying counted. -/
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace SeamlessKS.RuntimeAcceptance
open MatrixSpencer MatrixSpencer.RealRAM
open MatrixSpencer.RealRAM.JacobiIteration (Counted)
open SeamlessKS.Walk
attribute [local instance] Classical.propDecidable
variable {N d : ℕ}

def signTest (x : Fin N → ℝ) : Counted Bool :=
  let q := KSNormReport.signScan x (List.finRange N)
  ⟨q.value,q.cost+3*N+1⟩

theorem signTest_value (s : WalkState N) :
    (signTest s.coeff).value=decide (Walk.terminal s) := by
  apply Bool.eq_iff_iff.mpr
  simp only [signTest,KSNormReport.signScan_value,List.all_eq_true,
    Bool.or_eq_true,decide_eq_true_eq]
  rw [Walk.terminal,State.terminal_iff_signing]
  simp [IsSign]

theorem signTest_cost (x : Fin N → ℝ) : (signTest x).cost=12*N+2 := by
  simp [signTest,KSNormReport.signScan_cost]
  omega

def thresholdExpr : Expr Unit := .mul (.constant 399) (.input ())

theorem threshold_primitive (δ : ℝ) :
    Expr.Executes (fun _ : Unit => δ) thresholdExpr (399*δ) 3 := by
  exact Expr.executes_of_valid (fun _ : Unit => δ) thresholdExpr ⟨trivial,trivial⟩

def accepts (v : Fin N → Fin d → ℂ) (s : WalkState N) : Counted Bool :=
  let st := signTest s.coeff
  let H := KSFullStateData.signedCenter v s.coeff
  let q := RuntimeDirection.norm H.value
  ⟨st.value && decide (q.value≤thresholdExpr.eval (fun _ => Input.delta v)),
    st.cost+H.cost+q.cost+thresholdExpr.cost+4⟩

theorem accepts_value [Nonempty (Fin d)] (v : Fin N → Fin d → ℂ) (hd : 0<d)
    (hp : ∑ i,KSRankOne.atom (v i)=1) (s : WalkState N) :
    (accepts v s).value=Run.accepts v s := by
  have hH : (KSFullStateData.signedCenter v s.coeff).value=StatePotential.signedSum v s.coeff :=
    KSFullStateData.signedCenter_value v s.coeff
  simp only [accepts,signTest_value,hH,RuntimeDirection.actual_norm_value v hd hp s,
    thresholdExpr,Expr.eval]
  simp only [Run.accepts,TrialProbability.accepts,Bool.decide_and]
  norm_num

def costBound (N d : ℕ) : ℕ :=
  12*N+9+100*(N+1)*(d+1)^2+700*(d+d+1)^3

theorem accepts_cost (v : Fin N → Fin d → ℂ) (s : WalkState N) :
    (accepts v s).cost≤costBound N d := by
  have hH := KSFullStateData.signedCenter_cost v s.coeff
  have hq := RuntimeDirection.norm_cost (KSFullStateData.signedCenter v s.coeff).value

  dsimp only [accepts]
  rw [signTest_cost]
  norm_num only [thresholdExpr,Expr.cost]
  dsimp only [costBound]
  omega

def copyCircuit (N : ℕ) : Circuit (Fin N) (Fin N) where
  output i := .input i

def copy (s : WalkState N) : Counted (Fin N → ℝ) :=
  ⟨(copyCircuit N).eval s.coeff,(copyCircuit N).cost+N+1⟩

theorem copy_value (s : WalkState N) : (copy s).value=s.coeff := rfl

theorem copy_cost (s : WalkState N) : (copy s).cost=3*N+1 := by
  simp [copy,copyCircuit,Circuit.cost,Expr.cost]
  omega

end SeamlessKS.RuntimeAcceptance
