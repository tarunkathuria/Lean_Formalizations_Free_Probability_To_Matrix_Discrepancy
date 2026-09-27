import MatrixSpencer.MSCountedPreparation
import MatrixSpencer.MSCountedMovement

/-! Primitive witnesses for the fixed scalar expressions used by the counted
response and ledger routines. Finite index tests select only rational constants;
all concrete divisions and square roots have certified operands. -/
open Matrix
noncomputable section
namespace MatrixSpencer.RealRAM.MSFixedScalarChecks
variable {k : ℕ}

def mixedExpr (i j a : Fin k) : Expr Unit :=
  .mul (.div (.constant 1) (.sqrt (.constant 2)))
    (.add (.constant (if a=i then 1 else 0)) (.constant (if a=j then 1 else 0)))

theorem mixed_execution (i j a : Fin k) :
    Expr.Executes (fun _=>0) (mixedExpr i j a) ((MSResponse.mixed i j).value a) 8 := by
  have hv : (mixedExpr i j a).Valid (fun _=>0) := by
    simp [mixedExpr,Expr.Valid,Expr.eval]
  have h:=Expr.executes_of_valid (fun _=>0) (mixedExpr i j a) hv
  have he : (mixedExpr i j a).eval (fun _=>0)=(MSResponse.mixed i j).value a := by
    dsimp only [mixedExpr,Expr.eval,MSResponse.mixed]
    split_ifs <;> simp_all
  rw [he] at h
  exact h

def polarizationExpr : Expr (Fin 3) :=
  .sub (.input 0) (.div (.add (.input 1) (.input 2)) (.constant 2))

theorem polarization_execution (a b c : ℝ) :
    Expr.Executes ![a,b,c] polarizationExpr (a-(b+c)/2) 7 := by
  have hv : polarizationExpr.Valid ![a,b,c] := by
    simp [polarizationExpr,Expr.Valid,Expr.eval]
  have h:=Expr.executes_of_valid _ _ hv
  simpa [polarizationExpr,Expr.eval,Expr.cost,Matrix.cons_val_two] using h

theorem negative_execution (G : JacobiIteration.Mat k) (ij : Fin k×Fin k) :
    Expr.Executes (JacobiIteration.entries G) (MSGammaTop.negativeExpr ij) (-G ij.1 ij.2) 3 := by
  have hv : (MSGammaTop.negativeExpr ij).Valid (JacobiIteration.entries G) := by
    simp [MSGammaTop.negativeExpr,Expr.Valid]
  simpa [MSGammaTop.negativeExpr,Expr.eval,Expr.cost,JacobiIteration.entries] using
    Expr.executes_of_valid _ _ hv

theorem top_tolerance_execution (t : ℝ) :
    Expr.Executes (fun _=>t) MSGammaTop.toleranceExpr (t/64) 3 := by
  have hv : MSGammaTop.toleranceExpr.Valid (fun _=>t) := by
    simp [MSGammaTop.toleranceExpr,Expr.Valid,Expr.eval]
  simpa [MSGammaTop.toleranceExpr,Expr.eval,Expr.cost] using Expr.executes_of_valid _ _ hv

theorem top_threshold_execution (t : ℝ) :
    Expr.Executes (fun _=>t) MSGammaTop.thresholdExpr (15*t/16) 5 := by
  have hv : MSGammaTop.thresholdExpr.Valid (fun _=>t) := by
    simp [MSGammaTop.thresholdExpr,Expr.Valid,Expr.eval]
  simpa [MSGammaTop.thresholdExpr,Expr.eval,Expr.cost] using Expr.executes_of_valid _ _ hv

end MatrixSpencer.RealRAM.MSFixedScalarChecks
