import MatrixSpencer.RectangularRidgeWeightWork
import MatrixSpencer.RectangularRidgeNumericalSetup
import MatrixSpencer.RealRAMJacobiIteration

/-! The actual comparison scan and scalar expressions used by a covariance
response query. Values and work are proved from the two input dimensions. -/
noncomputable section
namespace MatrixSpencer.RectangularRidgeResponseScalars
open RealRAM
open RealRAM.JacobiIteration (Counted)
open RectangularRidgeTuning RectangularRidgeNumericalParameters

structure Values where
  depth : ℕ
  weight : ℝ
  spacing : ℝ
  accuracy : ℝ

def selected (N d : ℕ) : State := (scan N d (d+1) initial).getD initial

theorem selected_level {N d : ℕ} (hN : 1≤N) : (selected N d).level=depth N d hN := by
  obtain ⟨t,ht,hw,hl⟩:=scan_initial_success (D:=d) hN
  simpa [selected,ht] using hl

theorem selected_power {N d : ℕ} (hN : 1≤N) : (selected N d).power=order N d hN := by
  obtain ⟨t,ht,hw,hl⟩:=scan_initial_success (D:=d) hN
  simp only [selected,ht,Option.getD_some]
  rw [hw.2.1,hl]
  rfl

def input (N d : ℕ) : Fin 2→ℝ := ![d,N]

def compute (N d : ℕ) : Counted Values :=
  let t:=selected N d
  let theta:=RectangularRidgeWeightWork.expression t.level
  let spacing:=RectangularRidgeNumericalSetup.smallExpr 322 62
  let accuracy:=RectangularRidgeNumericalSetup.smallExpr 346 64
  ⟨⟨t.level,theta.eval ![N,d,t.power],spacing.eval (input N d),accuracy.eval (input N d)⟩,
    scanCost N d (d+1) initial+theta.cost+spacing.cost+accuracy.cost+20⟩

theorem compute_value {N d : ℕ} (hN : 1≤N) (hNd : N≤d) :
    (compute N d).value=⟨depth N d hN,RectangularRidgePrimitiveParameters.weight N d hN,
      differenceStep (RectangularRidgeNumericalOptimizerFloor.size d N),
      valueAccuracy (RectangularRidgeNumericalOptimizerFloor.size d N)⟩ := by
  simp only [compute,selected_level hN,selected_power hN]
  rw [show (![↑N,↑d,↑(order N d hN)] : Fin 3→ℝ)=RectangularRidgeWeightWork.registers N d hN from rfl,
    RectangularRidgeWeightWork.expression_eval hN hNd]
  simp only [RectangularRidgeNumericalSetup.smallExpr_eval,input,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_fin_one]
  rfl

theorem compute_cost {N d : ℕ} (hN : 1≤N) : (compute N d).cost≤8*d+900 := by
  have hs:=scanCost_le N d (d+1) initial
  simp only [compute,RectangularRidgeWeightWork.expression_cost,
    RectangularRidgeNumericalSetup.smallExpr_cost,selected_level hN]
  have hm:=depth_le N d hN
  omega

end MatrixSpencer.RectangularRidgeResponseScalars
