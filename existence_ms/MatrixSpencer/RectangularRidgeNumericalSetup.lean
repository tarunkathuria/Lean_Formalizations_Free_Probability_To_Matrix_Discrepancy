import MatrixSpencer.RectangularRidgeNumericalParameters
import MatrixSpencer.RealRAMCircuit

/-! Primitive real-RAM evaluation of all fixed polynomial numerical scales.
The size is calculated from the two input dimensions, and every load, constant,
multiplication and division is counted. These are numerical setup circuits;
the actual walk and its iteration-count proofs are separate obligations. -/

namespace MatrixSpencer.RectangularRidgeNumericalSetup
open RealRAM RectangularRidgeNumericalParameters
noncomputable section
set_option maxRecDepth 4096

def power {ι : Type*} (e : Expr ι) : ℕ → Expr ι
  | 0 => .constant 1
  | b+1 => .mul (power e b) e

theorem power_eval {ι : Type*} (e : Expr ι) (v : ι → ℝ) (b : ℕ) :
    (power e b).eval v = (e.eval v)^b := by
  induction b with
  | zero => simp [power, Expr.eval]
  | succ b ih => simp [power, Expr.eval, ih, pow_succ]

theorem power_cost {ι : Type*} (e : Expr ι) (b : ℕ) :
    (power e b).cost = 1+b*(e.cost+1) := by
  induction b with
  | zero => simp [power, Expr.cost]
  | succ b ih => simp [power, Expr.cost, ih]; ring

theorem power_valid {ι : Type*} (e : Expr ι) (v : ι → ℝ) (he : e.Valid v) (b : ℕ) :
    (power e b).Valid v := by
  induction b with
  | zero => trivial
  | succ b ih => exact ⟨ih, he⟩

def sizeExpr : Expr (Fin 2) := .add (.add (.input 0) (.input 1)) (.constant 2)
def bigExpr (a b : ℕ) : Expr (Fin 2) := .mul (.constant ((2:ℚ)^a)) (power sizeExpr b)
def smallExpr (a b : ℕ) : Expr (Fin 2) := .div (.constant 1) (bigExpr a b)

theorem sizeExpr_eval (v : Fin 2 → ℝ) : sizeExpr.eval v = v 0+v 1+2 := by
  simp [sizeExpr, Expr.eval]

theorem bigExpr_eval (a b : ℕ) (v : Fin 2 → ℝ) :
    (bigExpr a b).eval v = big (v 0+v 1+2) a b := by
  simp [bigExpr, Expr.eval, power_eval, sizeExpr_eval, big]

theorem smallExpr_eval (a b : ℕ) (v : Fin 2 → ℝ) :
    (smallExpr a b).eval v = small (v 0+v 1+2) a b := by
  simp [smallExpr, Expr.eval, bigExpr_eval, small]

theorem bigExpr_cost (a b : ℕ) : (bigExpr a b).cost = 6*b+3 := by
  simp only [bigExpr, Expr.cost, power_cost, sizeExpr]
  simp [Expr.cost]
  omega

theorem smallExpr_cost (a b : ℕ) : (smallExpr a b).cost = 6*b+5 := by
  simp only [smallExpr, Expr.cost, bigExpr_cost]
  omega

theorem bigExpr_valid (a b : ℕ) (v : Fin 2 → ℝ) : (bigExpr a b).Valid v :=
  ⟨trivial, power_valid sizeExpr v ⟨⟨trivial,trivial⟩,trivial⟩ b⟩

theorem smallExpr_valid (a b : ℕ) (v : Fin 2 → ℝ) (hv : 0<v 0+v 1+2) :
    (smallExpr a b).Valid v := by
  refine ⟨trivial, bigExpr_valid a b v, ?_⟩
  rw [bigExpr_eval]
  exact (big_pos hv a b).ne'

inductive Parameter where
  | density | fourth | covariance | paid | mesh | phase | epochs | prefix
  | ownerGrid | centerGrid | derivative | difference | value
  deriving DecidableEq, Fintype

def expression : Parameter → Expr (Fin 2)
  | .density => smallExpr 10 6
  | .fourth => bigExpr 1040 200
  | .covariance => bigExpr 300 60
  | .paid => smallExpr 320 62
  | .mesh => smallExpr 540 104
  | .phase => bigExpr 13 3
  | .epochs => bigExpr 22 4
  | .prefix => bigExpr 1120 213
  | .ownerGrid => smallExpr 1140 216
  | .centerGrid => smallExpr 1150 216
  | .derivative => smallExpr 20 2
  | .difference => smallExpr 322 62
  | .value => smallExpr 346 64

def specified (N : ℝ) : Parameter → ℝ
  | .density => densityFloor N
  | .fourth => fourthCap N
  | .covariance => covarianceCap N
  | .paid => paidStep N
  | .mesh => RectangularRidgeNumericalParameters.mesh N
  | .phase => phaseResponse N
  | .epochs => selectedEpochs N
  | .prefix => prefixUpdates N
  | .ownerGrid => RectangularRidgeNumericalParameters.ownerGrid N
  | .centerGrid => RectangularRidgeNumericalParameters.centerGrid N
  | .derivative => derivativeAccuracy N
  | .difference => differenceStep N
  | .value => valueAccuracy N

theorem expression_eval (p : Parameter) (v : Fin 2 → ℝ) :
    (expression p).eval v = specified (v 0+v 1+2) p := by
  cases p <;> simp only [expression, specified, bigExpr_eval, smallExpr_eval] <;> rfl

theorem expression_valid (p : Parameter) (v : Fin 2 → ℝ) (hv : 0<v 0+v 1+2) :
    (expression p).Valid v := by
  cases p with
  | density => exact smallExpr_valid 10 6 v hv
  | fourth => exact bigExpr_valid 1040 200 v
  | covariance => exact bigExpr_valid 300 60 v
  | paid => exact smallExpr_valid 320 62 v hv
  | mesh => exact smallExpr_valid 540 104 v hv
  | phase => exact bigExpr_valid 13 3 v
  | epochs => exact bigExpr_valid 22 4 v
  | «prefix» => exact bigExpr_valid 1120 213 v
  | ownerGrid => exact smallExpr_valid 1140 216 v hv
  | centerGrid => exact smallExpr_valid 1150 216 v hv
  | derivative => exact smallExpr_valid 20 2 v hv
  | difference => exact smallExpr_valid 322 62 v hv
  | value => exact smallExpr_valid 346 64 v hv

theorem expression_cost_le (p : Parameter) : (expression p).cost ≤ 1301 := by
  cases p <;> simp only [expression, bigExpr_cost, smallExpr_cost] <;> norm_num

/-- Evaluation is in the existing arithmetic execution relation, with the
specified numerical scale as its actual result. -/
theorem expression_executes (p : Parameter) (v : Fin 2 → ℝ) (hv : 0<v 0+v 1+2) :
    Expr.Executes v (expression p) (specified (v 0+v 1+2) p) (expression p).cost := by
  rw [← expression_eval]
  exact Expr.executes_of_valid v _ (expression_valid p v hv)

def circuit : Circuit (Fin 2) Parameter := ⟨expression⟩

theorem circuit_valid (v : Fin 2 → ℝ) (hv : 0<v 0+v 1+2) : circuit.Valid v :=
  fun p => expression_valid p v hv

theorem circuit_cost_le : circuit.cost ≤ 16926 := by
  unfold Circuit.cost
  calc
    _ ≤ ∑ _p : Parameter, 1302 := by
      apply Finset.sum_le_sum
      intro p _
      exact Nat.add_le_add_right (expression_cost_le p) 1
    _ = 16926 := by decide

end
end MatrixSpencer.RectangularRidgeNumericalSetup
