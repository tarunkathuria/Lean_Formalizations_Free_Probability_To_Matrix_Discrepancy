import SeamlessKS.Source
import MatrixSpencer.RealRAMCircuit

/-! Primitive arithmetic evaluation of the actual smooth covariance source.
There is no optimizer or transcendental oracle in these expressions. -/
noncomputable section
namespace SeamlessKS.SourceEvaluation
open MatrixSpencer.RealRAM

def relabel {ι κ : Type*} (f : ι → κ) : Expr ι → Expr κ
  | .input i => .input (f i)
  | .constant q => .constant q
  | .add a b => .add (relabel f a) (relabel f b)
  | .sub a b => .sub (relabel f a) (relabel f b)
  | .mul a b => .mul (relabel f a) (relabel f b)
  | .div a b => .div (relabel f a) (relabel f b)
  | .sqrt a => .sqrt (relabel f a)

@[simp] theorem relabel_eval {ι κ : Type*} (f : ι → κ) (v : κ → ℝ) (e : Expr ι) :
    (relabel f e).eval v=e.eval (v ∘ f) := by
  induction e <;> simp_all [relabel,Expr.eval,Function.comp_def]

@[simp] theorem relabel_cost {ι κ : Type*} (f : ι → κ) (e : Expr ι) :
    (relabel f e).cost=e.cost := by
  induction e <;> simp_all [relabel,Expr.cost]

@[simp] theorem relabel_valid {ι κ : Type*} (f : ι → κ) (v : κ → ℝ) (e : Expr ι) :
    (relabel f e).Valid v ↔ e.Valid (v ∘ f) := by
  induction e <;> simp_all [relabel,Expr.Valid]

def registers (x ζ : ℝ) : Fin 2 → ℝ := ![x,ζ]

def weightExpr : Expr (Fin 2) :=
  .mul (.constant 64)
    (.sub (.add (.sub (.constant 1) (.mul (.input 0) (.input 0)))
      (.sqrt (.add (.constant 1) (.mul (.input 1) (.input 1)))))
      (.sqrt (.add (.mul (.input 0) (.input 0)) (.mul (.input 1) (.input 1)))))

@[simp] theorem weightExpr_eval (x ζ : ℝ) :
    weightExpr.eval (registers x ζ) = Source.weight 64 ζ x := by
  simp [weightExpr,Expr.eval,registers,Source.weight,pow_two]

theorem weightExpr_valid (x ζ : ℝ) : weightExpr.Valid (registers x ζ) := by
  simp only [weightExpr,Expr.Valid,Expr.eval,registers,Matrix.cons_val_zero,
    Matrix.cons_val_one,true_and]
  norm_num only [Rat.cast_one]
  constructor <;> nlinarith [sq_nonneg x,sq_nonneg ζ]

@[simp] theorem weightExpr_cost : weightExpr.cost = 23 := by rfl

theorem weight_executes (x ζ : ℝ) :
    Expr.Executes (registers x ζ) weightExpr (Source.weight 64 ζ x) 23 := by
  simpa using Expr.executes_of_valid (registers x ζ) weightExpr (weightExpr_valid x ζ)

def diagonalExpr : Expr (Fin 2) := .sqrt (.div weightExpr (.constant 64))

@[simp] theorem diagonalExpr_eval (x ζ : ℝ) :
    diagonalExpr.eval (registers x ζ) = Real.sqrt (Source.weight 64 ζ x / 64) := by
  simp [diagonalExpr,Expr.eval]

theorem diagonalExpr_valid {x ζ : ℝ} (hx : |x|≤1) :
    diagonalExpr.Valid (registers x ζ) := by
  refine ⟨⟨weightExpr_valid x ζ,trivial,by norm_num [Expr.eval]⟩,?_⟩
  change 0≤weightExpr.eval (registers x ζ)/64
  rw [weightExpr_eval]
  exact div_nonneg (Source.weight_nonneg (by norm_num) hx) (by norm_num)

@[simp] theorem diagonalExpr_cost : diagonalExpr.cost = 26 := by rfl

theorem diagonal_executes {x ζ : ℝ} (hx : |x|≤1) :
    Expr.Executes (registers x ζ) diagonalExpr
      (Real.sqrt (Source.weight 64 ζ x / 64)) 26 := by
  simpa using Expr.executes_of_valid (registers x ζ) diagonalExpr (diagonalExpr_valid hx)

end SeamlessKS.SourceEvaluation
