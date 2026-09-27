import MatrixSpencer.RealRAMFiniteEnumeration
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Matrix.Mul

/-! Complex finite matrix arithmetic compiled into pairs of primitive real
expressions. No complex number operation is a machine primitive. -/
open scoped BigOperators Matrix
noncomputable section
namespace MatrixSpencer.RealRAM

def finiteSumExpr {α ι : Type*} [Fintype α] [FiniteEnumeration α] (f : α → Expr ι) : Expr ι :=
  Expr.sumList ((FiniteEnumeration.elems (α:=α)).map f)

theorem finiteSumExpr_eval {α ι : Type*} [Fintype α] [FiniteEnumeration α] (f : α → Expr ι) (v : ι → ℝ) :
    (finiteSumExpr f).eval v = ∑i,(f i).eval v := by
  simp only [finiteSumExpr,Expr.eval_sumList,List.map_map]
  exact FiniteEnumeration.sum_eq _

theorem finiteSumExpr_valid {α ι : Type*} [Fintype α] [FiniteEnumeration α] (f : α → Expr ι) (v : ι → ℝ)
    (hf : ∀i,(f i).Valid v) : (finiteSumExpr f).Valid v := by
  apply Expr.valid_sumList
  intro e he
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp he
  exact hf _

theorem finiteSumExpr_cost {α ι : Type*} [Fintype α] [FiniteEnumeration α] (f : α → Expr ι) :
    (finiteSumExpr f).cost = 1+Fintype.card α+∑i,(f i).cost := by
  simp only [finiteSumExpr,Expr.cost_sumList,List.length_map,
    FiniteEnumeration.length_eq_card,List.map_map,FiniteEnumeration.sum_eq,Function.comp_apply]

/-- The uniform list-built sum has a primitive execution with the exact
scalar cost, whenever its operands are valid. -/
theorem finiteSumExpr_execution {α ι : Type*} [Fintype α] [FiniteEnumeration α]
    (f : α → Expr ι) (v : ι → ℝ) (hf : ∀ i,(f i).Valid v) :
    Expr.Executes v (finiteSumExpr f) (∑ i,(f i).eval v)
      (1+Fintype.card α+∑ i,(f i).cost) := by
  simpa only [finiteSumExpr_eval,finiteSumExpr_cost] using
    Expr.executes_of_valid v (finiteSumExpr f) (finiteSumExpr_valid f v hf)

/-- At a numerical dimension the generated syntax uses the literal range. -/
theorem finiteSumExpr_fin {ι : Type*} (n : ℕ) (f : Fin n → Expr ι) :
    finiteSumExpr f=Expr.sumList ((List.finRange n).map f) := rfl

theorem finiteSumExpr_cost_le {α ι : Type*} [Fintype α] [FiniteEnumeration α] (f : α → Expr ι)
    (b : ℕ) (hb : ∀i,(f i).cost≤b) : (finiteSumExpr f).cost ≤ Fintype.card α*(b+1)+1 := by
  have hs : (∑i,(f i).cost)≤Fintype.card α*b := by
    calc _≤∑_i:α,b := Finset.sum_le_sum fun i _ => hb i
         _=_ := by simp
  rw [finiteSumExpr_cost]
  nlinarith

structure ComplexExpr (ι : Type*) where
  re : Expr ι
  im : Expr ι

namespace ComplexExpr
variable {ι : Type*}
def eval (e : ComplexExpr ι) (v : ι → ℝ) : ℂ := ⟨e.re.eval v,e.im.eval v⟩
def cost (e : ComplexExpr ι) : ℕ := e.re.cost+e.im.cost
def Valid (e : ComplexExpr ι) (v : ι → ℝ) : Prop := e.re.Valid v ∧ e.im.Valid v
def zero : ComplexExpr ι := ⟨.constant 0,.constant 0⟩
def real (a : Expr ι) : ComplexExpr ι := ⟨a,.constant 0⟩
def add (a b : ComplexExpr ι) : ComplexExpr ι := ⟨.add a.re b.re,.add a.im b.im⟩
def mul (a b : ComplexExpr ι) : ComplexExpr ι :=
  ⟨.sub (.mul a.re b.re) (.mul a.im b.im),.add (.mul a.re b.im) (.mul a.im b.re)⟩
def conj (a : ComplexExpr ι) : ComplexExpr ι := ⟨a.re,.sub (.constant 0) a.im⟩
def smul (a : Expr ι) (b : ComplexExpr ι) : ComplexExpr ι := ⟨.mul a b.re,.mul a b.im⟩
def sum {α : Type*} [Fintype α] [FiniteEnumeration α] (f : α → ComplexExpr ι) : ComplexExpr ι :=
  ⟨finiteSumExpr (fun i => (f i).re),finiteSumExpr (fun i => (f i).im)⟩

@[simp] theorem eval_zero (v : ι → ℝ) : zero.eval v=0 := by apply Complex.ext <;> simp [zero,eval,Expr.eval]
@[simp] theorem eval_real (a : Expr ι) (v : ι → ℝ) : (real a).eval v=(a.eval v:ℂ) := by apply Complex.ext <;> simp [real,eval,Expr.eval]
@[simp] theorem eval_add (a b : ComplexExpr ι) (v : ι → ℝ) :
    (add a b).eval v=a.eval v+b.eval v := rfl
@[simp] theorem eval_mul (a b : ComplexExpr ι) (v : ι → ℝ) :
    (mul a b).eval v=a.eval v*b.eval v := rfl
@[simp] theorem eval_conj (a : ComplexExpr ι) (v : ι → ℝ) :
    (conj a).eval v=star (a.eval v) := by apply Complex.ext <;> simp [conj,eval,Expr.eval]
@[simp] theorem eval_smul (a : Expr ι) (b : ComplexExpr ι) (v : ι → ℝ) :
    (smul a b).eval v=a.eval v • b.eval v := by apply Complex.ext <;> simp [smul,eval,Expr.eval]
@[simp] theorem eval_sum {α : Type*} [Fintype α] [FiniteEnumeration α] (f : α → ComplexExpr ι) (v : ι → ℝ) :
    (sum f).eval v=∑i,(f i).eval v := by
  apply Complex.ext <;> simp [sum,eval,finiteSumExpr_eval]

theorem valid_zero (v : ι → ℝ) : zero.Valid v := ⟨trivial,trivial⟩
theorem valid_real (a : Expr ι) (v : ι → ℝ) (ha : a.Valid v) : (real a).Valid v := ⟨ha,trivial⟩
theorem valid_add {a b : ComplexExpr ι} {v : ι → ℝ} (ha : a.Valid v) (hb : b.Valid v) :
    (add a b).Valid v := ⟨⟨ha.1,hb.1⟩,⟨ha.2,hb.2⟩⟩
theorem valid_mul {a b : ComplexExpr ι} {v : ι → ℝ} (ha : a.Valid v) (hb : b.Valid v) :
    (mul a b).Valid v := ⟨⟨⟨ha.1,hb.1⟩,⟨ha.2,hb.2⟩⟩,⟨⟨ha.1,hb.2⟩,⟨ha.2,hb.1⟩⟩⟩
theorem valid_conj {a : ComplexExpr ι} {v : ι → ℝ} (ha : a.Valid v) :
    (conj a).Valid v := ⟨ha.1,⟨trivial,ha.2⟩⟩
theorem valid_smul {a : Expr ι} {b : ComplexExpr ι} {v : ι → ℝ}
    (ha : a.Valid v) (hb : b.Valid v) : (smul a b).Valid v := ⟨⟨ha,hb.1⟩,⟨ha,hb.2⟩⟩
theorem valid_sum {α : Type*} [Fintype α] [FiniteEnumeration α] (f : α → ComplexExpr ι) (v : ι → ℝ)
    (hf : ∀i,(f i).Valid v) : (sum f).Valid v :=
  ⟨finiteSumExpr_valid _ _ (fun i => (hf i).1),finiteSumExpr_valid _ _ (fun i => (hf i).2)⟩

theorem cost_zero : (zero:ComplexExpr ι).cost=2 := rfl
theorem cost_real (a : Expr ι) : (real a).cost=a.cost+1 := rfl
theorem cost_add (a b : ComplexExpr ι) : (add a b).cost=a.cost+b.cost+2 := by simp [cost,add,Expr.cost];omega
theorem cost_mul (a b : ComplexExpr ι) : (mul a b).cost=2*a.cost+2*b.cost+6 := by
  simp [cost,mul,Expr.cost];omega
theorem cost_conj (a : ComplexExpr ι) : (conj a).cost=a.cost+2 := by simp [cost,conj,Expr.cost];omega
theorem cost_smul (a : Expr ι) (b : ComplexExpr ι) : (smul a b).cost=2*a.cost+b.cost+2 := by
  simp [cost,smul,Expr.cost];omega
theorem cost_sum {α : Type*} [Fintype α] [FiniteEnumeration α] (f : α → ComplexExpr ι) :
    (sum f).cost=2+2*Fintype.card α+∑i,(f i).cost := by
  simp [cost,sum,finiteSumExpr_cost,Finset.sum_add_distrib];omega
theorem cost_sum_le {α : Type*} [Fintype α] [FiniteEnumeration α] (f : α → ComplexExpr ι)
    (b : ℕ) (hb : ∀i,(f i).cost≤b) : (sum f).cost≤Fintype.card α*(b+2)+2 := by
  have hs : (∑i,(f i).cost)≤Fintype.card α*b := by
    calc _≤∑_i:α,b := Finset.sum_le_sum fun i _ => hb i
         _=_ := by simp
  rw [cost_sum]
  nlinarith

def matrixMul {α β γ : Type*} [Fintype β] [FiniteEnumeration β]
    (A : α → β → ComplexExpr ι) (B : β → γ → ComplexExpr ι) (i : α) (j : γ) : ComplexExpr ι :=
  sum (fun k => mul (A i k) (B k j))

theorem matrixMul_eval {α β γ : Type*} [Fintype β] [FiniteEnumeration β]
    (A : α → β → ComplexExpr ι) (B : β → γ → ComplexExpr ι) (v : ι → ℝ) (i : α) (j : γ) :
    (matrixMul A B i j).eval v =
      (Matrix.of (fun i j => (A i j).eval v) * Matrix.of (fun i j => (B i j).eval v)) i j := by
  simp [matrixMul,Matrix.mul_apply]

theorem matrixMul_valid {α β γ : Type*} [Fintype β] [FiniteEnumeration β]
    (A : α → β → ComplexExpr ι) (B : β → γ → ComplexExpr ι) (v : ι → ℝ)
    (hA : ∀i j,(A i j).Valid v) (hB : ∀i j,(B i j).Valid v) (i : α) (j : γ) :
    (matrixMul A B i j).Valid v := valid_sum _ _ (fun k => valid_mul (hA i k) (hB k j))

theorem matrixMul_cost {α β γ : Type*} [Fintype β] [FiniteEnumeration β]
    (A : α → β → ComplexExpr ι) (B : β → γ → ComplexExpr ι)
    (a b : ℕ) (hA : ∀i j,(A i j).cost≤a) (hB : ∀i j,(B i j).cost≤b) (i : α) (j : γ) :
    (matrixMul A B i j).cost ≤ Fintype.card β*(2*a+2*b+8)+2 := by
  apply cost_sum_le _ (2*a+2*b+6)
  intro k
  rw [cost_mul]
  have ha := hA i k
  have hb := hB k j
  omega

theorem executes (a : ComplexExpr ι) (v : ι → ℝ) (ha : a.Valid v) :
    Expr.Executes v a.re (a.eval v).re a.re.cost ∧
    Expr.Executes v a.im (a.eval v).im a.im.cost :=
  ⟨Expr.executes_of_valid _ _ ha.1,Expr.executes_of_valid _ _ ha.2⟩

end ComplexExpr
end MatrixSpencer.RealRAM
