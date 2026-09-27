import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.List.OfFn
import Mathlib.Tactic

/-!
# Finite scalar circuits and their real-RAM operation counts

Only the listed primitives are executable nodes. Register loads, rational
constants, arithmetic operations, and scalar square roots each cost one.
Each circuit output also costs one store. Register names are fixed finite
addresses when a circuit is instantiated; constructing a parameterized circuit
or computing its loop budget is not certified by its evaluation cost.

Division and square root use Mathlib's total real functions in `eval`.
`Valid` explicitly requires nonzero divisors and nonnegative radicands, so
results advertised as real-RAM computations must supply this predicate.
There is no primitive for an optimizer, eigenvector, derivative, ceiling, or
arbitrary real-valued function.
-/

namespace MatrixSpencer.RealRAM

inductive Expr (ι : Type*) where
  | input : ι → Expr ι
  | constant : ℚ → Expr ι
  | add : Expr ι → Expr ι → Expr ι
  | sub : Expr ι → Expr ι → Expr ι
  | mul : Expr ι → Expr ι → Expr ι
  | div : Expr ι → Expr ι → Expr ι
  | sqrt : Expr ι → Expr ι

namespace Expr
variable {ι : Type*}

noncomputable def eval (v : ι → ℝ) : Expr ι → ℝ
  | .input i => v i
  | .constant q => q
  | .add a b => eval v a + eval v b
  | .sub a b => eval v a - eval v b
  | .mul a b => eval v a * eval v b
  | .div a b => eval v a / eval v b
  | .sqrt a => Real.sqrt (eval v a)

def cost : Expr ι → ℕ
  | .input _ => 1
  | .constant _ => 1
  | .add a b | .sub a b | .mul a b | .div a b => cost a + cost b + 1
  | .sqrt a => cost a + 1

def Valid (v : ι → ℝ) : Expr ι → Prop
  | .input _ | .constant _ => True
  | .add a b | .sub a b | .mul a b => Valid v a ∧ Valid v b
  | .div a b => Valid v a ∧ Valid v b ∧ eval v b ≠ 0
  | .sqrt a => Valid v a ∧ 0 ≤ eval v a

/-- A finite execution derivation records exactly the permitted primitive work. -/
inductive Executes (v : ι → ℝ) : Expr ι → ℝ → ℕ → Prop where
  | input (i : ι) : Executes v (.input i) (v i) 1
  | constant (q : ℚ) : Executes v (.constant q) q 1
  | add {a b : Expr ι} {x y : ℝ} {ka kb : ℕ} :
      Executes v a x ka → Executes v b y kb →
      Executes v (.add a b) (x + y) (ka + kb + 1)
  | sub {a b : Expr ι} {x y : ℝ} {ka kb : ℕ} :
      Executes v a x ka → Executes v b y kb →
      Executes v (.sub a b) (x - y) (ka + kb + 1)
  | mul {a b : Expr ι} {x y : ℝ} {ka kb : ℕ} :
      Executes v a x ka → Executes v b y kb →
      Executes v (.mul a b) (x * y) (ka + kb + 1)
  | div {a b : Expr ι} {x y : ℝ} {ka kb : ℕ} :
      Executes v a x ka → Executes v b y kb → y ≠ 0 →
      Executes v (.div a b) (x / y) (ka + kb + 1)
  | sqrt {a : Expr ι} {x : ℝ} {ka : ℕ} :
      Executes v a x ka → 0 ≤ x →
      Executes v (.sqrt a) (Real.sqrt x) (ka + 1)

theorem executes_of_valid (v : ι → ℝ) (e : Expr ι) (h : e.Valid v) :
    Executes v e (e.eval v) e.cost := by
  induction e with
  | input i => exact Executes.input i
  | constant q => exact Executes.constant q
  | add a b ia ib => exact Executes.add (ia h.1) (ib h.2)
  | sub a b ia ib => exact Executes.sub (ia h.1) (ib h.2)
  | mul a b ia ib => exact Executes.mul (ia h.1) (ib h.2)
  | div a b ia ib => exact Executes.div (ia h.1) (ib h.2.1) h.2.2
  | sqrt a ia => exact Executes.sqrt (ia h.1) h.2

theorem executes_spec {v : ι → ℝ} {e : Expr ι} {x : ℝ} {k : ℕ}
    (h : Executes v e x k) : e.Valid v ∧ x = e.eval v ∧ k = e.cost := by
  induction h with
  | input i => exact ⟨trivial, rfl, rfl⟩
  | constant q => exact ⟨trivial, rfl, rfl⟩
  | add ha hb ia ib => rcases ia with ⟨hva, rfl, rfl⟩; rcases ib with ⟨hvb, rfl, rfl⟩; exact ⟨⟨hva,hvb⟩,rfl,rfl⟩
  | sub ha hb ia ib => rcases ia with ⟨hva, rfl, rfl⟩; rcases ib with ⟨hvb, rfl, rfl⟩; exact ⟨⟨hva,hvb⟩,rfl,rfl⟩
  | mul ha hb ia ib => rcases ia with ⟨hva, rfl, rfl⟩; rcases ib with ⟨hvb, rfl, rfl⟩; exact ⟨⟨hva,hvb⟩,rfl,rfl⟩
  | div ha hb hn ia ib => rcases ia with ⟨hva, rfl, rfl⟩; rcases ib with ⟨hvb, rfl, rfl⟩; exact ⟨⟨hva,hvb,hn⟩,rfl,rfl⟩
  | sqrt ha hn ia => rcases ia with ⟨hva, rfl, rfl⟩; exact ⟨⟨hva,hn⟩,rfl,rfl⟩

def sumList : List (Expr ι) → Expr ι
  | [] => .constant 0
  | e :: es => .add e (sumList es)

theorem eval_sumList (v : ι → ℝ) (es : List (Expr ι)) :
    (sumList es).eval v = (es.map (eval v)).sum := by
  induction es with
  | nil => simp [sumList, eval]
  | cons e es ih => simp [sumList, eval, ih]

theorem cost_sumList (es : List (Expr ι)) :
    (sumList es).cost = 1 + es.length + (es.map cost).sum := by
  induction es with
  | nil => simp [sumList, cost]
  | cons e es ih => simp [sumList, cost, ih]; omega

theorem valid_sumList (v : ι → ℝ) (es : List (Expr ι))
    (h : ∀ e ∈ es, e.Valid v) : (sumList es).Valid v := by
  induction es with
  | nil => trivial
  | cons e es ih => exact ⟨h e (by simp), ih (fun a ha => h a (by simp [ha]))⟩

end Expr

structure Circuit (ι ο : Type*) where
  output : ο → Expr ι

namespace Circuit
variable {ι ο : Type*}

noncomputable def eval (c : Circuit ι ο) (v : ι → ℝ) : ο → ℝ :=
  fun o => (c.output o).eval v

def cost [Fintype ο] (c : Circuit ι ο) : ℕ := ∑ o, ((c.output o).cost + 1)

def Valid (c : Circuit ι ο) (v : ι → ℝ) : Prop := ∀ o, (c.output o).Valid v

theorem executes [Fintype ο] (c : Circuit ι ο) (v : ι → ℝ) (h : c.Valid v) :
    ∀ o, Expr.Executes v (c.output o) (c.eval v o) (c.output o).cost :=
  fun o => Expr.executes_of_valid v (c.output o) (h o)

end Circuit
end MatrixSpencer.RealRAM
