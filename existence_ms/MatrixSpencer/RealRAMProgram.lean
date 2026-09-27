import MatrixSpencer.RealRAMCircuit

/-!
# Real-RAM programs with branch and bounded-loop execution costs

`repeat n p` is a counted loop with a supplied natural budget. Its setup and
each iteration's control cost are charged. Calculating `n` from real input
data requires a separate implementation and is not free in an end-to-end
runtime claim. The language has no call instruction for an opaque optimizer
or other arbitrary mathematical function.
-/

namespace MatrixSpencer.RealRAM

inductive Program (ι : Type*) where
  | skip : Program ι
  | assign : ι → Expr ι → Program ι
  | seq : Program ι → Program ι → Program ι
  | branchLE : Expr ι → Expr ι → Program ι → Program ι → Program ι
  | repeat : ℕ → Program ι → Program ι

namespace Program
variable {ι : Type*} [DecidableEq ι]

noncomputable def run : Program ι → (ι → ℝ) → (ι → ℝ)
  | .skip, v => v
  | .assign i e, v => Function.update v i (e.eval v)
  | .seq p q, v => run q (run p v)
  | .branchLE a b p q, v => if a.eval v ≤ b.eval v then run p v else run q v
  | .repeat n p, v => (run p)^[n] v

def loopCost (step : (ι → ℝ) → (ι → ℝ)) (charge : (ι → ℝ) → ℕ) :
    ℕ → (ι → ℝ) → ℕ
  | 0, _ => 1
  | n+1, v => charge v + 1 + loopCost step charge n (step v)

noncomputable def cost : Program ι → (ι → ℝ) → ℕ
  | .skip, _ => 0
  | .assign _ e, _ => e.cost + 1
  | .seq p q, v => cost p v + cost q (run p v)
  | .branchLE a b p q, v =>
      a.cost + b.cost + 1 + if a.eval v ≤ b.eval v then cost p v else cost q v
  | .repeat n p, v => loopCost (run p) (cost p) n v

def Safe : Program ι → (ι → ℝ) → Prop
  | .skip, _ => True
  | .assign _ e, v => e.Valid v
  | .seq p q, v => Safe p v ∧ Safe q (run p v)
  | .branchLE a b p q, v => a.Valid v ∧ b.Valid v ∧
      if a.eval v ≤ b.eval v then Safe p v else Safe q v
  | .repeat n p, v => ∀ k < n, Safe p ((run p)^[k] v)

def bound : Program ι → ℕ
  | .skip => 0
  | .assign _ e => e.cost + 1
  | .seq p q => bound p + bound q
  | .branchLE a b p q => a.cost + b.cost + 1 + max (bound p) (bound q)
  | .repeat n p => n * (bound p + 1) + 1

omit [DecidableEq ι] in
theorem loopCost_le (step : (ι → ℝ) → (ι → ℝ)) (charge : (ι → ℝ) → ℕ)
    (b : ℕ) (hb : ∀ v, charge v ≤ b) (n : ℕ) (v : ι → ℝ) :
    loopCost step charge n v ≤ n*(b+1)+1 := by
  induction n generalizing v with
  | zero => simp [loopCost]
  | succ n ih =>
    rw [loopCost]
    have h := ih (step v)
    have hc := hb v
    nlinarith

theorem cost_le_bound (p : Program ι) (v : ι → ℝ) : cost p v ≤ p.bound := by
  induction p generalizing v with
  | skip => exact le_rfl
  | assign i e => exact le_rfl
  | seq p q ip iq => exact Nat.add_le_add (ip v) (iq (run p v))
  | branchLE a b p q ip iq =>
    simp only [cost, bound]
    split_ifs
    · exact Nat.add_le_add_left ((ip v).trans (Nat.le_max_left _ _)) _
    · exact Nat.add_le_add_left ((iq v).trans (Nat.le_max_right _ _)) _
  | «repeat» n p ip => exact loopCost_le (run p) (cost p) p.bound ip n v

/-- Actual execution derivations, including the selected branch and every loop step. -/
inductive Executes : Program ι → (ι → ℝ) → (ι → ℝ) → ℕ → Prop where
  | skip (v : ι → ℝ) : Executes .skip v v 0
  | assign (i : ι) {e : Expr ι} {v : ι → ℝ} {x : ℝ} {k : ℕ} :
      Expr.Executes v e x k → Executes (.assign i e) v (Function.update v i x) (k+1)
  | seq {p q : Program ι} {v w z : ι → ℝ} {kp kq : ℕ} :
      Executes p v w kp → Executes q w z kq → Executes (.seq p q) v z (kp+kq)
  | branchTrue {a b : Expr ι} {p q : Program ι} {v w : ι → ℝ}
      {x y : ℝ} {ka kb kp : ℕ} :
      Expr.Executes v a x ka → Expr.Executes v b y kb → x ≤ y →
      Executes p v w kp → Executes (.branchLE a b p q) v w (ka+kb+1+kp)
  | branchFalse {a b : Expr ι} {p q : Program ι} {v w : ι → ℝ}
      {x y : ℝ} {ka kb kq : ℕ} :
      Expr.Executes v a x ka → Expr.Executes v b y kb → ¬ x ≤ y →
      Executes q v w kq → Executes (.branchLE a b p q) v w (ka+kb+1+kq)
  | repeatZero (p : Program ι) (v : ι → ℝ) : Executes (.repeat 0 p) v v 1
  | repeatSucc {p : Program ι} {n : ℕ} {v w z : ι → ℝ} {kp kr : ℕ} :
      Executes p v w kp → Executes (.repeat n p) w z kr →
      Executes (.repeat (n+1) p) v z (kp+1+kr)

theorem executes_of_safe (p : Program ι) (v : ι → ℝ) (h : p.Safe v) :
    Executes p v (p.run v) (p.cost v) := by
  induction p generalizing v with
  | skip => exact Executes.skip v
  | assign i e => exact Executes.assign i (Expr.executes_of_valid v e h)
  | seq p q ip iq => exact Executes.seq (ip v h.1) (iq (run p v) h.2)
  | branchLE a b p q ip iq =>
    obtain ⟨ha, hb, hbranch⟩ := h
    by_cases hle : a.eval v ≤ b.eval v
    · simp only [hle, ↓reduceIte] at hbranch
      simpa only [run, cost, hle, ↓reduceIte] using
        Executes.branchTrue (q := q) (Expr.executes_of_valid v a ha)
          (Expr.executes_of_valid v b hb) hle (ip v hbranch)
    · simp only [hle, ↓reduceIte] at hbranch
      simpa only [run, cost, hle, ↓reduceIte] using
        Executes.branchFalse (p := p) (Expr.executes_of_valid v a ha)
          (Expr.executes_of_valid v b hb) hle (iq v hbranch)
  | «repeat» n p ip =>
    induction n generalizing v with
    | zero => simpa only [run, cost, loopCost, Function.iterate_zero, id_eq] using Executes.repeatZero p v
    | succ n ih =>
      have hfirst : p.Safe v := by simpa using h 0 (by omega)
      have hrest : (Program.repeat n p).Safe (p.run v) := by
        intro k hk
        simpa only [Function.iterate_succ_apply] using h (k+1) (by omega)
      simpa only [run, cost, loopCost, Function.iterate_succ_apply] using
        Executes.repeatSucc (ip v hfirst) (ih (p.run v) hrest)

/-- Every safe run has an execution derivation and the syntactic operation bound. -/
theorem safe_execution_bounded (p : Program ι) (v : ι → ℝ) (h : p.Safe v) :
    ∃ k ≤ p.bound, Executes p v (p.run v) k :=
  ⟨p.cost v, p.cost_le_bound v, p.executes_of_safe v h⟩

end Program
end MatrixSpencer.RealRAM
