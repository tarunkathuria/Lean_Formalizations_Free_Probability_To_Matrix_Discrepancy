import MatrixSpencer.KSEighthRetirementLoop
import MatrixSpencer.RealRAMJacobiIteration

/-!
# Counted endpoint preparation for both KS walks

The evaluator below returns exactly the existing retirement-loop result. It
charges every report call, real comparison, scalar update, state copy, and
list/loop operation. Reports are explicitly parameterized counted operations;
their cost must be supplied by the value-solver layer before this is used in
a total runtime theorem. This is an intermediate composition lemma.

The scalar acceptance test has a safe `RealRAM.Program` implementation. The
eager evaluator calls both reports even at a frozen coordinate, a harmless
implementation choice with identical scan order and output.
-/

open Set
noncomputable section
namespace MatrixSpencer.KSRetirementRuntime

open RealRAM
open RealRAM.JacobiIteration (Counted)
attribute [local instance] Classical.propDecidable

inductive Register where
  | coordinate | radius | tolerance | current | proposed | result
  deriving DecidableEq, Fintype

def reject : Program Register := .assign .result (.constant 0)
def accept : Program Register := .assign .result (.constant 1)

def decision : Program Register :=
  .branchLE (.input .radius) (.input .coordinate) reject
    (.branchLE (.input .coordinate) (.sub (.constant 0) (.input .radius)) reject
      (.branchLE (.sub (.input .proposed) (.input .current))
        (.div (.input .tolerance) (.constant 2)) accept reject))

theorem decision_safe (v : Register → ℝ) : decision.Safe v := by
  simp [decision, reject, accept, Program.Safe, Expr.Valid, Expr.eval]

theorem decision_bound : decision.bound = 17 := by
  norm_num [decision, reject, accept, Program.bound, Expr.cost]

theorem decision_result (v : Register → ℝ) :
    decision.run v .result =
      if |v .coordinate| < v .radius ∧ v .proposed - v .current ≤ v .tolerance/2
      then 1 else 0 := by
  simp only [decision, Program.run, Expr.eval, Rat.cast_zero, Rat.cast_one,
    Rat.cast_ofNat, zero_sub]
  by_cases hu : v .radius ≤ v .coordinate
  · rw [if_pos hu, if_neg (by intro h; exact (not_lt_of_ge hu) (lt_of_le_of_lt (le_abs_self _) h.1))]
    simp [reject, Program.run, Expr.eval]
  · rw [if_neg hu]
    by_cases hl : v .coordinate ≤ -v .radius
    · rw [if_pos hl, if_neg (by intro h; have := (abs_lt.mp h.1).1; linarith)]
      simp [reject, Program.run, Expr.eval]
    · have hab : |v .coordinate| < v .radius := abs_lt.mpr ⟨by linarith, by linarith⟩
      rw [if_neg hl]
      simp only [hab, true_and]
      split_ifs <;> simp_all [reject, accept, Program.run, Expr.eval]

theorem decision_execution (v : Register → ℝ) :
    ∃ k ≤ 17, Program.Executes decision v (decision.run v) k := by
  simpa only [decision_bound] using Program.safe_execution_bounded decision v (decision_safe v)

variable {N : ℕ}
abbrev Report (N : ℕ) := (Fin N → ℝ) → Counted ℝ

def input (a τ : ℝ) (x : Fin N → ℝ) (c : KSEighthRetirementLoop.Candidate N)
    (r0 r1 : ℝ) : Register → ℝ
  | .coordinate => x c.1
  | .radius => a
  | .tolerance => τ
  | .current => r0
  | .proposed => r1
  | .result => 0

/-- The state copy is charged linearly, rather than treating a function update
as a free persistent map operation. -/
def test (a τ : ℝ) (report : Report N) (x : Fin N → ℝ)
    (c : KSEighthRetirementLoop.Candidate N) : Counted Bool :=
  let next := KSEighthRetirementLoop.update a x c
  let r0 := report x
  let r1 := report next
  let v := input a τ x c r0.value r1.value
  ⟨decide (decision.run v .result = 1),
    r0.cost+r1.cost+decision.cost v+3*N+20⟩

theorem test_value (a τ : ℝ) (report : Report N) (x : Fin N → ℝ)
    (c : KSEighthRetirementLoop.Candidate N) :
    (test a τ report x c).value =
      decide (KSEighthRetirementLoop.accepted a τ (fun y => (report y).value) x c) := by
  simp [test, decision_result, input, KSEighthRetirementLoop.accepted]

theorem test_cost {a τ : ℝ} (ha : 0 ≤ a) (report : Report N)
    {Q : ℕ} (hQ : ∀ x ∈ ksCube a, (report x).cost ≤ Q)
    {x : Fin N → ℝ} (hx : x ∈ ksCube a) (c : KSEighthRetirementLoop.Candidate N) :
    (test a τ report x c).cost ≤ 2*Q+3*N+39 := by
  have h0 := hQ x hx
  have h1 := hQ (KSEighthRetirementLoop.update a x c) (KSEighthRetirementLoop.update_mem_cube ha hx c)
  have h2 := decision.cost_le_bound
    (input a τ x c (report x).value (report (KSEighthRetirementLoop.update a x c)).value)
  rw [decision_bound] at h2
  dsimp only [test]
  omega

def scan (a τ : ℝ) (report : Report N) (x : Fin N → ℝ) :
    List (KSEighthRetirementLoop.Candidate N) → Counted (Option (KSEighthRetirementLoop.Candidate N))
  | [] => ⟨none, 1⟩
  | c::cs =>
    let t := test a τ report x c
    if t.value then ⟨some c, t.cost+3⟩ else
      let rest := scan a τ report x cs
      ⟨rest.value, t.cost+rest.cost+3⟩

theorem scan_value (a τ : ℝ) (report : Report N) (x : Fin N → ℝ)
    (cs : List (KSEighthRetirementLoop.Candidate N)) :
    (scan a τ report x cs).value =
      KSEighthRetirementLoop.scan a τ (fun y => (report y).value) x cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [scan, test_value, KSEighthRetirementLoop.scan, decide_eq_true_eq]
    split_ifs <;> simp_all

theorem scan_cost {a τ : ℝ} (ha : 0 ≤ a) (report : Report N)
    {Q : ℕ} (hQ : ∀ x ∈ ksCube a, (report x).cost ≤ Q)
    {x : Fin N → ℝ} (hx : x ∈ ksCube a) (cs : List (KSEighthRetirementLoop.Candidate N)) :
    (scan a τ report x cs).cost ≤ cs.length*(2*Q+3*N+42)+1 := by
  induction cs with
  | nil => simp [scan]
  | cons c cs ih =>
    have ht := test_cost (τ := τ) ha report hQ hx c
    simp only [scan, List.length_cons]
    split_ifs <;> dsimp
    · nlinarith
    · nlinarith

/-- Enumerating the `2N` candidates is charged even though the same list
could be cached once for the entire run. -/
def select (a τ : ℝ) (report : Report N) (x : Fin N → ℝ) :
    Counted (Option (KSEighthRetirementLoop.Candidate N)) :=
  let s := scan a τ report x Finset.univ.toList
  ⟨s.value, s.cost+10*N+1⟩

theorem select_value (a τ : ℝ) (report : Report N) (x : Fin N → ℝ) :
    (select a τ report x).value = KSEighthRetirementLoop.select a τ (fun y => (report y).value) x :=
  scan_value a τ report x _

theorem select_cost {a τ : ℝ} (ha : 0 ≤ a) (report : Report N)
    {Q : ℕ} (hQ : ∀ x ∈ ksCube a, (report x).cost ≤ Q)
    {x : Fin N → ℝ} (hx : x ∈ ksCube a) :
    (select a τ report x).cost ≤ 2*N*(2*Q+3*N+42)+10*N+2 := by
  have h := scan_cost (τ := τ) ha report hQ hx (Finset.univ.toList : List (KSEighthRetirementLoop.Candidate N))
  simp only [Finset.length_toList, Finset.card_univ, Fintype.card_prod,
    Fintype.card_fin, Fintype.card_bool] at h
  dsimp only [select]
  nlinarith

def prepare (a τ : ℝ) (report : Report N) : ℕ → (Fin N → ℝ) → Counted (Fin N → ℝ)
  | 0, x => ⟨x, 1⟩
  | k+1, x =>
    let s := select a τ report x
    match s.value with
    | none => ⟨x, s.cost+2⟩
    | some c =>
      let rest := prepare a τ report k (KSEighthRetirementLoop.update a x c)
      ⟨rest.value, s.cost+rest.cost+3*N+6⟩

theorem prepare_value (a τ : ℝ) (report : Report N) (k : ℕ) (x : Fin N → ℝ) :
    (prepare a τ report k x).value =
      KSEighthRetirementLoop.prepare a τ (fun y => (report y).value) k x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    simp only [prepare, select_value, KSEighthRetirementLoop.prepare]
    split <;> simp_all

def roundBudget (N Q : ℕ) : ℕ := 2*N*(2*Q+3*N+42)+13*N+8

theorem prepare_cost {a τ : ℝ} (ha : 0 ≤ a) (report : Report N)
    {Q : ℕ} (hQ : ∀ x ∈ ksCube a, (report x).cost ≤ Q)
    (k : ℕ) {x : Fin N → ℝ} (hx : x ∈ ksCube a) :
    (prepare a τ report k x).cost ≤ k*roundBudget N Q+1 := by
  induction k generalizing x with
  | zero => simp [prepare]
  | succ k ih =>
    have hs := select_cost (τ := τ) ha report hQ hx
    simp only [prepare]
    cases he : (select a τ report x).value with
    | none =>
      dsimp
      dsimp [roundBudget]
      nlinarith
    | some c =>
      have hi := ih (KSEighthRetirementLoop.update_mem_cube ha hx c)
      dsimp
      dsimp [roundBudget] at hi ⊢
      nlinarith


theorem preparation_cost {a τ : ℝ} (ha : 0 ≤ a) (report : Report N)
    {Q : ℕ} (hQ : ∀ x ∈ ksCube a, (report x).cost ≤ Q)
    {x : Fin N → ℝ} (hx : x ∈ ksCube a) :
    (prepare a τ report N x).cost ≤ 6*(N+1)^3*(Q+20) := by
  have h := prepare_cost (τ := τ) ha report hQ N hx
  calc
    _ ≤ N*roundBudget N Q+1 := h
    _ ≤ _ := by dsimp [roundBudget]; ring_nf; omega

end MatrixSpencer.KSRetirementRuntime
