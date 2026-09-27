import MatrixSpencer.RealRAMJacobiRotation
import MatrixSpencer.RealRAMLinearAlgebra
import MatrixSpencer.KSJacobiRayleigh

/-!
# Counted primitive composition for the actual finite Jacobi iteration

This is a typed composition of scalar `Expr`/`Program` executions and finite
address/control operations. It is not a new opaque Jacobi primitive. Matrix
products are evaluated entrywise by the existing scalar multiplication
circuits; the coefficients are the existing safe scalar Jacobi program; the
pivot scan executes both squared-entry expressions and a real comparison.

The scan preserves the original tie rule: the earlier candidate wins equality.
The state stores the current matrix and accumulated basis, so previous rounds
are not recomputed. Its output is proved equal to both original recurrences.
Construction of a supplied natural iteration budget is a separate operation.
-/

open Matrix
open scoped BigOperators
noncomputable section
namespace MatrixSpencer.RealRAM.JacobiIteration

abbrev Entries (d : ℕ) := Fin d × Fin d
abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) ℝ

structure Counted (α : Type*) where
  value : α
  cost : ℕ

def entries {d : ℕ} (A : Mat d) : Entries d → ℝ := fun p => A p.1 p.2

def scoreExpr {d : ℕ} (p : Entries d) : Expr (Entries d) :=
  .mul (.input p) (.input p)

theorem scoreExpr_executes {d : ℕ} (A : Mat d) (p : Entries d) :
    Expr.Executes (entries A) (scoreExpr p) (KSJacobiIteration.pivotScore A p) 3 := by
  simpa [scoreExpr, entries, KSJacobiIteration.pivotScore, pow_two] using
    Expr.Executes.mul (Expr.Executes.input (v := entries A) p)
      (Expr.Executes.input (v := entries A) p)

/-- Tail-first finite scan, including list tests, result stores, and comparisons. -/
def scan {d : ℕ} (A : Mat d) : List (Entries d) → Counted (Option (Entries d))
  | [] => ⟨none, 1⟩
  | p :: ps =>
    let tail := scan A ps
    match tail.value with
    | none => ⟨some p, tail.cost + 2⟩
    | some q =>
      let left := (scoreExpr q).eval (entries A)
      let right := (scoreExpr p).eval (entries A)
      ⟨if left ≤ right then some p else some q,
        tail.cost + (scoreExpr q).cost + (scoreExpr p).cost + 3⟩

theorem scan_value {d : ℕ} (A : Mat d) (ps : List (Entries d)) :
    (scan A ps).value = KSJacobiIteration.maxScan (KSJacobiIteration.pivotScore A) ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [scan, KSJacobiIteration.maxScan]
    rw [ih]
    cases KSJacobiIteration.maxScan (KSJacobiIteration.pivotScore A) ps with
    | none => rfl
    | some q => simp [scoreExpr, Expr.eval, entries, KSJacobiIteration.pivotScore, pow_two]

theorem scan_cost {d : ℕ} (A : Mat d) (ps : List (Entries d)) :
    (scan A ps).cost ≤ 9 * ps.length + 1 := by
  induction ps with
  | nil => simp [scan]
  | cons p ps ih =>
    simp only [scan, List.length_cons]
    cases (scan A ps).value with
    | none => dsimp; omega
    | some q => dsimp [scoreExpr, Expr.cost]; omega

/-- An execution derivation for the scan, with the actual two scalar score
executions and their selected comparison at each nonempty tail. -/
inductive ScanExec {d : ℕ} (A : Mat d) :
    List (Entries d) → Option (Entries d) → ℕ → Prop where
  | nil : ScanExec A [] none 1
  | emptyTail {ps : List (Entries d)} {k : ℕ} (p : Entries d) :
      ScanExec A ps none k → ScanExec A (p::ps) (some p) (k+2)
  | chooseEarlier {ps : List (Entries d)} {k : ℕ} (p q : Entries d) {x y : ℝ} :
      ScanExec A ps (some q) k →
      Expr.Executes (entries A) (scoreExpr q) x 3 →
      Expr.Executes (entries A) (scoreExpr p) y 3 → x ≤ y →
      ScanExec A (p::ps) (some p) (k+9)
  | chooseLater {ps : List (Entries d)} {k : ℕ} (p q : Entries d) {x y : ℝ} :
      ScanExec A ps (some q) k →
      Expr.Executes (entries A) (scoreExpr q) x 3 →
      Expr.Executes (entries A) (scoreExpr p) y 3 → ¬ x ≤ y →
      ScanExec A (p::ps) (some q) (k+9)

theorem scan_executes {d : ℕ} (A : Mat d) (ps : List (Entries d)) :
    ScanExec A ps (scan A ps).value (scan A ps).cost := by
  induction ps with
  | nil => exact ScanExec.nil
  | cons p ps ih =>
    cases he : (scan A ps).value with
    | none =>
      rw [he] at ih
      simpa only [scan, he] using ScanExec.emptyTail p ih
    | some q =>
      rw [he] at ih
      have hx := scoreExpr_executes A q
      have hy := scoreExpr_executes A p
      by_cases hle : KSJacobiIteration.pivotScore A q ≤ KSJacobiIteration.pivotScore A p
      · have hcmp : A q.1 q.2 * A q.1 q.2 ≤ A p.1 p.2 * A p.1 p.2 := by
          simpa [KSJacobiIteration.pivotScore, pow_two] using hle
        simpa [scan, he, scoreExpr, Expr.cost, Expr.eval, entries, hcmp,
          KSJacobiIteration.pivotScore, pow_two, Nat.add_assoc] using
          ScanExec.chooseEarlier p q ih hx hy hle
      · have hcmp : ¬ A q.1 q.2 * A q.1 q.2 ≤ A p.1 p.2 * A p.1 p.2 := by
          simpa [KSJacobiIteration.pivotScore, pow_two] using hle
        simpa [scan, he, scoreExpr, Expr.cost, Expr.eval, entries, hcmp,
          KSJacobiIteration.pivotScore, pow_two, Nat.add_assoc] using
          ScanExec.chooseLater p q ih hx hy hle

/-- Indexed finite-address generation: one comparison and bounded list/control
work per index pair. This uses the same order as `candidates`. -/
def row {d : ℕ} (i : Fin d) : List (Fin d) → Counted (List (Entries d))
  | [] => ⟨[], 1⟩
  | j :: js =>
    let tail := row i js
    ⟨if i ≠ j then (i,j) :: tail.value else tail.value, tail.cost + 4⟩

theorem row_value {d : ℕ} (i : Fin d) (js : List (Fin d)) :
    (row i js).value = (js.map (fun j => (i,j))).filter (fun p => p.1 ≠ p.2) := by
  induction js with
  | nil => rfl
  | cons j js ih => simp [row, ih]; split_ifs <;> simp_all

theorem row_cost {d : ℕ} (i : Fin d) (js : List (Fin d)) :
    (row i js).cost = 4 * js.length + 1 := by
  induction js with
  | nil => rfl
  | cons j js ih => simp [row, ih]; omega

def generate {d : ℕ} (js : List (Fin d)) : List (Fin d) → Counted (List (Entries d))
  | [] => ⟨[], 1⟩
  | i :: is =>
    let first := row i js
    let tail := generate js is
    ⟨first.value ++ tail.value, first.cost + tail.cost + first.value.length + 2⟩

theorem generate_value {d : ℕ} (is js : List (Fin d)) :
    (generate js is).value =
      (is.flatMap (fun i => js.map (fun j => (i,j)))).filter (fun p => p.1 ≠ p.2) := by
  induction is with
  | nil => rfl
  | cons i is ih => simp [generate, row_value, ih]

theorem row_length_le {d : ℕ} (i : Fin d) (js : List (Fin d)) :
    (row i js).value.length ≤ js.length := by
  rw [row_value]
  exact (List.length_filter_le _ _).trans_eq (List.length_map _)

theorem generate_cost {d : ℕ} (is js : List (Fin d)) :
    (generate js is).cost ≤ is.length * (5 * js.length + 3) + 1 := by
  induction is with
  | nil => simp [generate]
  | cons i is ih =>
    simp only [generate, List.length_cons, row_cost]
    have hl := row_length_le i js
    nlinarith

def pivot {d : ℕ} (A : Mat d) : Counted (Option (Entries d)) :=
  let ps := generate (List.finRange d) (List.finRange d)
  let result := scan A ps.value
  -- Two finite index ranges, including one index successor/store per element.
  ⟨result.value, 4*d + 2 + ps.cost + result.cost⟩

theorem pivot_value {d : ℕ} (A : Mat d) : (pivot A).value = KSJacobiIteration.pivot A := by
  simp [pivot, scan_value, generate_value, KSJacobiIteration.pivot, KSJacobiIteration.candidates]

theorem candidates_length_le (d : ℕ) : (KSJacobiIteration.candidates d).length ≤ d*d := by
  unfold KSJacobiIteration.candidates
  apply (List.length_filter_le _ _).trans
  simp

theorem pivot_cost {d : ℕ} (A : Mat d) : (pivot A).cost ≤ 20*(d+1)^2 := by
  have hg := generate_cost (List.finRange d) (List.finRange d)
  have hs := scan_cost A (generate (List.finRange d) (List.finRange d)).value
  have hl := candidates_length_le d
  have he : (generate (List.finRange d) (List.finRange d)).value =
      KSJacobiIteration.candidates d := by simp [generate_value, KSJacobiIteration.candidates]
  rw [he] at hs
  simp only [List.length_finRange] at hg
  dsimp [pivot]
  rw [he]
  nlinarith

/-- Rotation matrix entry circuit. Index tests are finite address/control
operations; the scalar work here consists of copies, constants, and negation. -/
def rotationExpr {d : ℕ} (i j : Fin d) (p : Entries d) : Expr Jacobi.Registers :=
  if p.2 = i then
    .add (if p.1 = i then .input 3 else .constant 0)
      (if p.1 = j then .sub (.constant 0) (.input 4) else .constant 0)
  else if p.2 = j then
    .add (if p.1 = i then .input 4 else .constant 0)
      (if p.1 = j then .input 3 else .constant 0)
  else if p.1 = p.2 then .constant 1 else .constant 0

def rotationCircuit {d : ℕ} (i j : Fin d) : Circuit Jacobi.Registers (Entries d) :=
  ⟨rotationExpr i j⟩

theorem rotationCircuit_eval {d : ℕ} (i j : Fin d) (v : Jacobi.Registers → ℝ)
    (k l : Fin d) :
    (rotationCircuit i j).eval v (k,l) = KSJacobiStep.embedding i j (v 3) (v 4) k l := by
  simp only [Circuit.eval, rotationCircuit, rotationExpr, KSJacobiStep.embedding]
  split_ifs <;> simp [Expr.eval]

theorem rotationCircuit_valid {d : ℕ} (i j : Fin d) (v : Jacobi.Registers → ℝ) :
    (rotationCircuit i j).Valid v := by
  intro p
  dsimp [rotationCircuit, rotationExpr]
  split_ifs <;> simp [Expr.Valid]

theorem rotationExpr_cost {d : ℕ} (i j : Fin d) (p : Entries d) :
    (rotationExpr i j p).cost ≤ 5 := by
  unfold rotationExpr
  split_ifs <;> norm_num [Expr.cost]

theorem rotationCircuit_cost {d : ℕ} (i j : Fin d) :
    (rotationCircuit i j).cost ≤ 6*d^2 := by
  calc
    _ ≤ ∑ _p : Entries d, 6 := by
      apply Finset.sum_le_sum
      intro p _
      have h := rotationExpr_cost i j p
      change (rotationExpr i j p).cost + 1 ≤ 6
      omega
    _ = _ := by simp [Entries]; ring

def coefficientInput {d : ℕ} (A : Mat d) (i j : Fin d) : Jacobi.Registers → ℝ :=
  fun r => if r = 0 then A i i else if r = 1 then A i j else if r = 2 then A j j else 0

def rotation {d : ℕ} (A : Mat d) (i j : Fin d) : Counted (Mat d) :=
  let v := coefficientInput A i j
  let w := Jacobi.program.run v
  ⟨fun k l => (rotationCircuit i j).eval w (k,l),
    10 + Jacobi.program.cost v + (rotationCircuit i j).cost + 8*d^2 + 1⟩

theorem rotation_value {d : ℕ} (A : Mat d) (i j : Fin d) :
    (rotation A i j).value = KSJacobiStep.rotation A i j := by
  ext k l
  dsimp [rotation]
  rw [rotationCircuit_eval]
  have hc := Jacobi.program_outputs (coefficientInput A i j)
  norm_num [coefficientInput] at hc
  rw [hc.1, hc.2]
  rfl

theorem rotation_cost {d : ℕ} (A : Mat d) (i j : Fin d) :
    (rotation A i j).cost ≤ 311 + 14*d^2 := by
  have hp := (Jacobi.program.cost_le_bound (coefficientInput A i j)).trans Jacobi.program_bound
  have hr := rotationCircuit_cost i j
  dsimp [rotation]
  omega

/-- Primitive executions of every scalar output of the actual rotation. -/
theorem rotation_primitive_execution {d : ℕ} (A : Mat d) (i j : Fin d) :
    ∃ w : Jacobi.Registers → ℝ, ∃ k ≤ 300,
      Program.Executes Jacobi.program (coefficientInput A i j) w k ∧
      ∀ p : Entries d,
        Expr.Executes w ((rotationCircuit i j).output p)
          ((rotation A i j).value p.1 p.2) ((rotationCircuit i j).output p).cost := by
  refine ⟨Jacobi.program.run _, Jacobi.program.cost _,
    (Jacobi.program.cost_le_bound _).trans Jacobi.program_bound,
    Program.executes_of_safe _ _ (Jacobi.program_safe _), ?_⟩
  intro p
  exact Expr.executes_of_valid _ _ (rotationCircuit_valid i j _ p)

def identity (d : ℕ) : Counted (Mat d) :=
  ⟨fun i j => if i = j then 1 else 0, 3*d^2+1⟩

theorem identity_value (d : ℕ) : (identity d).value = (1 : Mat d) := by
  ext i j
  simp [identity, Matrix.one_apply]

def selectedRotation {d : ℕ} (A : Mat d) : Counted (Mat d) :=
  let p := pivot A
  let r := match p.value with | none => identity d | some q => rotation A q.1 q.2
  ⟨r.value, p.cost + r.cost + 1⟩

theorem selectedRotation_value {d : ℕ} (A : Mat d) :
    (selectedRotation A).value = KSJacobiIteration.selectedRotation A := by
  dsimp only [selectedRotation]
  rw [pivot_value]
  cases hp : KSJacobiIteration.pivot A with
  | none => simpa [KSJacobiIteration.selectedRotation, hp] using identity_value d
  | some p => simpa [KSJacobiIteration.selectedRotation, hp] using rotation_value A p.1 p.2

theorem selectedRotation_cost {d : ℕ} (A : Mat d) :
    (selectedRotation A).cost ≤ 400*(d+1)^2 := by
  have hp := pivot_cost A
  have hd2 : d^2 ≤ (d+1)^2 := Nat.pow_le_pow_left (by omega) 2
  have hb : 1 ≤ (d+1)^2 := Nat.one_le_pow 2 _ (by omega)
  dsimp only [selectedRotation]
  cases he : (pivot A).value with
  | none => dsimp [identity]; omega
  | some p =>
    have hr := rotation_cost A p.1 p.2
    change (pivot A).cost + (rotation A p.1 p.2).cost + 1 ≤ _
    omega

/-- Direct matrix multiplication by the previously proved scalar dot circuits.
The extra term counts finite output addressing and loop control. -/
def multiply {d : ℕ} (A B : Mat d) : Counted (Mat d) :=
  ⟨fun i j => (matrixMulCircuit d d d).eval (matrixInput A B) (i,j),
    (matrixMulCircuit d d d).cost + 4*d^2 + 1⟩

theorem multiply_value {d : ℕ} (A B : Mat d) : (multiply A B).value = A*B := by
  ext i j
  exact matrixMulCircuit_eval A B i j

theorem multiply_cost {d : ℕ} (A B : Mat d) :
    (multiply A B).cost = 4*d^3 + 6*d^2 + 1 := by
  simp [multiply, matrixMulCircuit_cost]
  ring

theorem multiply_primitive_execution {d : ℕ} (A B : Mat d) (i j : Fin d) :
    Expr.Executes (matrixInput A B) ((matrixMulCircuit d d d).output (i,j))
      ((multiply A B).value i j) (4*d+1) := by
  rw [multiply_value]
  exact matrixMulCircuit_entry_executes A B i j

structure State (d : ℕ) where
  matrix : Mat d
  basis : Mat d

/-- Three actual primitive matrix products per round, retaining the basis.
The transpose is copied by index permutation, charged per entry. -/
def round {d : ℕ} (s : State d) : Counted (State d) :=
  let r := selectedRotation s.matrix
  let left := multiply r.valueᵀ s.matrix
  let next := multiply left.value r.value
  let basis := multiply s.basis r.value
  ⟨⟨next.value, basis.value⟩,
    r.cost + left.cost + next.cost + basis.cost + 3*d^2 + 1⟩

theorem round_matrix {d : ℕ} (s : State d) :
    (round s).value.matrix = KSJacobiIteration.advance s.matrix := by
  simp [round, multiply_value, selectedRotation_value, KSJacobiIteration.advance]

theorem round_basis {d : ℕ} (s : State d) :
    (round s).value.basis = s.basis * KSJacobiIteration.selectedRotation s.matrix := by
  simp [round, multiply_value, selectedRotation_value]

theorem round_cost {d : ℕ} (s : State d) : (round s).cost ≤ 500*(d+1)^3 := by
  have hr := selectedRotation_cost s.matrix
  simp only [round, multiply_cost]
  nlinarith [Nat.zero_le d, sq_nonneg (d : ℤ)]

def iterate {d : ℕ} (s : State d) : ℕ → Counted (State d)
  | 0 => ⟨s, 1⟩
  | n+1 =>
    let previous := iterate s n
    let next := round previous.value
    ⟨next.value, previous.cost + next.cost + 1⟩

theorem iterate_cost {d : ℕ} (s : State d) (n : ℕ) :
    (iterate s n).cost ≤ n*(500*(d+1)^3+1)+1 := by
  induction n with
  | zero => simp [iterate]
  | succ n ih =>
    have hr := round_cost (iterate s n).value
    simp only [iterate]
    nlinarith

def diagonalize {d : ℕ} (A : Mat d) (n : ℕ) : Counted (State d) :=
  let initial := identity d
  let result := iterate ⟨A, initial.value⟩ n
  ⟨result.value, initial.cost + result.cost + 1⟩

theorem iterate_actual {d : ℕ} (A : Mat d) (n : ℕ) :
    (iterate ⟨A, 1⟩ n).value.matrix = KSJacobiIteration.run A n ∧
    (iterate ⟨A, 1⟩ n).value.basis = KSJacobiIteration.accumulatedBasis A n := by
  induction n with
  | zero => exact ⟨rfl,rfl⟩
  | succ n ih =>
    simp only [iterate, KSJacobiIteration.run, KSJacobiIteration.accumulatedBasis]
    rw [round_matrix, round_basis, ih.1, ih.2]
    exact ⟨rfl,rfl⟩

/-- Equality to the literal previously verified matrix and basis recurrences. -/
theorem diagonalize_actual {d : ℕ} (A : Mat d) (n : ℕ) :
    (diagonalize A n).value.matrix = KSJacobiIteration.run A n ∧
    (diagonalize A n).value.basis = KSJacobiIteration.accumulatedBasis A n := by
  simpa only [diagonalize, identity_value] using iterate_actual A n

/-- Polynomial primitive arithmetic/comparison/address work in dimension and
the supplied number of rounds, without a spectral or optimizer primitive. -/
theorem diagonalize_cost {d : ℕ} (A : Mat d) (n : ℕ) :
    (diagonalize A n).cost ≤ 510*(n+1)*(d+1)^3 := by
  have hi := iterate_cost (⟨A, (identity d).value⟩ : State d) n
  dsimp only [identity] at hi
  dsimp [diagonalize, identity]
  have hd : d^2 ≤ (d+1)^3 := by
    nlinarith [Nat.zero_le (d^3), Nat.zero_le (d^2)]
  have hb : 1 ≤ (d+1)^3 := Nat.one_le_pow 3 _ (by omega)
  calc
    _ ≤ 3*d^2 + 1 + (n*(500*(d+1)^3+1)+1) + 1 := by omega
    _ ≤ 3*(d+1)^3 + (d+1)^3 + (n*(501*(d+1)^3)+(d+1)^3) + (d+1)^3 := by
      have hn := Nat.mul_le_mul_left n (show 500*(d+1)^3+1 ≤ 501*(d+1)^3 by omega)
      omega
    _ = (501*n+6)*(d+1)^3 := by ring
    _ ≤ 510*(n+1)*(d+1)^3 := Nat.mul_le_mul_right _ (by omega)

/-- The original finite Rayleigh routine receives these exact outputs when
the supplied budget is its existing `iterationCount`. Budget computation is
not hidden inside the operation bound. -/
theorem diagonalize_rayleigh_outputs {d : ℕ} (A : Mat d) (τ : ℝ) :
    (diagonalize A (KSJacobiIteration.iterationCount A τ)).value.matrix =
      KSJacobiRayleigh.finalMatrix A τ ∧
    (diagonalize A (KSJacobiIteration.iterationCount A τ)).value.basis =
      KSJacobiRayleigh.finalBasis A τ :=
  diagonalize_actual A _

end MatrixSpencer.RealRAM.JacobiIteration
