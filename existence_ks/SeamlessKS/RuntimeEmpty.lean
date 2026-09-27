import SeamlessKS.Input
import MatrixSpencer.RealRAMProgram

/-! The zero-dimensional endpoint is an explicit original-label all-ones
array. Its program writes one rational constant per label; it uses no
SDP query or random draw. The index list is the literal `List.finRange N`. -/
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace SeamlessKS.RuntimeEmpty
open MatrixSpencer MatrixSpencer.RealRAM
variable {N : ℕ}

def writeOnes : List (Fin N) → Program (Fin N)
  | [] => .skip
  | i :: is => .seq (.assign i (.constant 1)) (writeOnes is)

def program (N : ℕ) : Program (Fin N) := writeOnes (List.finRange N)

def input (N : ℕ) : Fin N → ℝ := fun _ => 0

def output (N : ℕ) : Fin N → ℝ := fun _ => 1

theorem writeOnes_value (is : List (Fin N)) (q : Fin N → ℝ) (j : Fin N) :
    (writeOnes is).run q j = if j ∈ is then 1 else q j := by
  induction is generalizing q with
  | nil => simp [writeOnes,Program.run]
  | cons i is ih =>
    simp only [writeOnes,Program.run,Expr.eval,ih,List.mem_cons]
    by_cases h : j = i
    · subst j
      simp
    · simp [h]

theorem program_value (N : ℕ) : (program N).run (input N) = output N := by
  funext i
  simp [program,writeOnes_value,output]

theorem writeOnes_safe (is : List (Fin N)) (q : Fin N → ℝ) :
    (writeOnes is).Safe q := by
  induction is generalizing q with
  | nil => trivial
  | cons i is ih => exact ⟨trivial,ih _⟩

theorem writeOnes_cost (is : List (Fin N)) (q : Fin N → ℝ) :
    (writeOnes is).cost q = 2 * is.length := by
  induction is generalizing q with
  | nil => rfl
  | cons i is ih => simp [writeOnes,Program.cost,Expr.cost,ih]; omega

/-- Every scalar write, including its constant load, appears in the execution. -/
theorem execution (N : ℕ) :
    Program.Executes (program N) (input N) (output N) (2*N) := by
  have h := Program.executes_of_safe (program N) (input N) (writeOnes_safe _ _)
  rw [program_value] at h
  simpa only [program,writeOnes_cost,List.length_finRange] using h

/-- Two scalar primitives per output and a linear allowance for generating
and traversing the explicit label list. -/
def costBound (N : ℕ) : ℕ := 4*N+1

theorem execution_bounded (N : ℕ) :
    ∃ k ≤ costBound N, Program.Executes (program N) (input N) (output N) k :=
  ⟨2*N,by dsimp [costBound]; omega,execution N⟩

theorem output_sound (v : Fin N → Fin 0 → ℂ) {ε : ℝ} (_hε : 0≤ε) :
    (∀ i,IsSign (output N i)) ∧
      ‖∑ i,output N i • KSRankOne.atom (v i)‖≤400*Real.sqrt ε := by
  constructor
  · intro i
    exact Or.inl rfl
  · have h : (∑ i,output N i • KSRankOne.atom (v i)) =
        (0 : Matrix (Fin 0) (Fin 0) ℂ) := Subsingleton.elim _ _
    rw [h,norm_zero]
    positivity

/-- Complete deterministic dimension-zero guarantee; it has no positivity,
Parseval, solver, or random-sampling premise. -/
theorem guarantee (v : Fin N → Fin 0 → ℂ) {ε : ℝ} (hε : 0≤ε) :
    (∀ i,IsSign (output N i)) ∧
      ‖∑ i,output N i • KSRankOne.atom (v i)‖≤400*Real.sqrt ε ∧
      ∃ k ≤ costBound N, Program.Executes (program N) (input N) (output N) k :=
  ⟨(output_sound v hε).1,(output_sound v hε).2,execution_bounded N⟩

end SeamlessKS.RuntimeEmpty
