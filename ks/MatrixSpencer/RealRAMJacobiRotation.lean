import MatrixSpencer.RealRAMProgram
import MatrixSpencer.KSJacobiRotation

/-!
# A counted real-RAM implementation of the actual Jacobi scalar coefficients

Input registers 0,1,2 contain a,b,d. The program writes cosine and sine to
registers 3,4. Its zero-pivot test uses two real comparisons, and its nonzero
branch implements exactly `KSJacobiRotation.cosine` and `.sine`, with explicit
square-root and division safety. This is an executed program, not a unit-cost
call to the mathematical coefficient definitions.
-/

namespace MatrixSpencer.RealRAM.Jacobi

abbrev Registers := Fin 5

def aExpr : Expr Registers := .input 0
def bExpr : Expr Registers := .input 1
def dExpr : Expr Registers := .input 2
def gapExpr : Expr Registers := .sub dExpr aExpr
def square (e : Expr Registers) : Expr Registers := .mul e e
def shiftExpr : Expr Registers :=
  .div (.add gapExpr (.sqrt (.add (square gapExpr) (.mul (.constant 4) (square bExpr)))))
    (.constant 2)
def radiusExpr : Expr Registers := .sqrt (.add (square bExpr) (square shiftExpr))
def cosineExpr : Expr Registers := .div bExpr radiusExpr
def sineExpr : Expr Registers := .div (.sub (.constant 0) shiftExpr) radiusExpr

theorem shiftExpr_eval (v : Registers → ℝ) :
    shiftExpr.eval v = KSJacobiRotation.shift (v 0) (v 1) (v 2) := by
  simp [shiftExpr, gapExpr, square, aExpr, bExpr, dExpr, Expr.eval,
    KSJacobiRotation.shift, pow_two]

theorem radiusExpr_eval (v : Registers → ℝ) :
    radiusExpr.eval v = KSJacobiRotation.radius (v 0) (v 1) (v 2) := by
  simp [radiusExpr, square, bExpr, Expr.eval, shiftExpr_eval, KSJacobiRotation.radius, pow_two]

theorem shiftExpr_valid (v : Registers → ℝ) : shiftExpr.Valid v := by
  simp only [shiftExpr, gapExpr, square, aExpr, bExpr, dExpr, Expr.Valid, Expr.eval]
  refine ⟨⟨⟨trivial,trivial⟩,⟨⟨⟨⟨trivial,trivial⟩,⟨trivial,trivial⟩⟩,
    ⟨trivial,⟨trivial,trivial⟩⟩⟩,?_⟩⟩,trivial,by norm_num⟩
  norm_num at *
  nlinarith [sq_nonneg (v 2-v 0), sq_nonneg (v 1)]

theorem radiusExpr_valid (v : Registers → ℝ) : radiusExpr.Valid v := by
  refine ⟨⟨⟨trivial,trivial⟩,⟨shiftExpr_valid v,shiftExpr_valid v⟩⟩,?_⟩
  change 0 ≤ v 1*v 1 + shiftExpr.eval v*shiftExpr.eval v
  nlinarith [sq_nonneg (v 1), sq_nonneg (shiftExpr.eval v)]

theorem cosineExpr_valid (v : Registers → ℝ) (hb : v 1 ≠ 0) : cosineExpr.Valid v := by
  refine ⟨trivial,radiusExpr_valid v,?_⟩
  rw [radiusExpr_eval]
  exact (KSJacobiRotation.radius_pos _ _ _ hb).ne'

theorem sineExpr_valid (v : Registers → ℝ) (hb : v 1 ≠ 0) : sineExpr.Valid v := by
  refine ⟨⟨trivial,shiftExpr_valid v⟩,radiusExpr_valid v,?_⟩
  rw [radiusExpr_eval]
  exact (KSJacobiRotation.radius_pos _ _ _ hb).ne'

theorem cosineExpr_eval (v : Registers → ℝ) (hb : v 1 ≠ 0) :
    cosineExpr.eval v = KSJacobiRotation.cosine (v 0) (v 1) (v 2) := by
  simp [cosineExpr, bExpr, Expr.eval, radiusExpr_eval, KSJacobiRotation.cosine, hb]

theorem sineExpr_eval (v : Registers → ℝ) (hb : v 1 ≠ 0) :
    sineExpr.eval v = KSJacobiRotation.sine (v 0) (v 1) (v 2) := by
  simp [sineExpr, Expr.eval, shiftExpr_eval, radiusExpr_eval, KSJacobiRotation.sine, hb]

def zeroProgram : Program Registers :=
  .seq (.assign 3 (.constant 1)) (.assign 4 (.constant 0))

def nonzeroProgram : Program Registers :=
  .seq (.assign 3 cosineExpr) (.assign 4 sineExpr)

def program : Program Registers :=
  .branchLE bExpr (.constant 0)
    (.branchLE (.constant 0) bExpr zeroProgram nonzeroProgram) nonzeroProgram

theorem zeroProgram_safe (v : Registers → ℝ) : zeroProgram.Safe v := ⟨trivial,trivial⟩

theorem nonzeroProgram_safe (v : Registers → ℝ) (hb : v 1 ≠ 0) : nonzeroProgram.Safe v := by
  refine ⟨cosineExpr_valid v hb, sineExpr_valid _ ?_⟩
  simpa [Program.run] using hb

theorem program_safe (v : Registers → ℝ) : program.Safe v := by
  simp only [program, Program.Safe, bExpr, Expr.Valid, Expr.eval, Rat.cast_zero]
  refine ⟨trivial,trivial,?_⟩
  by_cases hb : v 1 ≤ 0
  · rw [if_pos hb]
    refine ⟨trivial,trivial,?_⟩
    by_cases hneg : 0 ≤ v 1
    · rw [if_pos hneg]
      exact zeroProgram_safe v
    · rw [if_neg hneg]
      exact nonzeroProgram_safe v (by intro h; simp [h] at hneg)
  · rw [if_neg hb]
    exact nonzeroProgram_safe v (by intro h; simp [h] at hb)

theorem zeroProgram_outputs (v : Registers → ℝ) :
    zeroProgram.run v 3 = 1 ∧ zeroProgram.run v 4 = 0 := by
  simp [zeroProgram, Program.run, Expr.eval]

theorem nonzeroProgram_outputs (v : Registers → ℝ) (hb : v 1 ≠ 0) :
    nonzeroProgram.run v 3 = KSJacobiRotation.cosine (v 0) (v 1) (v 2) ∧
    nonzeroProgram.run v 4 = KSJacobiRotation.sine (v 0) (v 1) (v 2) := by
  simp [nonzeroProgram, Program.run, cosineExpr_eval v hb, sineExpr, shiftExpr,
    radiusExpr, square, gapExpr, aExpr, bExpr, dExpr, Expr.eval,
    KSJacobiRotation.sine, KSJacobiRotation.radius, KSJacobiRotation.shift, hb, pow_two]

theorem program_outputs (v : Registers → ℝ) :
    program.run v 3 = KSJacobiRotation.cosine (v 0) (v 1) (v 2) ∧
    program.run v 4 = KSJacobiRotation.sine (v 0) (v 1) (v 2) := by
  by_cases hb : v 1 = 0
  · simpa [program, Program.run, bExpr, Expr.eval, hb, KSJacobiRotation.cosine,
      KSJacobiRotation.sine] using zeroProgram_outputs v
  · have hp := nonzeroProgram_outputs v hb
    by_cases hle : v 1 ≤ 0
    · have hn : ¬ 0 ≤ v 1 := by intro h; exact hb (le_antisymm hle h)
      simpa only [program, Program.run, bExpr, Expr.eval, Rat.cast_zero, if_pos hle,
        if_neg hn] using hp
    · simpa only [program, Program.run, bExpr, Expr.eval, Rat.cast_zero, if_neg hle] using hp

/-- A universal bound for this literal scalar program, including loads and branches. -/
theorem program_bound : program.bound ≤ 300 := by
  decide

theorem program_executes (v : Registers → ℝ) :
    ∃ w : Registers → ℝ, ∃ k ≤ 300, Program.Executes program v w k ∧
      w 3 = KSJacobiRotation.cosine (v 0) (v 1) (v 2) ∧
      w 4 = KSJacobiRotation.sine (v 0) (v 1) (v 2) := by
  refine ⟨program.run v, program.cost v,
    (Program.cost_le_bound program v).trans program_bound,
    Program.executes_of_safe program v (program_safe v), program_outputs v⟩

end MatrixSpencer.RealRAM.Jacobi
