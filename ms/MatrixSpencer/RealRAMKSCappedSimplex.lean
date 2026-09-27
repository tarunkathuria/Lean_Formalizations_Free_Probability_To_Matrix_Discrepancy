import MatrixSpencer.RealRAMJacobiIteration
import MatrixSpencer.KSEighthManuscriptMatrixProjection

/-!
# Counted finite capped-simplex projection and Jacobi conjugation

The scalar algorithm reproduces the existing ordered breakpoint/candidate
list and the first exact-mass threshold, including its zero fallback. Every
nonlinear scalar operation is a primitive real comparison or guarded division.
Clipping, absolute value, and cell classification execute explicit `Program`s.
Finite sums, list scans, address control and output stores are counted directly.

The matrix report composes the counted Jacobi implementation and two dense
scalar multiplication circuits. The supplied natural Jacobi budget is kept
explicit; its calculation from a real tolerance is a separate operation.
-/

open Matrix
open scoped BigOperators
noncomputable section
namespace MatrixSpencer.RealRAM.KSCappedSimplex
open JacobiIteration (Counted Mat)

abbrev Reg := Fin 2

def clipProgram : Program Reg :=
  .branchLE (.input 0) (.constant 0) (.assign 1 (.constant 0))
    (.branchLE (.constant 1) (.input 0) (.assign 1 (.constant 1)) (.assign 1 (.input 0)))

def absProgram : Program Reg :=
  .branchLE (.constant 0) (.input 0) (.assign 1 (.input 0))
    (.assign 1 (.sub (.constant 0) (.input 0)))

def unaryInput (x : ℝ) : Reg → ℝ := fun r => if r = 0 then x else 0

theorem clipProgram_safe (v : Reg → ℝ) : clipProgram.Safe v := by
  simp [clipProgram, Program.Safe, Expr.Valid]

theorem absProgram_safe (v : Reg → ℝ) : absProgram.Safe v := by
  simp [absProgram, Program.Safe, Expr.Valid]

theorem clipProgram_output (v : Reg → ℝ) :
    clipProgram.run v 1 = KSEighthManuscriptCappedSimplex.clip (v 0) := by
  by_cases h0 : v 0 ≤ 0
  · simp [clipProgram, Program.run, Expr.eval, h0,
      KSEighthManuscriptCappedSimplex.clip_of_nonpos h0]
  · by_cases h1 : 1 ≤ v 0
    · simp [clipProgram, Program.run, Expr.eval, h0, h1,
        KSEighthManuscriptCappedSimplex.clip_of_one_le h1]
    · simp [clipProgram, Program.run, Expr.eval, h0, h1,
        KSEighthManuscriptCappedSimplex.clip_of_mem (le_of_not_ge h0) (le_of_not_ge h1)]

theorem absProgram_output (v : Reg → ℝ) : absProgram.run v 1 = |v 0| := by
  by_cases h : 0 ≤ v 0
  · simp [absProgram, Program.run, Expr.eval, h, abs_of_nonneg h]
  · simp [absProgram, Program.run, Expr.eval, h, abs_of_neg (lt_of_not_ge h)]

theorem unary_program_bounds : clipProgram.bound ≤ 10 ∧ absProgram.bound ≤ 10 := by decide

def clipped (x : ℝ) : Counted ℝ :=
  ⟨clipProgram.run (unaryInput x) 1, clipProgram.cost (unaryInput x) + 4⟩

def absolute (x : ℝ) : Counted ℝ :=
  ⟨absProgram.run (unaryInput x) 1, absProgram.cost (unaryInput x) + 4⟩

theorem clipped_value (x : ℝ) : (clipped x).value = KSEighthManuscriptCappedSimplex.clip x := by
  simpa [clipped, unaryInput] using clipProgram_output (unaryInput x)

theorem absolute_value (x : ℝ) : (absolute x).value = |x| := by
  simpa [absolute, unaryInput] using absProgram_output (unaryInput x)

theorem clipped_cost (x : ℝ) : (clipped x).cost ≤ 14 := by
  exact Nat.add_le_add_right ((clipProgram.cost_le_bound _).trans unary_program_bounds.1) 4

theorem absolute_cost (x : ℝ) : (absolute x).cost ≤ 14 := by
  exact Nat.add_le_add_right ((absProgram.cost_le_bound _).trans unary_program_bounds.2) 4

theorem clipped_primitive_execution (x : ℝ) :
    Program.Executes clipProgram (unaryInput x) (clipProgram.run (unaryInput x))
      (clipProgram.cost (unaryInput x)) :=
  Program.executes_of_safe _ _ (clipProgram_safe _)

theorem absolute_primitive_execution (x : ℝ) :
    Program.Executes absProgram (unaryInput x) (absProgram.run (unaryInput x))
      (absProgram.cost (unaryInput x)) :=
  Program.executes_of_safe _ _ (absProgram_safe _)

abbrev CellReg := Fin 5
def zeroMiddle : Program CellReg :=
  .seq (.assign 3 (.constant 0)) (.assign 4 (.constant 0))
def nonzeroMiddle : Program CellReg :=
  .seq (.assign 3 (.constant 1)) (.assign 4 (.input 0))
def cellProgram : Program CellReg :=
  .seq
    (.branchLE (.input 0) (.add (.input 1) (.constant 1))
      (.assign 2 (.constant 0)) (.assign 2 (.constant 1)))
    (.branchLE (.input 0) (.input 1) zeroMiddle
      (.branchLE (.input 0) (.add (.input 1) (.constant 1)) nonzeroMiddle zeroMiddle))

theorem cellProgram_safe (v : CellReg → ℝ) : cellProgram.Safe v := by
  simp [cellProgram, zeroMiddle, nonzeroMiddle, Program.Safe, Expr.Valid]

theorem cellProgram_bound : cellProgram.bound ≤ 40 := by decide

theorem cellProgram_outputs (v : CellReg → ℝ) :
    cellProgram.run v 2 = (if v 1 + 1 < v 0 then 1 else 0) ∧
    cellProgram.run v 3 = (if v 1 < v 0 ∧ v 0 ≤ v 1 + 1 then 1 else 0) ∧
    cellProgram.run v 4 = (if v 1 < v 0 ∧ v 0 ≤ v 1 + 1 then v 0 else 0) := by
  by_cases hlow : v 0 ≤ v 1 <;> by_cases hhigh : v 0 ≤ v 1 + 1 <;>
    simp [cellProgram, zeroMiddle, nonzeroMiddle, Program.run, Expr.eval,
      hlow, hhigh, not_lt.mpr, lt_of_not_ge]

structure Stats where
  high : ℝ
  middle : ℝ
  total : ℝ

def cellInput (x b : ℝ) : CellReg → ℝ :=
  fun r => if r = 0 then x else if r = 1 then b else 0

def cell (x b : ℝ) : Counted Stats :=
  let v := cellInput x b
  let w := cellProgram.run v
  ⟨⟨w 2,w 3,w 4⟩, cellProgram.cost v + 10⟩

theorem cell_values (x b : ℝ) :
    (cell x b).value.high = (if b+1 < x then 1 else 0) ∧
    (cell x b).value.middle = (if b < x ∧ x ≤ b+1 then 1 else 0) ∧
    (cell x b).value.total = (if b < x ∧ x ≤ b+1 then x else 0) := by
  simpa [cell, cellInput] using cellProgram_outputs (cellInput x b)

theorem cell_cost (x b : ℝ) : (cell x b).cost ≤ 50 :=
  Nat.add_le_add_right ((cellProgram.cost_le_bound _).trans cellProgram_bound) 10

theorem cell_primitive_execution (x b : ℝ) :
    Program.Executes cellProgram (cellInput x b) (cellProgram.run (cellInput x b))
      (cellProgram.cost (cellInput x b)) :=
  Program.executes_of_safe _ _ (cellProgram_safe _)

def sumCells {d : ℕ} (z : Fin d → ℝ) (b : ℝ) : List (Fin d) → Counted Stats
  | [] => ⟨⟨0,0,0⟩, 7⟩
  | i :: is =>
    let t := sumCells z b is
    let a := cell (z i) b
    ⟨⟨a.value.high+t.value.high, a.value.middle+t.value.middle, a.value.total+t.value.total⟩,
      a.cost+t.cost+15⟩

theorem sumCells_values {d : ℕ} (z : Fin d → ℝ) (b : ℝ) (is : List (Fin d)) :
    (sumCells z b is).value.high = (is.map (fun i => if b+1 < z i then (1:ℝ) else 0)).sum ∧
    (sumCells z b is).value.middle =
      (is.map (fun i => if b < z i ∧ z i ≤ b+1 then (1:ℝ) else 0)).sum ∧
    (sumCells z b is).value.total =
      (is.map (fun i => if b < z i ∧ z i ≤ b+1 then z i else 0)).sum := by
  induction is with
  | nil => simp [sumCells]
  | cons i is ih =>
    have hc := cell_values (z i) b
    simp [sumCells, hc.1, hc.2.1, hc.2.2, ih.1, ih.2.1, ih.2.2]

theorem sumCells_cost {d : ℕ} (z : Fin d → ℝ) (b : ℝ) (is : List (Fin d)) :
    (sumCells z b is).cost ≤ 65*is.length+7 := by
  induction is with
  | nil => simp [sumCells]
  | cons i is ih =>
    have h := cell_cost (z i) b
    simp only [sumCells, List.length_cons]
    omega

def stats {d : ℕ} (z : Fin d → ℝ) (b : ℝ) : Counted Stats :=
  let r := sumCells z b (List.finRange d)
  ⟨r.value,r.cost+2*d+1⟩

theorem stats_values {d : ℕ} (z : Fin d → ℝ) (b : ℝ) :
    (stats z b).value.high = KSEighthManuscriptCappedSimplex.highCount z b ∧
    (stats z b).value.middle = KSEighthManuscriptCappedSimplex.middleCount z b ∧
    (stats z b).value.total = KSEighthManuscriptCappedSimplex.middleSum z b := by
  simpa [stats, ← List.ofFn_eq_map, List.sum_ofFn, KSEighthManuscriptCappedSimplex.highCount,
    KSEighthManuscriptCappedSimplex.middleCount, KSEighthManuscriptCappedSimplex.middleSum,
    KSEighthManuscriptCappedSimplex.middle] using sumCells_values z b (List.finRange d)

theorem stats_cost {d : ℕ} (z : Fin d → ℝ) (b : ℝ) : (stats z b).cost ≤ 67*d+8 := by
  have h := sumCells_cost z b (List.finRange d)
  dsimp [stats]
  simp only [List.length_finRange] at h
  omega

def quotientExpr : Expr (Fin 4) :=
  .div (.sub (.add (.input 2) (.input 0)) (.input 3)) (.input 1)
def quotientInput (a : Stats) (s : ℝ) : Fin 4 → ℝ :=
  fun r => if r=0 then a.high else if r=1 then a.middle else if r=2 then a.total else s

theorem quotientExpr_eval (a : Stats) (s : ℝ) :
    quotientExpr.eval (quotientInput a s) = (a.total+a.high-s)/a.middle := by
  norm_num [quotientExpr, Expr.eval, quotientInput, Fin.ext_iff]

theorem quotientExpr_executes (a : Stats) (s : ℝ) (ha : a.middle ≠ 0) :
    Expr.Executes (quotientInput a s) quotientExpr ((a.total+a.high-s)/a.middle) 7 := by
  have hv : quotientExpr.Valid (quotientInput a s) := by
    simpa [quotientExpr, Expr.Valid, Expr.eval, quotientInput] using ha
  simpa [quotientExpr_eval, quotientExpr, Expr.cost] using Expr.executes_of_valid _ _ hv

def affine {d : ℕ} (z : Fin d → ℝ) (s b : ℝ) : Counted ℝ :=
  let a := stats z b
  ⟨if a.value.middle = 0 then b else quotientExpr.eval (quotientInput a.value s), a.cost+20⟩

theorem affine_value {d : ℕ} (z : Fin d → ℝ) (s b : ℝ) :
    (affine z s b).value = KSEighthManuscriptCappedSimplex.affineCandidate z s b := by
  have h := stats_values z b
  simp [affine, quotientExpr_eval, h.1, h.2.1, h.2.2,
    KSEighthManuscriptCappedSimplex.affineCandidate]

theorem affine_cost {d : ℕ} (z : Fin d → ℝ) (s b : ℝ) : (affine z s b).cost ≤ 67*d+28 :=
  Nat.add_le_add_right (stats_cost z b) 20

/-- The actual branch either copies its breakpoint or executes the seven-step
quotient with a proved nonzero divisor. There is no numerical premise. -/
theorem affine_guarded_execution {d : ℕ} (z : Fin d → ℝ) (s b : ℝ) :
    ((stats z b).value.middle = 0 ∧ (affine z s b).value = b) ∨
    Expr.Executes (quotientInput (stats z b).value s) quotientExpr (affine z s b).value 7 := by
  by_cases h : (stats z b).value.middle = 0
  · exact Or.inl ⟨h, by simp [affine, h]⟩
  · apply Or.inr
    simpa only [affine, h, ↓reduceIte, quotientExpr_eval] using
      quotientExpr_executes (stats z b).value s h

def sumAbs {d : ℕ} (z : Fin d → ℝ) : List (Fin d) → Counted ℝ
  | [] => ⟨0, 2⟩
  | i :: is =>
    let t := sumAbs z is
    let a := absolute (z i)
    ⟨a.value+t.value, a.cost+t.cost+6⟩

theorem sumAbs_value {d : ℕ} (z : Fin d → ℝ) (is : List (Fin d)) :
    (sumAbs z is).value = (is.map (fun i => |z i|)).sum := by
  induction is with
  | nil => rfl
  | cons i is ih => simp [sumAbs, absolute_value, ih]

theorem sumAbs_cost {d : ℕ} (z : Fin d → ℝ) (is : List (Fin d)) :
    (sumAbs z is).cost ≤ 20*is.length+2 := by
  induction is with
  | nil => simp [sumAbs]
  | cons i is ih =>
    have h := absolute_cost (z i)
    simp only [sumAbs, List.length_cons]
    omega

def radius {d : ℕ} (z : Fin d → ℝ) : Counted ℝ :=
  let a := sumAbs z (List.finRange d)
  ⟨1+a.value,a.cost+2*d+5⟩

theorem radius_value {d : ℕ} (z : Fin d → ℝ) :
    (radius z).value = KSEighthManuscriptCappedSimplex.radius z := by
  simp [radius, sumAbs_value, ← List.ofFn_eq_map, List.sum_ofFn,
    KSEighthManuscriptCappedSimplex.radius]

theorem radius_cost {d : ℕ} (z : Fin d → ℝ) : (radius z).cost ≤ 22*d+7 := by
  have h := sumAbs_cost z (List.finRange d)
  dsimp [radius]
  simp only [List.length_finRange] at h
  omega

def coordinateBreaks {d : ℕ} (z : Fin d → ℝ) : List (Fin d) → Counted (List ℝ)
  | [] => ⟨[],1⟩
  | i::is =>
    let t := coordinateBreaks z is
    ⟨z i :: (z i-1) :: t.value,t.cost+10⟩

theorem coordinateBreaks_value {d : ℕ} (z : Fin d → ℝ) (is : List (Fin d)) :
    (coordinateBreaks z is).value = is.flatMap (fun i => [z i,z i-1]) := by
  induction is with
  | nil => rfl
  | cons i is ih => simp [coordinateBreaks, ih]

theorem coordinateBreaks_cost {d : ℕ} (z : Fin d → ℝ) (is : List (Fin d)) :
    (coordinateBreaks z is).cost = 10*is.length+1 := by
  induction is with
  | nil => rfl
  | cons i is ih => simp [coordinateBreaks, ih]; omega

def breaks {d : ℕ} (z : Fin d → ℝ) : Counted (List ℝ) :=
  let r := radius z
  let bs := coordinateBreaks z (List.finRange d)
  ⟨-r.value :: bs.value,r.cost+bs.cost+2*d+5⟩

theorem breaks_value {d : ℕ} (z : Fin d → ℝ) :
    (breaks z).value = KSEighthManuscriptCappedSimplex.breaks z := by
  simp [breaks, radius_value, coordinateBreaks_value, KSEighthManuscriptCappedSimplex.breaks]

theorem breaks_length {d : ℕ} (z : Fin d → ℝ) : (breaks z).value.length = 2*d+1 := by
  rw [breaks_value]
  simp [KSEighthManuscriptCappedSimplex.breaks, List.length_flatMap]
  omega

theorem breaks_cost {d : ℕ} (z : Fin d → ℝ) : (breaks z).cost ≤ 34*d+13 := by
  have h := radius_cost z
  simp only [breaks, coordinateBreaks_cost, List.length_finRange]
  omega

def buildCandidates {d : ℕ} (z : Fin d → ℝ) (s : ℝ) : List ℝ → Counted (List ℝ)
  | [] => ⟨[],1⟩
  | b::bs =>
    let a := affine z s b
    let t := buildCandidates z s bs
    ⟨b :: a.value :: t.value,a.cost+t.cost+6⟩

theorem buildCandidates_value {d : ℕ} (z : Fin d → ℝ) (s : ℝ) (bs : List ℝ) :
    (buildCandidates z s bs).value =
      bs.flatMap (fun b => [b,KSEighthManuscriptCappedSimplex.affineCandidate z s b]) := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [buildCandidates, affine_value, ih]

theorem buildCandidates_cost {d : ℕ} (z : Fin d → ℝ) (s : ℝ) (bs : List ℝ) :
    (buildCandidates z s bs).cost ≤ bs.length*(67*d+34)+1 := by
  induction bs with
  | nil => simp [buildCandidates]
  | cons b bs ih =>
    have h := affine_cost z s b
    simp only [buildCandidates, List.length_cons]
    nlinarith

def candidates {d : ℕ} (z : Fin d → ℝ) (s : ℝ) : Counted (List ℝ) :=
  let bs := breaks z
  let cs := buildCandidates z s bs.value
  ⟨cs.value,bs.cost+cs.cost+1⟩

theorem candidates_value {d : ℕ} (z : Fin d → ℝ) (s : ℝ) :
    (candidates z s).value = KSEighthManuscriptCappedSimplex.candidates z s := by
  simp [candidates, buildCandidates_value, breaks_value, KSEighthManuscriptCappedSimplex.candidates]

theorem candidates_length {d : ℕ} (z : Fin d → ℝ) (s : ℝ) :
    (candidates z s).value.length = 4*d+2 := by
  rw [candidates_value]
  exact KSEighthManuscriptCappedSimplex.candidates_length z s

theorem candidates_cost {d : ℕ} (z : Fin d → ℝ) (s : ℝ) :
    (candidates z s).cost ≤ 300*(d+1)^2 := by
  have hb := breaks_cost z
  have hc := buildCandidates_cost z s (breaks z).value
  rw [breaks_length] at hc
  dsimp [candidates]
  nlinarith

def sumMass {d : ℕ} (z : Fin d → ℝ) (x : ℝ) : List (Fin d) → Counted ℝ
  | [] => ⟨0,2⟩
  | i::is =>
    let a := clipped (z i-x)
    let t := sumMass z x is
    ⟨a.value+t.value,a.cost+t.cost+10⟩

theorem sumMass_value {d : ℕ} (z : Fin d → ℝ) (x : ℝ) (is : List (Fin d)) :
    (sumMass z x is).value =
      (is.map (fun i => KSEighthManuscriptCappedSimplex.clip (z i-x))).sum := by
  induction is with
  | nil => rfl
  | cons i is ih => simp [sumMass, clipped_value, ih]

theorem sumMass_cost {d : ℕ} (z : Fin d → ℝ) (x : ℝ) (is : List (Fin d)) :
    (sumMass z x is).cost ≤ 24*is.length+2 := by
  induction is with
  | nil => simp [sumMass]
  | cons i is ih =>
    have h := clipped_cost (z i-x)
    simp only [sumMass, List.length_cons]
    omega

def mass {d : ℕ} (z : Fin d → ℝ) (x : ℝ) : Counted ℝ :=
  let a := sumMass z x (List.finRange d)
  ⟨a.value,a.cost+2*d+1⟩

theorem mass_value {d : ℕ} (z : Fin d → ℝ) (x : ℝ) :
    (mass z x).value = KSEighthManuscriptCappedSimplex.mass z x := by
  simp [mass, sumMass_value, ← List.ofFn_eq_map, List.sum_ofFn,
    KSEighthManuscriptCappedSimplex.mass]

theorem mass_cost {d : ℕ} (z : Fin d → ℝ) (x : ℝ) : (mass z x).cost ≤ 26*d+3 := by
  have h := sumMass_cost z x (List.finRange d)
  dsimp [mass]
  simp only [List.length_finRange] at h
  omega

/-- Equality is performed by the two opposite real comparisons. The first
matching candidate is retained, exactly as in the existing implementation. -/
def firstExact {d : ℕ} (z : Fin d → ℝ) (s : ℝ) : List ℝ → Counted ℝ
  | [] => ⟨0,2⟩
  | c::cs =>
    let a := mass z c
    if a.value ≤ s ∧ s ≤ a.value then ⟨c,a.cost+10⟩
    else let t := firstExact z s cs; ⟨t.value,a.cost+t.cost+10⟩

theorem firstExact_value {d : ℕ} (z : Fin d → ℝ) (s : ℝ) (cs : List ℝ) :
    (firstExact z s cs).value = KSEighthManuscriptCappedSimplex.firstExact z s cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp [firstExact, mass_value, ← le_antisymm_iff, KSEighthManuscriptCappedSimplex.firstExact, ih]
    split_ifs <;> rfl

theorem firstExact_cost {d : ℕ} (z : Fin d → ℝ) (s : ℝ) (cs : List ℝ) :
    (firstExact z s cs).cost ≤ cs.length*(26*d+13)+2 := by
  induction cs with
  | nil => simp [firstExact]
  | cons c cs ih =>
    have h := mass_cost z c
    dsimp only [firstExact]
    split_ifs <;> dsimp <;> nlinarith

def threshold {d : ℕ} (z : Fin d → ℝ) (s : ℝ) : Counted ℝ :=
  let cs := candidates z s
  let t := firstExact z s cs.value
  ⟨t.value,cs.cost+t.cost+1⟩

theorem threshold_value {d : ℕ} (z : Fin d → ℝ) (s : ℝ) :
    (threshold z s).value = KSEighthManuscriptCappedSimplex.threshold z s := by
  simp [threshold, firstExact_value, candidates_value, KSEighthManuscriptCappedSimplex.threshold]

theorem threshold_cost {d : ℕ} (z : Fin d → ℝ) (s : ℝ) :
    (threshold z s).cost ≤ 500*(d+1)^2 := by
  have hc := candidates_cost z s
  have ht := firstExact_cost z s (candidates z s).value
  rw [candidates_length] at ht
  dsimp [threshold]
  nlinarith

def project {d : ℕ} (z : Fin d → ℝ) (s : ℝ) : Counted (Fin d → ℝ) :=
  let t := threshold z s
  ⟨fun i => (clipped (z i-t.value)).value,
    t.cost + (∑ i, ((clipped (z i-t.value)).cost + 6)) + 2*d+1⟩

theorem project_value {d : ℕ} (z : Fin d → ℝ) (s : ℝ) :
    (project z s).value = KSEighthManuscriptCappedSimplex.project z s := by
  funext i
  simp [project, clipped_value, threshold_value, KSEighthManuscriptCappedSimplex.project]

theorem project_cost {d : ℕ} (z : Fin d → ℝ) (s : ℝ) :
    (project z s).cost ≤ 600*(d+1)^2 := by
  have ht := threshold_cost z s
  have hs : (∑ i, ((clipped (z i-(threshold z s).value)).cost+6)) ≤ 20*d := by
    calc
      _ ≤ ∑ _i : Fin d, 20 := by
        apply Finset.sum_le_sum
        intro i _
        have h := clipped_cost (z i-(threshold z s).value)
        omega
      _ = _ := by simp; omega
  dsimp [project]
  nlinarith

theorem project_coordinate_execution {d : ℕ} (z : Fin d → ℝ) (s : ℝ) (i : Fin d) :
    ∃ w : Reg → ℝ, ∃ k ≤ 10,
      Program.Executes clipProgram (unaryInput (z i-(threshold z s).value)) w k ∧
      w 1 = (project z s).value i := by
  let v := unaryInput (z i-(threshold z s).value)
  refine ⟨clipProgram.run v,clipProgram.cost v,
    (clipProgram.cost_le_bound v).trans unary_program_bounds.1,
    Program.executes_of_safe _ v (clipProgram_safe v),rfl⟩

def matrixReport {d : ℕ} (A : Mat d) (s : ℝ) (n : ℕ) : Counted (Mat d) :=
  let jac := JacobiIteration.diagonalize A n
  let p := project (fun i => jac.value.matrix i i) s
  let left := JacobiIteration.multiply jac.value.basis (Matrix.diagonal p.value)
  let result := JacobiIteration.multiply left.value jac.value.basisᵀ
  ⟨result.value,jac.cost+p.cost+left.cost+result.cost+6*d^2+3*d+3⟩

/-- The counted matrix report is the literal existing numerical output at its
specified Jacobi budget; no exact spectral projection is selected. -/
theorem matrixReport_value {d : ℕ} (A : Mat d) (s ν : ℝ) :
    (matrixReport A s (KSJacobiIteration.iterationCount A ν)).value =
      KSEighthManuscriptMatrixProjection.report A s ν := by
  have hj := JacobiIteration.diagonalize_rayleigh_outputs A ν
  simp [matrixReport, JacobiIteration.multiply_value, project_value, hj.1, hj.2,
    KSEighthManuscriptMatrixProjection.report, KSJacobiMatrixProjection.conjugate]

theorem matrixReport_cost {d : ℕ} (A : Mat d) (s : ℝ) (n : ℕ) :
    (matrixReport A s n).cost ≤ 1500*(n+1)*(d+1)^3 := by
  have hj := JacobiIteration.diagonalize_cost A n
  have hp := project_cost (fun i => (JacobiIteration.diagonalize A n).value.matrix i i) s
  simp only [matrixReport, JacobiIteration.multiply_cost]
  have h2 : (d+1)^2 ≤ (d+1)^3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hd2 : d^2 ≤ (d+1)^3 := (Nat.pow_le_pow_left (by omega) 2).trans h2
  have hd3 : d^3 ≤ (d+1)^3 := Nat.pow_le_pow_left (by omega) 3
  have hd : d ≤ (d+1)^3 := by
    have hd' := Nat.pow_le_pow_right (n:=d+1) (by omega) (show 1 ≤ 3 by omega)
    simp only [pow_one] at hd'
    exact (show d ≤ d+1 from by omega).trans hd'
  have h1 : 1 ≤ (d+1)^3 := Nat.one_le_pow 3 _ (by omega)
  have hscale := Nat.mul_le_mul_left ((d+1)^3) (show 1 ≤ n+1 by omega)
  nlinarith

/-- The computed report inherits the original unconditional spectral caps and
specified trace. Runtime uses the same value, rather than a surrogate output. -/
theorem matrixReport_feasible {d : ℕ} (A : Mat d) (s ν : ℝ)
    (h0 : 0 ≤ s) (hd : s ≤ d) :
    KSEighthManuscriptMatrixProjection.Feasible s
      (matrixReport A s (KSJacobiIteration.iterationCount A ν)).value := by
  rw [matrixReport_value]
  exact KSEighthManuscriptMatrixProjection.report_feasible A s h0 hd ν

theorem matrixReport_accuracy {d : ℕ} (A : Mat d) (hA : A.IsSymm)
    (s : ℝ) (h0 : 0 ≤ s) (hd : s ≤ d) {ν : ℝ} (hν : 0 < ν) :
    Real.sqrt (KSJacobiStep.frobeniusEnergy
      ((matrixReport A s (KSJacobiIteration.iterationCount A ν)).value -
        KSEighthManuscriptMatrixProjection.exactProjection A hA s h0 hd)) ≤ ν := by
  rw [matrixReport_value]
  exact KSEighthManuscriptMatrixProjection.report_accuracy A hA s h0 hd hν

end MatrixSpencer.RealRAM.KSCappedSimplex
