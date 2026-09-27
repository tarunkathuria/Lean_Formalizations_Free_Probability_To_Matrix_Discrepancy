import MatrixSpencer.KSFullManuscriptPSDAlgebra
import Mathlib.Data.List.OfFn

/-!
# A concrete finite PSD test with a separating quadratic vector

The recursion performs scalar symmetric elimination. A positive first pivot
uses its Schur complement. A zero pivot scans the finite first row: a nonzero
off-diagonal entry supplies an explicit negative two-coordinate witness;
otherwise the zero row and column are removed. A negative pivot immediately
supplies its coordinate vector. No eigensystem or exact PSD oracle occurs in
the numerical definition. Complexity accounting is separate.
-/

open Matrix
open scoped BigOperators
noncomputable section
namespace MatrixSpencer.KSFullManuscriptPSDSeparation

open KSFullManuscriptPSDAlgebra
variable {n : ℕ}

def firstOffDiagonal (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) : Option (Fin n) :=
  (List.finRange n).find? (fun j => decide (A 0 j.succ ≠ 0))

theorem firstOffDiagonal_none (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hA : firstOffDiagonal A = none) : ∀ j : Fin n, A 0 j.succ = 0 := by
  simpa [firstOffDiagonal, List.find?_eq_none] using hA

theorem firstOffDiagonal_some (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    {j : Fin n} (hA : firstOffDiagonal A = some j) : A 0 j.succ ≠ 0 := by
  exact of_decide_eq_true ((List.find?_eq_some_iff_getElem.mp hA).1)

/-- The actual finite symmetric-elimination computation. The only divisions
are positive-pivot divisions and the explicitly positive zero-pivot witness
denominator. -/
def report : (n : ℕ) → Matrix (Fin n) (Fin n) ℝ → Option (Fin n → ℝ)
  | 0, _ => none
  | n + 1, A =>
    if A 0 0 < 0 then some (Pi.single 0 1)
    else if A 0 0 = 0 then
      match firstOffDiagonal A with
      | some j => some (zeroPivotWitness A j)
      | none => (report n (tail A)).map (Fin.cons 0)
    else (report n (schur A)).map (lift A)

private theorem psd_of_quadratic (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm)
    (hq : ∀ x, 0 ≤ quadratic A x) : A.PosSemidef := by
  constructor
  · ext i j
    simpa only [Matrix.conjTranspose_apply, star_trivial] using congrFun (congrFun hA i) j
  · intro x
    simpa only [star_trivial] using hq x

private theorem cons_decomposition (x : Fin (n + 1) → ℝ) :
    Fin.cons (x 0) (fun i : Fin n => x i.succ) = x := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

theorem report_correct : ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ), A.IsSymm →
    match report n A with
    | none => A.PosSemidef
    | some v => quadratic A v < 0 := by
  intro n
  induction n with
  | zero =>
    intro A hA
    apply psd_of_quadratic A hA
    intro x
    simp [quadratic, dotProduct]
  | succ n ih =>
    intro A hA
    by_cases hneg : A 0 0 < 0
    · simp only [report, if_pos hneg]
      simpa only [quadratic_single, one_pow, one_mul] using hneg
    · by_cases hzero : A 0 0 = 0
      · simp only [report, if_neg hneg, if_pos hzero]
        cases hrow : firstOffDiagonal A with
        | some j =>
          exact zeroPivotWitness_negative A hA hzero j (firstOffDiagonal_some A hrow)
        | none =>
          have htail := ih (tail A) (hA.submatrix Fin.succ)
          cases hrec : report n (tail A) with
          | none =>
            simp only [Option.map_none]
            simp only [hrec] at htail
            apply psd_of_quadratic A hA
            intro x
            have he := quadratic_cons A hA (x 0) (fun i => x i.succ)
            rw [cons_decomposition] at he
            have hrowzero : KSFullManuscriptPSDAlgebra.row A = 0 := by
              funext j
              exact firstOffDiagonal_none A hrow j
            rw [hzero, hrowzero] at he
            simp only [zero_mul, zero_dotProduct, mul_zero, zero_add] at he
            rw [he]
            simpa only [star_trivial] using htail.2 (fun i => x i.succ)
          | some v =>
            simp only [Option.map_some]
            simp only [hrec] at htail
            rw [quadratic_cons A hA]
            simpa only [zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul, zero_add] using htail
      · have hpos : 0 < A 0 0 := lt_of_le_of_ne (le_of_not_gt hneg) (Ne.symm hzero)
        simp only [report, if_neg hneg, if_neg hzero]
        have hschur := ih (schur A) (schur_isSymm A hA)
        cases hrec : report n (schur A) with
        | none =>
          simp only [Option.map_none]
          simp only [hrec] at hschur
          apply psd_of_quadratic A hA
          intro x
          have he := positive_pivot_identity A hA hzero (x 0) (fun i => x i.succ)
          rw [cons_decomposition] at he
          rw [he]
          exact add_nonneg (mul_nonneg hpos.le (sq_nonneg _))
            (by simpa only [star_trivial] using hschur.2 (fun i => x i.succ))
        | some v =>
          simp only [Option.map_some]
          simp only [hrec] at hschur
          rw [quadratic_lift A hA hzero]
          exact hschur

theorem report_none_iff (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) :
    report n A = none ↔ A.PosSemidef := by
  constructor
  · intro hr
    simpa only [hr] using report_correct n A hA
  · intro hp
    cases hr : report n A with
    | none => rfl
    | some v =>
      have hn := report_correct n A hA
      simp only [hr] at hn
      have hnonneg : 0 ≤ quadratic A v := by simpa only [star_trivial] using hp.2 v
      exact False.elim (not_lt_of_ge hnonneg hn)

theorem report_some_negative (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm)
    {v : Fin n → ℝ} (hr : report n A = some v) : quadratic A v < 0 := by
  simpa only [hr] using report_correct n A hA

theorem report_some_nonzero (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm)
    {v : Fin n → ℝ} (hr : report n A = some v) : v ≠ 0 := by
  intro hz
  have hn := report_some_negative A hA hr
  simp [hz, quadratic, dotProduct] at hn

end MatrixSpencer.KSFullManuscriptPSDSeparation
