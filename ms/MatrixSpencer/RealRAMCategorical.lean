import MatrixSpencer.RealRAMJacobiIteration
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Sampling a computed finite list of nonnegative real weights by one
uniform real draw in `[0,1)`. The subtraction scan is explicit and linear in
the list length. Its Lebesgue interval probabilities equal the supplied
weights exactly, including zero weights. Constructing the weights is a
separate counted numerical computation; it is not a primitive here.

This uses a uniform real random register, not an uncharged oracle for an
arbitrary finite distribution. Arithmetic, comparisons and list control are
counted below. Bit generation is outside this exact random real-RAM model. -/

open MeasureTheory Set
noncomputable section
namespace MatrixSpencer.RealRAM.Categorical
open JacobiIteration (Counted)

def select : List ℝ → ℝ → Option ℕ
  | [], _ => none
  | w :: ws, u => if u < w then some 0 else (select ws (u-w)).map Nat.succ

def scan : List ℝ → ℝ → Counted (Option ℕ)
  | [], _ => ⟨none, 1⟩
  | w :: ws, u =>
      if u < w then ⟨some 0, 5⟩ else
        let tail := scan ws (u-w)
        ⟨tail.value.map Nat.succ, tail.cost+10⟩

theorem scan_value (ws : List ℝ) (u : ℝ) : (scan ws u).value = select ws u := by
  induction ws generalizing u with
  | nil => rfl
  | cons w ws ih => simp only [scan, select]; split <;> simp_all

theorem scan_cost (ws : List ℝ) (u : ℝ) : (scan ws u).cost ≤ 10*ws.length+1 := by
  induction ws generalizing u with
  | nil => simp [scan]
  | cons w ws ih =>
    simp only [scan, List.length_cons]
    split
    · dsimp; omega
    · dsimp; have h := ih (u-w); omega

def residual : Expr Bool := .sub (.input false) (.input true)
def registers (u w : ℝ) : Bool → ℝ := fun b => if b then w else u

theorem residual_executes (u w : ℝ) :
    Expr.Executes (registers u w) residual (u-w) 3 := by
  exact Expr.Executes.sub (Expr.Executes.input false) (Expr.Executes.input true)

inductive Executes : List ℝ → ℝ → Option ℕ → ℕ → Prop where
  | nil (u : ℝ) : Executes [] u none 1
  | hit (w : ℝ) (ws : List ℝ) (u : ℝ) (hu : u < w) :
      Executes (w::ws) u (some 0) 5
  | miss {w u v : ℝ} {ws : List ℝ} {out : Option ℕ} {cost : ℕ} :
      ¬u < w → Expr.Executes (registers u w) residual v 3 →
      Executes ws v out cost →
      Executes (w::ws) u (out.map Nat.succ) (cost+10)

theorem scan_executes (ws : List ℝ) (u : ℝ) :
    Executes ws u (scan ws u).value (scan ws u).cost := by
  induction ws generalizing u with
  | nil => exact Executes.nil u
  | cons w ws ih =>
    by_cases hu : u < w
    · simpa only [scan, if_pos hu] using Executes.hit w ws u hu
    · simpa only [scan, if_neg hu] using
        Executes.miss hu (residual_executes u w) (ih (u-w))

def lower (ws : List ℝ) (j : ℕ) : ℝ := (ws.take j).sum

theorem selected_iff (ws : List ℝ) (hw : ∀ w ∈ ws, 0 ≤ w)
    (j : ℕ) (hj : j < ws.length) (u : ℝ) :
    (0 ≤ u ∧ select ws u = some j) ↔
      lower ws j ≤ u ∧ u < lower ws j + ws[j] := by
  induction ws generalizing j u with
  | nil => simp at hj
  | cons w ws ih =>
    have hw0 : 0 ≤ w := hw w (by simp)
    have hws : ∀ v ∈ ws, 0 ≤ v := fun v hv => hw v (by simp [hv])
    cases j with
    | zero =>
      simp only [lower, List.take_zero, List.sum_nil, List.getElem_cons_zero, zero_add]
      by_cases hu : u < w
      · simp [select, hu]
      · simp only [select, if_neg hu]
        cases select ws (u-w) <;> simp [hu]
    | succ j =>
      have hj' : j < ws.length := by simpa using hj
      have hnon : 0 ≤ lower ws j := List.sum_nonneg (fun v hv => hws v (List.mem_of_mem_take hv))
      have ht := ih hws j hj' (u-w)
      simp only [lower, List.take_succ_cons, List.sum_cons, List.getElem_cons_succ]
      change (0 ≤ u ∧ select (w::ws) u = some (j+1)) ↔
        w + lower ws j ≤ u ∧ u < w + lower ws j + ws[j]
      by_cases hu : u < w
      · have hbad : ¬w + lower ws j ≤ u := by linarith
        simp [select, hu, hbad]
      · simp only [select, if_neg hu]
        have hm : (select ws (u-w)).map Nat.succ = some (j+1) ↔
            select ws (u-w) = some j := by
          cases select ws (u-w) <;> simp
        rw [hm]
        constructor
        · intro h
          have hi := ht.mp ⟨by linarith, h.2⟩
          constructor <;> linarith [hi.1, hi.2]
        · intro h
          have hi := ht.mpr ⟨by linarith [h.1], by linarith [h.2]⟩
          exact ⟨by linarith, hi.2⟩

theorem selected_lt_sum (ws : List ℝ) (hw : ∀ w ∈ ws, 0 ≤ w)
    {u : ℝ} (hu : 0 ≤ u) {j : ℕ} (hs : select ws u = some j) : u < ws.sum := by
  induction ws generalizing u j with
  | nil => simp [select] at hs
  | cons w ws ih =>
    have hws : ∀ v ∈ ws, 0 ≤ v := fun v hv => hw v (by simp [hv])
    have hsum : 0 ≤ ws.sum := List.sum_nonneg hws
    by_cases h : u < w
    · simp only [List.sum_cons]; linarith
    · simp only [select, if_neg h] at hs
      obtain ⟨j', hj', _⟩ := Option.map_eq_some_iff.mp hs
      have ht := ih hws (by linarith) hj'
      simp only [List.sum_cons]; linarith

theorem selected_exists (ws : List ℝ) (hw : ∀ w ∈ ws, 0 ≤ w)
    {u : ℝ} (hu : 0 ≤ u) (hs : u < ws.sum) : ∃ j, select ws u = some j := by
  induction ws generalizing u with
  | nil => simp at hs; linarith
  | cons w ws ih =>
    have hws : ∀ v ∈ ws, 0 ≤ v := fun v hv => hw v (by simp [hv])
    by_cases h : u < w
    · exact ⟨0, by simp [select, h]⟩
    · have ht : u-w < ws.sum := by
        simp only [List.sum_cons] at hs
        linarith
      obtain ⟨j,hj⟩ := ih hws (u := u-w) (by linarith) ht
      exact ⟨j+1, by simp [select, h, hj]⟩

theorem selected_index_lt (ws : List ℝ) (u : ℝ) {j : ℕ}
    (hs : select ws u = some j) : j < ws.length := by
  induction ws generalizing u j with
  | nil => simp [select] at hs
  | cons w ws ih =>
    by_cases h : u < w
    · simp only [select, if_pos h, Option.some.injEq] at hs
      subst j
      simp
    · simp only [select, if_neg h] at hs
      obtain ⟨j', hj', he⟩ := Option.map_eq_some_iff.mp hs
      have hi := ih (u-w) hj'
      simp only [List.length_cons]
      omega

/-- One uniform `[0,1)` draw realizes exactly the original real weights. -/
theorem sampling_probability (ws : List ℝ) (hw : ∀ w ∈ ws, 0 ≤ w)
    (hsum : ws.sum = 1) (j : ℕ) (hj : j < ws.length) :
    (volume.restrict (Ico (0:ℝ) 1)) {u | (scan ws u).value = some j} =
      ENNReal.ofReal ws[j] := by
  rw [Measure.restrict_apply' measurableSet_Ico]
  have he : {u | (scan ws u).value = some j} ∩ Ico (0:ℝ) 1 =
      Ico (lower ws j) (lower ws j + ws[j]) := by
    ext u
    simp only [mem_inter_iff, mem_setOf_eq, mem_Ico, scan_value]
    constructor
    · intro h
      exact (selected_iff ws hw j hj u).mp ⟨h.2.1,h.1⟩
    · intro h
      have ht := (selected_iff ws hw j hj u).mpr h
      exact ⟨ht.2,ht.1,hsum ▸ selected_lt_sum ws hw ht.1 ht.2⟩
  rw [he, Real.volume_Ico]
  congr 1
  ring

theorem execution_bounded (ws : List ℝ) (hw : ∀ w ∈ ws, 0 ≤ w)
    (hsum : ws.sum = 1) {u : ℝ} (hu : u ∈ Ico (0:ℝ) 1) :
    ∃ j cost, j < ws.length ∧ Executes ws u (some j) cost ∧
      cost ≤ 10*ws.length+1 := by
  obtain ⟨j,hj⟩ := selected_exists ws hw hu.1 (hsum.symm ▸ hu.2)
  have he := scan_executes ws u
  rw [scan_value, hj] at he
  exact ⟨j,(scan ws u).cost,selected_index_lt ws u hj,he,scan_cost ws u⟩

end MatrixSpencer.RealRAM.Categorical
