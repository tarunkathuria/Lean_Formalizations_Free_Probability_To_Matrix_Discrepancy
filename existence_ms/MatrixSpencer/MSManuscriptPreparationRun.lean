import MatrixSpencer.MSManuscriptPaidStep

/-! The finite rank-one paid-cut loop. Its data are an actual cleanup map and
stop/direction routine. The specification is a separate local interface:
numerical response accuracy and covariance curvature must instantiate it.
This module never selects a covariance minimizer or a favorable execution. -/
open Matrix
open scoped BigOperators MatrixOrder
noncomputable section
namespace MatrixSpencer.MSManuscriptPreparationRun
open MSManuscriptPaidStep
variable {ι : Type*} [Fintype ι]

structure Data (ι : Type*) where
  clean : Matrix ι ι ℝ → Matrix ι ι ℝ
  direction : Matrix ι ι ℝ → Option (ι → ℝ)

structure Spec (D : Data ι) (f : Matrix ι ι ℝ → ℝ) (α debit : ℝ)
    (cap : Matrix ι ι ℝ → Prop) : Prop where
  clean_psd : ∀ C, C.PosSemidef → (D.clean C).PosSemidef
  clean_le : ∀ C, C.PosSemidef → D.clean C ≤ C
  clean_value_le : ∀ C, C.PosSemidef → f (D.clean C) ≤ f C
  stop : ∀ C, C.PosSemidef → D.direction (D.clean C) = none → cap (D.clean C)
  paid : ∀ C, C.PosSemidef → ∀ w, D.direction (D.clean C) = some w →
    w ≠ 0 ∧ (cut (D.clean C) α w).PosSemidef ∧
      f (cut (D.clean C) α w)+debit ≤ f (D.clean C)

/-- At most `fuel` fresh cap tests; the counter counts only paid rank-one cuts. -/
def run (D : Data ι) (α : ℝ) : ℕ → Matrix ι ι ℝ → Option (Matrix ι ι ℝ × ℕ)
  | 0, _ => none
  | fuel+1, C =>
    match D.direction (D.clean C) with
    | none => some (D.clean C, 0)
    | some w => (run D α fuel (cut (D.clean C) α w)).map (fun y => (y.1, y.2+1))

private theorem trace_mono {C K : Matrix ι ι ℝ} (h : K ≤ C) : realTrace K ≤ realTrace C := by
  have ht := realTrace_nonneg (Matrix.le_iff.mp h)
  rw [realTrace_sub] at ht
  linarith

theorem run_sound (D : Data ι) (f : Matrix ι ι ℝ → ℝ) {α debit : ℝ}
    (hα : 0 ≤ α) {cap : Matrix ι ι ℝ → Prop} (S : Spec D f α debit cap)
    (fuel : ℕ) {C : Matrix ι ι ℝ} (hC : C.PosSemidef)
    {y : Matrix ι ι ℝ × ℕ} (ho : run D α fuel C = some y) :
    y.1.PosSemidef ∧ y.1 ≤ C ∧ cap y.1 ∧ y.2 ≤ fuel ∧
      realTrace y.1+α*(y.2:ℝ) ≤ realTrace C ∧ f y.1+debit*(y.2:ℝ) ≤ f C := by
  induction fuel generalizing C y with
  | zero => simp [run] at ho
  | succ fuel ih =>
    cases hc : D.direction (D.clean C) with
    | none =>
      simp only [run, hc, Option.some.injEq] at ho
      subst y
      refine ⟨S.clean_psd C hC, S.clean_le C hC, S.stop C hC hc, by omega, ?_, ?_⟩
      · simpa using trace_mono (S.clean_le C hC)
      · simpa using S.clean_value_le C hC
    | some w =>
      simp only [run, hc] at ho
      obtain ⟨z, hz, hzy⟩ := Option.map_eq_some_iff.mp ho
      subst y
      obtain ⟨hw, hp, hf⟩ := S.paid C hC w hc
      obtain ⟨hzp, hzc, hzcap, hzcnt, hztrace, hzval⟩ := ih hp hz
      have htr := cut_trace (D.clean C) α hw
      have hclean := trace_mono (S.clean_le C hC)
      refine ⟨hzp, hzc.trans ((cut_le _ hα w).trans (S.clean_le C hC)), hzcap, by omega, ?_, ?_⟩
      · dsimp
        push_cast
        linarith
      · have hv := S.clean_value_le C hC
        dsimp
        push_cast
        linarith

/-- Failure to stop after `fuel` cap tests would consume at least `fuel*α` trace. -/
theorem trace_lower_of_run_none (D : Data ι) (f : Matrix ι ι ℝ → ℝ) {α debit : ℝ}
    {cap : Matrix ι ι ℝ → Prop} (S : Spec D f α debit cap) (fuel : ℕ)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (ho : run D α fuel C = none) :
    (fuel:ℝ)*α ≤ realTrace C := by
  induction fuel generalizing C with
  | zero => simpa using realTrace_nonneg hC
  | succ fuel ih =>
    cases hc : D.direction (D.clean C) with
    | none => simp [run, hc] at ho
    | some w =>
      have hn : run D α fuel (cut (D.clean C) α w) = none := by
        simpa only [run, hc, Option.map_eq_none_iff] using ho
      obtain ⟨hw, hp, _⟩ := S.paid C hC w hc
      have ht := ih hp hn
      have htr := cut_trace (D.clean C) α hw
      have hclean := trace_mono (S.clean_le C hC)
      push_cast
      nlinarith

/-- A scalar trace cap chooses the finite loop budget by arithmetic. -/
def budget (L α : ℝ) : ℕ := Nat.ceil (L/α)+1

theorem budget_trace_lt {L α : ℝ} (hα : 0 < α) : L < (budget L α:ℝ)*α := by
  have hc := Nat.le_ceil (L/α)
  have hm := mul_le_mul_of_nonneg_right hc hα.le
  have he : L/α*α = L := div_mul_cancel₀ L hα.ne'
  unfold budget
  push_cast
  nlinarith

theorem run_isSome (D : Data ι) (f : Matrix ι ι ℝ → ℝ) {α debit : ℝ}
    (hα : 0 < α) {cap : Matrix ι ι ℝ → Prop} (S : Spec D f α debit cap)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) {L : ℝ} (hL : realTrace C ≤ L) :
    (run D α (budget L α) C).isSome = true := by
  cases ho : run D α (budget L α) C with
  | some y => rfl
  | none =>
    have ht := trace_lower_of_run_none D f S (budget L α) hC ho
    have hb := budget_trace_lt (L := L) hα
    exfalso
    linarith

/-- The returned paid-step count is bounded by the initial trace, including all
intervening monotone unpaid deletions. -/
theorem paid_count_le (D : Data ι) (f : Matrix ι ι ℝ → ℝ) {α debit : ℝ}
    (hα : 0 < α) {cap : Matrix ι ι ℝ → Prop} (S : Spec D f α debit cap)
    (fuel : ℕ) {C : Matrix ι ι ℝ} (hC : C.PosSemidef) {y : Matrix ι ι ℝ × ℕ}
    (ho : run D α fuel C = some y) : (y.2:ℝ) ≤ realTrace C/α := by
  have hs := run_sound D f hα.le S fuel hC ho
  apply (le_div_iff₀ hα).mpr
  have hn := realTrace_nonneg hs.1
  nlinarith [hs.2.2.2.2.1]

end MatrixSpencer.MSManuscriptPreparationRun
