import HigherRankKSRuntime.ControllerLoop
import HigherRankKSRuntime.ValueDecisions

/-! The preparation branch scans actual approximate value reports and stops
at the first accepted withdrawal. A rejected scan supplies a rejection for
every owner; it does not take that certificate as an oracle input. -/

noncomputable section
namespace HigherRankKSRuntime.PreparationScan
open MatrixSpencer.RealRAM.JacobiIteration (Counted)

variable {ι : Type*}

def scan (query : ι → Counted ℝ) (base threshold : ℝ) : List ι → Counted (Option ι)
  | [] => ⟨none, 0⟩
  | i :: rest =>
      let r := query i
      if r.value - base ≤ threshold then ⟨some i, r.cost + 3⟩
      else
        let out := scan query base threshold rest
        ⟨out.value, r.cost + out.cost + 3⟩

theorem scan_some (query : ι → Counted ℝ) (base threshold : ℝ)
    (owners : List ι) {i : ι} (hi : (scan query base threshold owners).value = some i) :
    i ∈ owners ∧ (query i).value - base ≤ threshold := by
  induction owners with
  | nil => simp [scan] at hi
  | cons j rest ih =>
    by_cases hj : (query j).value - base ≤ threshold
    · simp only [scan, hj, ↓reduceIte, Option.some.injEq] at hi
      subst j
      exact ⟨List.mem_cons_self, hj⟩
    · simp only [scan, hj, ↓reduceIte] at hi
      obtain ⟨hm, ha⟩ := ih hi
      exact ⟨List.mem_cons_of_mem _ hm, ha⟩

theorem scan_none (query : ι → Counted ℝ) (base threshold : ℝ)
    (owners : List ι) (hn : (scan query base threshold owners).value = none) :
    ∀ i ∈ owners, threshold < (query i).value - base := by
  induction owners with
  | nil => simp
  | cons j rest ih =>
    by_cases hj : (query j).value - base ≤ threshold
    · simp [scan, hj] at hn
    · simp only [scan, hj, ↓reduceIte] at hn
      intro i hi
      rcases List.mem_cons.mp hi with hi | hi
      · subst i
        exact lt_of_not_ge hj
      · exact ih hn i hi

theorem scan_work_le (query : ι → Counted ℝ) (base threshold : ℝ)
    (owners : List ι) {Q : ℕ} (hQ : ∀ i ∈ owners, (query i).cost ≤ Q) :
    (scan query base threshold owners).cost ≤ owners.length * (Q + 3) := by
  induction owners with
  | nil => simp [scan]
  | cons j rest ih =>
    have hj := hQ j List.mem_cons_self
    have hr := ih (fun i hi => hQ i (List.mem_cons_of_mem _ hi))
    simp only [scan, List.length_cons]
    split_ifs <;> nlinarith

theorem accepted_actual_descent (query : ι → Counted ℝ) (baseReport baseValue : ℝ)
    (value : ι → ℝ) (owners : List ι) {i : ι} {scale ν : ℝ}
    (hbase : |baseReport - baseValue| ≤ ν)
    (herr : ∀ i ∈ owners, |(query i).value - value i| ≤ ν)
    (hν : ν ≤ scale / 64)
    (hi : (scan query baseReport (-scale / 4) owners).value = some i) :
    value i - baseValue ≤ -(7 * scale / 32) := by
  obtain ⟨hm, ha⟩ := scan_some query baseReport (-scale / 4) owners hi
  exact preparation_accepted_descent
    (reported_difference_error hbase (herr i hm)) hν ha

theorem rejected_actual_derivative (query : ι → Counted ℝ) (baseReport baseValue : ℝ)
    (value deriv : ι → ℝ) (owners : List ι) {step p0 a M ν : ℝ}
    (hstep : 0 < step) (ha : 0 < a) (hp0 : 0 ≤ p0)
    (hbase : |baseReport - baseValue| ≤ ν)
    (herr : ∀ i ∈ owners, |(query i).value - value i| ≤ ν)
    (htaylor : ∀ i ∈ owners, |(value i - baseValue) / step - deriv i| ≤ M * step / 2)
    (hν : ν ≤ step * p0 / (64 * a)) (hsmall : M * step ≤ p0 / (8 * a))
    (hn : (scan query baseReport (-(step * p0 / (4 * a))) owners).value = none) :
    ∀ i ∈ owners, -(p0 / (2 * a)) < deriv i := by
  intro i hi
  exact preparation_rejected_derivative hstep ha hp0
    (reported_difference_error hbase (herr i hi)) (htaylor i hi) hν hsmall
    (scan_none query baseReport _ owners hn i hi)

end HigherRankKSRuntime.PreparationScan
