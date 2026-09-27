import HigherRankKSRuntime.CleanupScan
import HigherRankKSRuntime.PreparationScan
import HigherRankKSRuntime.WalkExecution
import HigherRankKSRuntime.ActiveExecution

/-! The executable local controller. It scans cleanup guards, evaluates the
base potential, scans actual preparation reports, and otherwise constructs
the tangent Hessian step and zero-extends it to the original owner labels.
The lemmas below expose precisely the branches that subsequent analytic
lemmas discharge; these are not additional primitives. -/

noncomputable section
open scoped BigOperators
namespace HigherRankKSRuntime.NextEvent
open AugmentedHigherRankKS ControllerLoop ActiveEnumeration
open MatrixSpencer.RealRAM.JacobiIteration (Counted)
open MatrixSpencer RealRAM
open Tangent
variable {N : ℕ}

def chartReport (query : EpochState (Fin N) → Counted ℝ) (a : ℝ)
    (z : EpochState (Fin N)) : FullHessian.Report (count z) :=
  fun u =>
    let ex := Execution.extension z u
    let out := query (movement a z ex.value 1)
    ⟨out.value, out.cost + ex.cost + 100*(N+1)^2⟩

theorem chartReport_value (query : EpochState (Fin N) → Counted ℝ) (a : ℝ)
    (z : EpochState (Fin N)) (u : KSNumericalHessian.Space (count z)) :
    (chartReport query a z u).value = (query (movement a z (extend z u) 1)).value := by
  simp only [chartReport, Execution.extension_value]

/-- The rank-zero branch is a totality guard. The rejected-preparation
curvature theorem proves that this guard is unreachable on a clean state. -/
def afterRejection (query : EpochState (Fin N) → Counted ℝ)
    (a t h : ℝ) (z : EpochState (Fin N)) : Counted (Event (Fin N)) :=
  let x := Execution.positions z
  if hr : 0 < (Frame.canonical (count z) (restrictedPosition z)).rank then
    let g := WalkExecution.compute (chartReport query a z) (restrictedPosition z) t h hr
    let out := Execution.extension z g.value
    ⟨.move out.value, x.cost + g.cost + out.cost + 100 * (N + 1) ^ 2⟩
  else ⟨.done, x.cost + 100 * (N + 1) ^ 2⟩

def compute (query : EpochState (Fin N) → Counted ℝ)
    (a step h t p0 ρ ζ : ℝ) (z : EpochState (Fin N)) : Counted (Event (Fin N)) :=
  let cleanup := CleanupScan.scan z ρ ζ (List.finRange N)
  match cleanup.value with
  | some e => ⟨e.event, cleanup.cost + 100 * (N + 1) ^ 2⟩
  | none =>
      let tab := Execution.table z
      if count z = 0 then ⟨.done, cleanup.cost + tab.cost + 100 * (N + 1) ^ 2⟩
      else
        let base := query z
        let prep := PreparationScan.scan (fun i => query (prepareOwner a z i step))
          base.value (-(step * p0 / (4 * a))) (labels z)
        match prep.value with
        | some i => ⟨.prepare i, cleanup.cost + tab.cost + base.cost + prep.cost +
            100 * (N + 1) ^ 2⟩
        | none =>
            let out := afterRejection query a t h z
            ⟨out.value, cleanup.cost + tab.cost + base.cost + prep.cost + out.cost⟩

def Clean (z : EpochState (Fin N)) (ρ ζ : ℝ) : Prop :=
  ∀ i, 0 < reserve z i → ρ < 1 - |position z i| ∧ 2 * ζ ≤ reserve z i

def Rejected (query : EpochState (Fin N) → Counted ℝ)
    (a step p0 : ℝ) (z : EpochState (Fin N)) : Prop :=
  (PreparationScan.scan (fun i => query (prepareOwner a z i step))
    (query z).value (-(step * p0 / (4 * a))) (labels z)).value = none

theorem clean_of_scan_none {z : EpochState (Fin N)} {ρ ζ : ℝ}
    (hc : (CleanupScan.scan z ρ ζ (List.finRange N)).value = none) : Clean z ρ ζ := by
  intro i hi
  exact CleanupScan.scan_none z ρ ζ (List.finRange N) hc i (List.mem_finRange i) hi

theorem terminal_of_count_zero {a R : ℝ} {z : EpochState (Fin N)}
    (hz : z ∈ epochDomain a R) (hc : count z = 0) : Terminal z := by
  intro i
  have hn : ¬ 0 < reserve z i := by
    intro hi
    have hm := (mem_labels z i).mpr hi
    have he : labels z = [] := List.length_eq_zero_iff.mp hc
    simpa [he] using hm
  exact le_antisymm (le_of_not_gt hn) (hz i).2.2.2.2.1

theorem afterRejection_value (query : EpochState (Fin N) → Counted ℝ)
    (a t h : ℝ) (z : EpochState (Fin N))
    (hr : 0 < (Frame.canonical (count z) (restrictedPosition z)).rank) :
    (afterRejection query a t h z).value = .move
      (extend z (WalkExecution.compute (chartReport query a z)
        (restrictedPosition z) t h hr).value) := by
  simp only [afterRejection, dif_pos hr, Execution.extension_value]

theorem afterRejection_valid (query : EpochState (Fin N) → Counted ℝ)
    (a R step t h : ℝ) (z : EpochState (Fin N))
    (hr : 0 < (Frame.canonical (count z) (restrictedPosition z)).rank)
    (hfeas : movement a z (extend z (WalkExecution.compute (chartReport query a z)
        (restrictedPosition z) t h hr).value) h ∈ epochDomain a R) :
    (afterRejection query a t h z).value.Valid a R step h z := by
  rw [afterRejection_value query a t h z hr]
  exact ⟨extend_orthogonal z _ (WalkExecution.compute_orthogonal _ _ _ _ _),
    extend_unit_square_sum z _ (WalkExecution.compute_unit _ _ _ _ _), hfeas⟩

theorem valid (query : EpochState (Fin N) → Counted ℝ)
    {a R step h t p0 ρ ζ : ℝ} (ha : 0 < a) (hstep : 0 ≤ step)
    (hstepζ : step ≤ 2 * ζ) {z : EpochState (Fin N)} (hz : z ∈ epochDomain a R)
    (hmove : Clean z ρ ζ → count z ≠ 0 → Rejected query a step p0 z →
      (afterRejection query a t h z).value.Valid a R step h z) :
    (compute query a step h t p0 ρ ζ z).value.Valid a R step h z := by
  generalize he : (CleanupScan.scan z ρ ζ (List.finRange N)).value = cleanup
  cases cleanup with
  | some e =>
      simp only [compute, he]
      exact CleanupScan.Cleanup.valid (CleanupScan.scan_some z ρ ζ (List.finRange N) he).2
  | none =>
      have hclean := clean_of_scan_none he
      by_cases hc : count z = 0
      · simp only [compute, he, hc, ↓reduceIte]
        exact terminal_of_count_zero hz hc
      · generalize hp : (PreparationScan.scan (fun i => query (prepareOwner a z i step))
          (query z).value (-(step * p0 / (4 * a))) (labels z)).value = prep
        cases prep with
        | some i =>
          simp only [compute, he, hc, ↓reduceIte, hp]
          have hi := (PreparationScan.scan_some _ _ _ _ hp).1
          exact prepareOwner_feasible hz ha i hstep
            (hstepζ.trans (hclean i ((mem_labels z i).mp hi)).2)
        | none =>
          simp only [compute, he, hc, ↓reduceIte, hp]
          exact hmove hclean hc hp

theorem potential_le (query : EpochState (Fin N) → Counted ℝ)
    {a step h t p0 ρ ζ κ : ℝ} (E : EpochState (Fin N) → ℝ)
    (z : EpochState (Fin N))
    (hcleanup : ∀ e : CleanupScan.Cleanup (Fin N), e.Enabled z ρ ζ →
      E (e.event.apply a step h z) ≤ E z + κ)
    (hprep : Clean z ρ ζ → ∀ i ∈ labels z,
      (query (prepareOwner a z i step)).value - (query z).value ≤ -(step * p0 / (4*a)) →
      E (prepareOwner a z i step) ≤ E z)
    (hmove : Clean z ρ ζ → count z ≠ 0 → Rejected query a step p0 z →
      E ((afterRejection query a t h z).value.apply a step h z) ≤ E z) :
    E ((compute query a step h t p0 ρ ζ z).value.apply a step h z) ≤
      E z + ((compute query a step h t p0 ρ ζ z).value.cleanups : ℝ) * κ := by
  generalize he : (CleanupScan.scan z ρ ζ (List.finRange N)).value = cleanup
  cases cleanup with
  | some e =>
      simp only [compute, he, CleanupScan.Cleanup.cleanups, Nat.cast_one, one_mul]
      exact hcleanup e (CleanupScan.scan_some z ρ ζ (List.finRange N) he).2
  | none =>
      have hclean := clean_of_scan_none he
      by_cases hc : count z = 0
      · simp only [compute, he, hc, ↓reduceIte, Event.apply, Event.cleanups,
          Nat.cast_zero, zero_mul, add_zero, le_refl]
      · generalize hp : (PreparationScan.scan (fun i => query (prepareOwner a z i step))
          (query z).value (-(step * p0 / (4 * a))) (labels z)).value = prep
        cases prep with
        | some i =>
          simp only [compute, he, hc, ↓reduceIte, hp, Event.apply, Event.cleanups,
            Nat.cast_zero, zero_mul, add_zero]
          obtain ⟨hi, ha⟩ := PreparationScan.scan_some _ _ _ _ hp
          exact hprep hclean i hi ha
        | none =>
          simp only [compute, he, hc, ↓reduceIte, hp]
          have hm := hmove hclean hc hp
          have hzcleanup : (afterRejection query a t h z).value.cleanups = 0 := by
            unfold afterRejection
            split_ifs <;> rfl
          simpa only [hzcleanup, Nat.cast_zero, zero_mul, add_zero] using hm

end HigherRankKSRuntime.NextEvent
