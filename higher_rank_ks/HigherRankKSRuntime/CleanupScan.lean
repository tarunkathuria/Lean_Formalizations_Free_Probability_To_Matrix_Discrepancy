import HigherRankKSRuntime.ControllerLoop
import HigherRankKSRuntime.CleanupPotential

/-! The explicit cleanup scan tests original coordinates in order. It rounds
only inside the prescribed face margin and otherwise exhausts tiny reserves. -/

noncomputable section
namespace HigherRankKSRuntime.CleanupScan
open AugmentedHigherRankKS
open MatrixSpencer.RealRAM.JacobiIteration (Counted)
open ControllerLoop

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

inductive Cleanup (ι : Type*)
  | round (i : ι)
  | exhaust (i : ι)

def Cleanup.owner : Cleanup ι → ι | .round i | .exhaust i => i
def Cleanup.event : Cleanup ι → Event ι | .round i => .round i | .exhaust i => .exhaust i

def Cleanup.Enabled (z : EpochState ι) (ρ ζ : ℝ) : Cleanup ι → Prop
  | .round i => 0 < reserve z i ∧ 1 - |position z i| ≤ ρ
  | .exhaust i => 0 < reserve z i ∧ reserve z i < 2 * ζ

def scan (z : EpochState ι) (ρ ζ : ℝ) : List ι → Counted (Option (Cleanup ι))
  | [] => ⟨none, 0⟩
  | i :: rest =>
      if 0 < reserve z i then
        if 1 - |position z i| ≤ ρ then ⟨some (.round i), 8⟩
        else if reserve z i < 2 * ζ then ⟨some (.exhaust i), 8⟩
        else
          let out := scan z ρ ζ rest
          ⟨out.value, out.cost + 8⟩
      else
        let out := scan z ρ ζ rest
        ⟨out.value, out.cost + 8⟩

theorem scan_some (z : EpochState ι) (ρ ζ : ℝ) (owners : List ι)
    {e : Cleanup ι} (he : (scan z ρ ζ owners).value = some e) :
    e.owner ∈ owners ∧ e.Enabled z ρ ζ := by
  induction owners with
  | nil => simp [scan] at he
  | cons i rest ih =>
    by_cases hi : 0 < reserve z i
    · by_cases hf : 1 - |position z i| ≤ ρ
      · simp only [scan, hi, hf, ↓reduceIte, Option.some.injEq] at he
        subst e
        exact ⟨List.mem_cons_self, hi, hf⟩
      · by_cases hc : reserve z i < 2 * ζ
        · simp only [scan, hi, hf, hc, ↓reduceIte, Option.some.injEq] at he
          subst e
          exact ⟨List.mem_cons_self, hi, hc⟩
        · simp only [scan, hi, hf, hc, ↓reduceIte] at he
          obtain ⟨hm, he⟩ := ih he
          exact ⟨List.mem_cons_of_mem _ hm, he⟩
    · simp only [scan, hi, ↓reduceIte] at he
      obtain ⟨hm, he⟩ := ih he
      exact ⟨List.mem_cons_of_mem _ hm, he⟩

theorem scan_none (z : EpochState ι) (ρ ζ : ℝ) (owners : List ι)
    (he : (scan z ρ ζ owners).value = none) :
    ∀ i ∈ owners, 0 < reserve z i → ρ < 1 - |position z i| ∧ 2 * ζ ≤ reserve z i := by
  induction owners with
  | nil => simp
  | cons i rest ih =>
    by_cases hi : 0 < reserve z i
    · by_cases hf : 1 - |position z i| ≤ ρ
      · simp [scan, hi, hf] at he
      · by_cases hc : reserve z i < 2 * ζ
        · simp [scan, hi, hf, hc] at he
        · simp only [scan, hi, hf, hc, ↓reduceIte] at he
          intro j hj hjp
          rcases List.mem_cons.mp hj with hj | hj
          · subst j
            exact ⟨lt_of_not_ge hf, le_of_not_gt hc⟩
          · exact ih he j hj hjp
    · simp only [scan, hi, ↓reduceIte] at he
      intro j hj hjp
      rcases List.mem_cons.mp hj with hj | hj
      · subst j
        exact (hi hjp).elim
      · exact ih he j hj hjp

theorem scan_work_le (z : EpochState ι) (ρ ζ : ℝ) (owners : List ι) :
    (scan z ρ ζ owners).cost ≤ owners.length * 8 := by
  induction owners with
  | nil => simp [scan]
  | cons i rest ih =>
    simp only [scan, List.length_cons]
    split_ifs <;> nlinarith

theorem Cleanup.valid {a R step h ρ ζ : ℝ} {z : EpochState ι}
    {e : Cleanup ι} (he : e.Enabled z ρ ζ) : e.event.Valid a R step h z := by
  cases e <;> exact he.1

theorem Cleanup.cleanups (e : Cleanup ι) : e.event.cleanups = 1 := by cases e <;> rfl

theorem Cleanup.face_distance {a R ρ ζ : ℝ} {z : EpochState ι}
    (hz : z ∈ epochDomain a R) {i : ι} (hi : (Cleanup.round i).Enabled z ρ ζ) :
    |faceSign (position z i) - position z i| ≤ ρ := by
  have hc : |position z i| ≤ 1 := abs_le.mpr ⟨(hz i).1, (hz i).2.1⟩
  rw [faceSign_distance hc]
  exact hi.2

end HigherRankKSRuntime.CleanupScan
