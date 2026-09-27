import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

/-!
# A finite clock for a fixed support mesh

The last step may be shortened only to reach the time limit. The natural
ceiling clock strictly decreases on every step with a fixed positive mesh.
-/

noncomputable section
namespace MatrixSpencer

def epochMeshStep (mesh limit time : ℝ) : ℝ := min mesh (Real.sqrt (limit - time))

def epochMeshFuel (mesh limit time : ℝ) : ℕ := Nat.ceil ((limit - time) / mesh ^ 2)

theorem epochMeshStep_pos {mesh limit time : ℝ} (hm : 0 < mesh) (ht : time < limit) :
    0 < epochMeshStep mesh limit time := lt_min hm (Real.sqrt_pos.mpr (sub_pos.mpr ht))

theorem epochMeshStep_le (mesh limit time : ℝ) : epochMeshStep mesh limit time ≤ mesh :=
  min_le_left _ _

theorem epochMeshStep_time_le {mesh limit time : ℝ} (hm : 0 < mesh) (ht : time < limit) :
    time + epochMeshStep mesh limit time ^ 2 ≤ limit := by
  have h0 := (epochMeshStep_pos hm ht).le
  have hh : epochMeshStep mesh limit time ≤ Real.sqrt (limit - time) := min_le_right _ _
  have hs := Real.sq_sqrt (sub_nonneg.mpr ht.le)
  have hs0 := Real.sqrt_nonneg (limit - time)
  nlinarith

/-- A shortened step immediately reaches the stopping time. -/
theorem epochMeshStep_full_or_terminal {mesh limit time : ℝ} (hm : 0 < mesh)
    (ht : time < limit) :
    epochMeshStep mesh limit time = mesh ∨
      time + epochMeshStep mesh limit time ^ 2 = limit := by
  by_cases hh : mesh ≤ Real.sqrt (limit - time)
  · exact Or.inl (min_eq_left hh)
  · right
    rw [epochMeshStep, min_eq_right (le_of_not_ge hh), Real.sq_sqrt (sub_nonneg.mpr ht.le)]
    ring

theorem epochMeshFuel_pos {mesh limit time : ℝ} (hm : 0 < mesh) (ht : time < limit) :
    0 < epochMeshFuel mesh limit time := Nat.ceil_pos.mpr (div_pos (sub_pos.mpr ht) (sq_pos_of_pos hm))

theorem epochMeshFuel_full_step {mesh limit time : ℝ} (hm : 0 < mesh) :
    epochMeshFuel mesh limit (time + mesh ^ 2) = epochMeshFuel mesh limit time - 1 := by
  unfold epochMeshFuel
  have he : (limit - (time + mesh ^ 2)) / mesh ^ 2 = (limit - time) / mesh ^ 2 - 1 := by
    field_simp
    ring
  rw [he, Nat.ceil_sub_one]

/-- The actual capped step strictly decreases a finite natural clock. -/
theorem epochMeshFuel_decreases {mesh limit time : ℝ} (hm : 0 < mesh) (ht : time < limit) :
    epochMeshFuel mesh limit (time + epochMeshStep mesh limit time ^ 2) <
      epochMeshFuel mesh limit time := by
  have hp := epochMeshFuel_pos hm ht
  rcases epochMeshStep_full_or_terminal hm ht with hh | hh
  · rw [hh, epochMeshFuel_full_step hm]
    omega
  · rw [hh]
    simpa [epochMeshFuel] using hp

end MatrixSpencer
