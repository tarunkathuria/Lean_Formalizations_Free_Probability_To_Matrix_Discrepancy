import MatrixSpencer.MSManuscriptPreparationRun

/-! An arithmetic finite clock for a fixed mesh clipped at the terminal time.
No compactness witness or favorable sampled path occurs in the clock. -/
noncomputable section
namespace MatrixSpencer.MSManuscriptEpochClock

def step (T β t : ℝ) : ℝ := min β (Real.sqrt (max 0 (T-t)))

theorem step_pos {T β t : ℝ} (hβ : 0<β) (ht : t<T) : 0<step T β t :=
  lt_min hβ (Real.sqrt_pos.mpr (lt_max_of_lt_right (sub_pos.mpr ht)))

theorem step_le (T β t : ℝ) : step T β t≤β := min_le_left _ _

theorem step_square_le {T β t : ℝ} (hβ : 0≤β) (ht : t≤T) : (step T β t)^2≤T-t := by
  have hs : 0≤step T β t := le_min hβ (Real.sqrt_nonneg _)
  have hb := (sq_le_sq₀ hs (Real.sqrt_nonneg _)).mpr (min_le_right β (Real.sqrt (max 0 (T-t))))
  rw [Real.sq_sqrt (le_max_left _ _),max_eq_right (sub_nonneg.mpr ht)] at hb
  exact hb

theorem time_le {T β t : ℝ} (hβ : 0≤β) (ht : t≤T) : t+(step T β t)^2≤T := by
  linarith [step_square_le hβ ht]

theorem step_eq_mesh_of_not_reached {T β t : ℝ} (ht : t<T)
    (hn : t+(step T β t)^2<T) : step T β t=β := by
  unfold step at *
  by_cases hb : β≤Real.sqrt (max 0 (T-t))
  · exact min_eq_left hb
  · rw [min_eq_right (le_of_not_ge hb),Real.sq_sqrt (le_max_left _ _),
      max_eq_right (sub_nonneg.mpr ht.le)] at hn
    linarith

def count (T β : ℝ) : ℕ := MSManuscriptPreparationRun.budget T (β^2)

theorem count_time_gt {T β : ℝ} (hβ : 0<β) : T<(count T β:ℝ)*β^2 :=
  MSManuscriptPreparationRun.budget_trace_lt (sq_pos_of_pos hβ)

end MatrixSpencer.MSManuscriptEpochClock
