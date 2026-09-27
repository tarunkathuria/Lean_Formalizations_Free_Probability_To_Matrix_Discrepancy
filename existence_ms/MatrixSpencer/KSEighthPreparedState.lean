import MatrixSpencer.KSEighthRetirementLoop

open Set
noncomputable section
namespace MatrixSpencer.KSEighthPreparedState

open KSEighthRetirementLoop
variable {N : ℕ}

theorem prepare_eq_or_endpoint {a τ : ℝ} (ha : 0 ≤ a)
    (report : (Fin N → ℝ) → ℝ) (k : ℕ) (x : Fin N → ℝ) (i : Fin N) :
    prepare a τ report k x i = x i ∨ |prepare a τ report k x i| = a := by
  induction k generalizing x with
  | zero => exact Or.inl rfl
  | succ k ih =>
    cases hs : select a τ report x with
    | none => simp only [prepare, hs, true_or]
    | some c =>
      simp only [prepare, hs]
      rcases ih (update a x c) with he | he
      · by_cases hi : i = c.1
        · right
          rw [he]
          subst i
          simp only [update, Function.update_self]
          exact endpoint_abs ha _
        · left
          rw [he]
          exact Function.update_of_ne hi _ _
      · exact Or.inr he

theorem prepare_live_eq_input {a τ : ℝ} (ha : 0 ≤ a)
    (report : (Fin N → ℝ) → ℝ) (k : ℕ) (x : Fin N → ℝ) (i : Fin N)
    (hi : |prepare a τ report k x i| < a) : prepare a τ report k x i = x i := by
  rcases prepare_eq_or_endpoint ha report k x i with h | h
  · exact h
  · exact False.elim ((ne_of_lt hi) h)

theorem prepare_preserves_live_margin {a τ ρ : ℝ} (ha : 0 ≤ a)
    (report : (Fin N → ℝ) → ℝ) (k : ℕ) (x : Fin N → ℝ)
    (hmargin : ∀ i, |x i| < a → ρ < a - |x i|)
    (i : Fin N) (hi : |prepare a τ report k x i| < a) :
    ρ < a - |prepare a τ report k x i| := by
  have he := prepare_live_eq_input ha report k x i hi
  rw [he] at hi ⊢
  exact hmargin i hi


def prepareState (a τ ρ : ℝ) (report : (Fin N → ℝ) → ℝ)
    (x : Fin N → ℝ) : Fin N → ℝ :=
  prepare a τ report N (KSCubePreparation.snap a ρ x)

theorem prepareState_mem_cube {a τ ρ : ℝ} (ha : 0 ≤ a)
    (report : (Fin N → ℝ) → ℝ) {x : Fin N → ℝ} (hx : x ∈ ksCube a) :
    prepareState a τ ρ report x ∈ ksCube a :=
  prepare_mem_cube ha report N (KSCubePreparation.snap_mem_cube ha hx)

theorem prepareState_preserves_frozen {a τ ρ : ℝ}
    (report : (Fin N → ℝ) → ℝ) (x : Fin N → ℝ) (i : Fin N) (hi : |x i| = a) :
    prepareState a τ ρ report x i = x i := by
  have hs := KSCubePreparation.snap_preserves_frozen (ρ := ρ) x i hi
  exact (prepare_preserves_frozen report N (KSCubePreparation.snap a ρ x) i
    (by rwa [hs])).trans hs

theorem prepareState_live_margin {a τ ρ : ℝ} (ha : 0 ≤ a)
    (report : (Fin N → ℝ) → ℝ) (x : Fin N → ℝ) (i : Fin N)
    (hi : |prepareState a τ ρ report x i| < a) :
    ρ < a - |prepareState a τ ρ report x i| :=
  prepare_preserves_live_margin ha report N (KSCubePreparation.snap a ρ x)
    (KSCubePreparation.snap_live_margin ha x) i hi

theorem prepareState_energy_progress {a τ ρ : ℝ} (ha : 0 ≤ a)
    (report : (Fin N → ℝ) → ℝ) {x : Fin N → ℝ} (hx : x ∈ ksCube a) :
    KSCubePreparation.energy x ≤ KSCubePreparation.energy (prepareState a τ ρ report x) :=
  (KSCubePreparation.snap_energy_progress hx).trans
    (prepare_energy_progress ha report N (KSCubePreparation.snap_mem_cube ha hx))

theorem prepareState_exhausts_tests {a τ ρ : ℝ} (ha : 0 ≤ a)
    (report : (Fin N → ℝ) → ℝ) (x : Fin N → ℝ) :
    select a τ report (prepareState a τ ρ report x) = none :=
  prepare_exhausts_tests ha report (KSCubePreparation.snap a ρ x)

end MatrixSpencer.KSEighthPreparedState
