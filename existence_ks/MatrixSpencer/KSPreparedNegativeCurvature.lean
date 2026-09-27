import MatrixSpencer.KSWeightedNegativeCurvature
import MatrixSpencer.KSDebitWalkRun

/-!
# Negative normalized curvature at every nonterminal prepared walk state

Exhausted endpoint tests make preparation a fixed point. The actual local
descent theorem therefore applies at every prepared state of the defined
walk, not only states presented syntactically as one preparation output.
-/

open Set
noncomputable section
namespace MatrixSpencer.KSPreparedNegativeCurvature

open KSDebitPreparation KSDebitWalkRun KSLiveEnumeration KSWeightedLiveCoordinates
variable {N : ℕ}

theorem prepare_eq_of_exhausted (η : ℝ) (report : (Fin N → ℝ) → ℝ) (x : Fin N → ℝ)
    (h : Retirement.select 1 (-η) report x = none) : prepare η report x = x := by
  have he (k : ℕ) : KSEighthRetirementLoop.prepare 1 (-η) report k x = x := by
    cases k with
    | zero => rfl
    | succ k => simp only [KSEighthRetirementLoop.prepare, h]
  exact he N

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- The direction is expressed in the exact explicit live coordinates;
the potential being differentiated is the actual state potential. -/
theorem exists_negative_second (C : Controller N n) (s : State C) (hs : ¬terminal s) :
    ∃ w : EuclideanSpace ℝ (Fin (count s.coeff)), w ≠ 0 ∧
      deriv (fun t : ℝ => statePotential C.vectors C.δ C.η C.θ (face s.coeff (t • w))) 0 = 0 ∧
      iteratedDeriv 2 (fun t : ℝ => statePotential C.vectors C.δ C.η C.θ
        (face s.coeff (t • w))) 0 < 0 := by
  have hlive := count_pos_of_not_vertex s.cube hs
  letI : Nonempty (KSLiveCurve.Live 1 s.coeff) := ⟨liveEquiv s.coeff ⟨0, hlive⟩⟩
  have hp := prepare_eq_of_exhausted C.η C.report s.coeff s.exhausted
  letI : Nonempty (KSLiveCurve.Live 1 (prepare C.η C.report s.coeff)) := by
    rw [hp]
    infer_instance
  have h := KSWeightedNegativeCurvature.exists_negative_second_after_prepare C.vectors
    C.δ_pos.le C.η_nonneg C.θ_pos C.report C.accuracy s.cube
  dsimp only at h
  rw [hp] at h
  exact h

end MatrixSpencer.KSPreparedNegativeCurvature
