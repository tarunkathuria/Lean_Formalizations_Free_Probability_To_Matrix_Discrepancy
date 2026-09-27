import MatrixSpencer.MSManuscriptAdaptive

/-! Event statements for the actual finite output. Soundness identifies the
returned-output event with the event of returning a valid result. Positive
event mass gives an actual draw returning such a result. -/
open scoped BigOperators
noncomputable section
namespace MatrixSpencer.MSManuscriptAdaptive.Sampler
variable {α : Type*}
attribute [local instance] Classical.propDecidable

theorem valid_event_eq (P : Sampler (Option α)) (Q : α → Prop)
    (hQ : ∀ z a, P.value z = some a → Q a) :
    (∑ z, P.weight z * (if ∃ a, P.value z = some a ∧ Q a then (1 : ℝ) else 0)) =
      ∑ z, P.weight z * (if (P.value z).isSome then (1 : ℝ) else 0) := by
  classical
  apply Finset.sum_congr rfl
  intro z _
  cases hz : P.value z with
  | none => simp [hz]
  | some a => simp [hz, hQ z a hz]

theorem exists_return_of_positive_event (P : Sampler (Option α))
    (hp : 0 < ∑ z, P.weight z * (if (P.value z).isSome then (1 : ℝ) else 0)) :
    ∃ z a, P.value z = some a := by
  classical
  by_contra hn
  have hz : ∀ z, P.value z = none := by
    intro z
    cases h : P.value z with
    | none => rfl
    | some a => exact False.elim (hn ⟨z, a, h⟩)
  simp [hz] at hp

end MatrixSpencer.MSManuscriptAdaptive.Sampler
