import MatrixSpencer.MSManuscriptAdaptive

/-! Data maps and proof-only certificates for actual finite samples. -/
open scoped BigOperators
noncomputable section
namespace MatrixSpencer.MSManuscriptAdaptive.Sampler
variable {α β : Type*}

def map (P : Sampler α) (f : α → β) : Sampler β where
  Draws := P.Draws
  fintypeDraws := inferInstance
  weight := P.weight
  value z := f (P.value z)
  weight_nonneg := P.weight_nonneg
  weight_sum := P.weight_sum

@[simp] theorem expectation_map (P : Sampler α) (f : α → β) (g : β → ℝ) :
    (P.map f).expectation g = P.expectation (g ∘ f) := rfl

theorem failure_map (P : Sampler (Option α)) (f : α → β) :
    (P.map (Option.map f)).expectation MSManuscriptAdaptive.failure =
      P.expectation MSManuscriptAdaptive.failure := by
  unfold expectation
  apply Finset.sum_congr rfl
  intro z _
  change P.weight z * MSManuscriptAdaptive.failure ((P.value z).map f) = _
  cases P.value z <;> rfl

theorem map_option_sound (P : Sampler (Option α)) (f : α → β) (q : α → Prop) (r : β → Prop)
    (hq : ∀ z y, P.value z = some y → q y) (hf : ∀ y, q y → r (f y))
    (z : (P.map (Option.map f)).Draws) (y : β)
    (ho : (P.map (Option.map f)).value z = some y) : r y := by
  change (P.value z).map f = some y at ho
  obtain ⟨w, hw, hwy⟩ := Option.map_eq_some_iff.mp ho
  subst y
  exact hf w (hq z w hw)

def certify (P : Sampler (Option α)) (q : α → Prop)
    (hq : ∀ z y, P.value z = some y → q y) : Sampler (Option {y // q y}) where
  Draws := P.Draws
  fintypeDraws := inferInstance
  weight := P.weight
  value z := match he : P.value z with
    | none => none
    | some y => some ⟨y, hq z y he⟩
  weight_nonneg := P.weight_nonneg
  weight_sum := P.weight_sum

theorem certify_map_val (P : Sampler (Option α)) (q : α → Prop)
    (hq : ∀ z y, P.value z = some y → q y) (z : P.Draws) :
    ((P.certify q hq).value z).map Subtype.val = P.value z := by
  simp only [certify]
  split <;> simp_all

theorem failure_certify (P : Sampler (Option α)) (q : α → Prop)
    (hq : ∀ z y, P.value z = some y → q y) :
    (P.certify q hq).expectation MSManuscriptAdaptive.failure =
      P.expectation MSManuscriptAdaptive.failure := by
  unfold expectation
  apply Finset.sum_congr rfl
  intro z _
  simp only [certify]
  split <;> simp_all [MSManuscriptAdaptive.failure]

end MatrixSpencer.MSManuscriptAdaptive.Sampler
