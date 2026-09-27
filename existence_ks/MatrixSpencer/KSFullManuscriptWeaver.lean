import MatrixSpencer.KSFullManuscriptExplicit
import MatrixSpencer.KSManuscriptWeaverTools


open Matrix
open scoped BigOperators Matrix.Norms.L2Operator InnerProductSpace
noncomputable section
namespace MatrixSpencer.KSFullManuscriptWeaver
open KSManuscriptWeaverTools
variable {N d : ℕ}

def Frame (w : Fin N → EuclideanSpace ℂ (Fin d)) : Prop :=
  ∀u : EuclideanSpace ℂ (Fin d), ‖u‖ = 1 → (∑i, ‖inner ℂ u (w i)‖^2) = eta

abbrev Draws (w : Fin N → EuclideanSpace ℂ (Fin d)) (hp : Frame w) (r : ℕ) :=
  KSFullManuscriptExplicit.Draws (scaled w) (scaled_parseval w hp) r

/-- Partition the original label set by the returned sign+1. -/
def output (w : Fin N → EuclideanSpace ℂ (Fin d)) (hp : Frame w) (r : ℕ)
    (z : Draws w hp r) : Option (Finset (Fin N)) :=
  (KSFullManuscriptExplicit.output (scaled w) (scaled_parseval w hp) r z).map positiveSet

def drawWeight (w : Fin N → EuclideanSpace ℂ (Fin d)) (hp : Frame w) (r : ℕ)
    (z : Draws w hp r) : ℝ :=
  KSFullManuscriptExplicit.drawWeight (scaled w) (scaled_parseval w hp) r z

theorem drawWeight_nonneg (w : Fin N → EuclideanSpace ℂ (Fin d)) (hp : Frame w)
    (r : ℕ) (z : Draws w hp r) : 0 ≤ drawWeight w hp r z :=
  KSFullManuscriptExplicit.drawWeight_nonneg _ _ r z

theorem drawWeight_sum (w : Fin N → EuclideanSpace ℂ (Fin d)) (hp : Frame w)
    (r : ℕ) : (∑z : Draws w hp r, drawWeight w hp r z) = 1 :=
  KSFullManuscriptExplicit.drawWeight_sum _ _ r

/-- Every returned partition satisfies the original energy bound for both classes. -/
theorem output_sound (w : Fin N → EuclideanSpace ℂ (Fin d)) (hp : Frame w)
    (hw : ∀i, ‖w i‖ ≤ 1) (r : ℕ) (z : Draws w hp r) (S : Finset (Fin N))
    (hout : output w hp r z = some S) :
    ∀u : EuclideanSpace ℂ (Fin d), ‖u‖ = 1 →
      (∑i ∈ S, ‖inner ℂ u (w i)‖^2) ≤ eta-theta ∧
      (∑i ∈ Sᶜ, ‖inner ℂ u (w i)‖^2) ≤ eta-theta := by
  obtain ⟨σ,hσ,hS⟩ := Option.map_eq_some_iff.mp hout
  subst S
  have hs := KSFullManuscriptExplicit.output_sound (scaled w) (scaled_parseval w hp)
    epsilon_pos.le (scaled_atom_size w hw) r z σ hσ
  apply partition_energy w hp σ hs.1
  have hroot : Real.sqrt epsilon = 1/1024 := by norm_num [epsilon]
  rw [hroot] at hs
  have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hn := Real.sqrt_nonneg (2 : ℝ)
  nlinarith [hs.2]

/-- The literal returned-partition event, under normalized actual draw weights. -/
theorem output_event_probability_ge (w : Fin N → EuclideanSpace ℂ (Fin d)) (hp : Frame w)
    (r : ℕ) : 1-(15/56 : ℝ)^r ≤ ∑z : Draws w hp r,
      drawWeight w hp r z * (if (output w hp r z).isSome then 1 else 0) := by
  simpa only [output,drawWeight,Option.isSome_map] using
    KSFullManuscriptExplicit.output_event_probability_ge (scaled w) (scaled_parseval w hp) r

theorem exists_output (w : Fin N → EuclideanSpace ℂ (Fin d)) (hp : Frame w) :
    ∃(z : Draws w hp 1) (S : Finset (Fin N)), output w hp 1 z = some S := by
  classical
  have ht := output_event_probability_ge w hp 1
  by_contra! hn
  have hz : ∀z : Draws w hp 1, output w hp 1 z = none := by
    intro z
    cases ho : output w hp 1 z with
    | none => rfl
    | some S => exact False.elim (hn z S ho)
  simp [hz] at ht
  norm_num at ht

/-- The original finite unit-energy assertion, from an actual successful walk. -/
theorem weaver_unit_energy (w : Fin N → EuclideanSpace ℂ (Fin d))
    (hw : ∀i, ‖w i‖ ≤ 1)
    (hp : ∀u : EuclideanSpace ℂ (Fin d), ‖u‖ = 1 → (∑i, ‖inner ℂ u (w i)‖^2) = eta) :
    ∃S : Finset (Fin N), ∀u : EuclideanSpace ℂ (Fin d), ‖u‖ = 1 →
      (∑i ∈ S, ‖inner ℂ u (w i)‖^2) ≤ eta-theta ∧
      (∑i ∈ Sᶜ, ‖inner ℂ u (w i)‖^2) ≤ eta-theta := by
  obtain ⟨z,S,ho⟩ := exists_output w hp
  exact ⟨S,output_sound w hp hw 1 z S ho⟩

/-- Weaver KS₂ with universal eta=1048576 and theta=262144. -/
theorem weaver_KS2 :
    ∃η θ : ℝ, 2 ≤ η ∧ 0 < θ ∧
      ∀(N d : ℕ) (w : Fin N → EuclideanSpace ℂ (Fin d)),
        (∀i, ‖w i‖ ≤ 1) →
        (∀u : EuclideanSpace ℂ (Fin d), ‖u‖ = 1 → (∑i, ‖inner ℂ u (w i)‖^2) = η) →
        ∃S : Finset (Fin N), ∀u : EuclideanSpace ℂ (Fin d), ‖u‖ = 1 →
          (∑i ∈ S, ‖inner ℂ u (w i)‖^2) ≤ η-θ ∧
          (∑i ∈ Sᶜ, ‖inner ℂ u (w i)‖^2) ≤ η-θ := by
  refine ⟨eta,theta,by norm_num [eta],by norm_num [theta],?_⟩
  intro N d w hw hp
  exact weaver_unit_energy w hw hp

end MatrixSpencer.KSFullManuscriptWeaver
