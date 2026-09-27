import MatrixSpencer.MSManuscriptPhaseProgress
import MatrixSpencer.MSManuscriptSamplerTools

/-! Finite adaptive half-phase assembly. The factory is instantiated by each
actual epoch sampler in the square and dyadic wrappers, not by selecting leaves. -/
open scoped BigOperators
noncomputable section
namespace MatrixSpencer.MSManuscriptPhase
open FiniteHalfPhase MSManuscriptAdaptive
variable {ι : Type*} [Fintype ι]

abbrev Point (ε : ℝ) := {x : EuclideanSpace ℝ ι // CubeRegular ε x}

structure Factory (potential : EuclideanSpace ℝ ι → ℝ) (ε τ B p : ℝ) where
  sample : ∀ (x : Point (ι := ι) ε), ¬Terminal x.val → Sampler (Option (Point (ι := ι) ε × ℝ))
  sound : ∀ x hx z y, (sample x hx).value z = some y →
    EpochAdvance potential τ B x.val y.1.val y.2
  failure_le : ∀ x hx, (sample x hx).expectation MSManuscriptAdaptive.failure ≤ p

variable {potential : EuclideanSpace ℝ ι → ℝ} {ε τ B p : ℝ}

def rawStep (F : Factory potential ε τ B p) (x : Point (ι := ι) ε) : Sampler (Option (Point (ι := ι) ε)) := by
  classical
  exact if hx : Terminal x.val then Sampler.pure (some x)
    else (F.sample x hx).map (Option.map Prod.fst)

theorem rawStep_sound (F : Factory potential ε τ B p) (hτ : 0 < τ)
    (hk : 0 < Fintype.card ι) (hB : 0 ≤ B) (x : Point (ι := ι) ε) (hx : ¬Terminal x.val) :
    ∀ z y, (rawStep F x).value z = some y →
      MSManuscriptPhaseProgress.progress τ x.val+1 ≤ MSManuscriptPhaseProgress.progress τ y.val ∧
      potential y.val ≤ potential x.val + B*Real.sqrt (Fintype.card ι : ℝ) := by
  classical
  unfold rawStep
  rw [dif_neg hx]
  intro z y ho
  change ((F.sample x hx).value z).map Prod.fst = some y at ho
  obtain ⟨w, hw, hwy⟩ := Option.map_eq_some_iff.mp ho
  subst y
  have ha := F.sound x hx z w hw
  exact ⟨MSManuscriptPhaseProgress.progress_advance hτ hk ha hx, ha.uniform_cost hB⟩

theorem rawStep_failure (F : Factory potential ε τ B p) (hp : 0 ≤ p)
    (x : Point (ι := ι) ε) : (rawStep F x).expectation MSManuscriptAdaptive.failure ≤ p := by
  classical
  unfold rawStep
  split_ifs with hx
  · simpa using hp
  · rw [Sampler.failure_map]
    exact F.failure_le x hx

def config (F : Factory potential ε τ B p) (hτ : 0 < τ) (hk : 0 < Fintype.card ι)
    (hB : 0 ≤ B) (hp : 0 ≤ p) (start : Point (ι := ι) ε) :
    MSManuscriptBoundedProcess.Config (Point (ι := ι) ε) where
  initial := start
  terminal x := Terminal x.val
  progress x := MSManuscriptPhaseProgress.progress τ x.val
  bound := 32/τ+128
  progress_nonneg x := MSManuscriptPhaseProgress.progress_nonneg hτ x.val
  progress_le x := MSManuscriptPhaseProgress.progress_le hτ hk x.property.1
  potential x := potential x.val
  cost := B*Real.sqrt (Fintype.card ι : ℝ)
  cost_nonneg := mul_nonneg hB (Real.sqrt_nonneg _)
  failureBound := p
  failure_nonneg := hp
  step := rawStep F
  step_sound := rawStep_sound F hτ hk hB
  step_failure x _ := rawStep_failure F hp x

def output (F : Factory potential ε τ B p) (hτ : 0 < τ) (hk : 0 < Fintype.card ι)
    (hB : 0 ≤ B) (hp : 0 ≤ p) (start : Point (ι := ι) ε) (K : ℕ) :=
  MSManuscriptBoundedProcess.output (config F hτ hk hB hp start) K

theorem output_sound (F : Factory potential ε τ B p) (hτ : 0 < τ) (hk : 0 < Fintype.card ι)
    (hB : 0 ≤ B) (hp : 0 ≤ p) (start : Point (ι := ι) ε) (K : ℕ)
    (hK : 32/τ+128 < (K:ℝ)) (z : (output F hτ hk hB hp start K).Draws)
    (y : Point (ι := ι) ε) (ho : (output F hτ hk hB hp start K).value z = some y) :
    Terminal y.val ∧ potential y.val ≤ potential start.val + B*(K:ℝ)*Real.sqrt (Fintype.card ι : ℝ) := by
  have h := MSManuscriptBoundedProcess.output_sound (config F hτ hk hB hp start) K hK z y ho
  change Terminal y.val ∧ potential y.val ≤ potential start.val + (K:ℝ)*(B*Real.sqrt (Fintype.card ι : ℝ)) at h
  refine ⟨h.1, h.2.trans_eq ?_⟩
  ring

theorem output_event_probability (F : Factory potential ε τ B p) (hτ : 0 < τ) (hk : 0 < Fintype.card ι)
    (hB : 0 ≤ B) (hp : 0 ≤ p) (start : Point (ι := ι) ε) (K : ℕ) :
    1-(K:ℝ)*p ≤ ∑ z, (output F hτ hk hB hp start K).weight z *
      (if ((output F hτ hk hB hp start K).value z).isSome then 1 else 0) :=
  MSManuscriptBoundedProcess.output_event_probability (config F hτ hk hB hp start) K

end MatrixSpencer.MSManuscriptPhase
