import MatrixSpencer.KSEnvelopeFourth

/-! Quantitative third derivative of a stationary envelope, retaining the cancellation. -/
noncomputable section
open MatrixSpencer Set Filter
open scoped Topology ContDiff
namespace AugmentedHigherRankKS.EnvelopeThird
open KSEnvelopeFourth
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
local instance : NormedAddCommGroup (Joint E →L[ℝ] Joint E →L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (Joint E →L[ℝ] Joint E →L[ℝ] ℝ) := inferInstance
local instance : NormedAddCommGroup (Joint E →L[ℝ] Joint E →L[ℝ] Joint E →L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (Joint E →L[ℝ] Joint E →L[ℝ] Joint E →L[ℝ] ℝ) := inferInstance

theorem value_second_le {I : Set ℝ} (hI : IsOpen I) (s : ℝ → E)
    (hs : ContDiffOn ℝ 4 s I) (F : ℝ × E → ℝ)
    (hF : ∀ t ∈ I, ContDiffAt ℝ 4 F (t, s t))
    (hstat : ∀ t ∈ I, ∀ v : E, fderiv ℝ F (t, s t) (0, v) = 0)
    {t : ℝ} (ht : t ∈ I) {μ B2 : ℝ} (hμ : 0 < μ) (hB2 : 0 ≤ B2)
    (h2 : ‖second F (t, s t)‖ ≤ B2)
    (hcoercive : ∀ v : E, μ * ‖v‖ ^ 2 ≤ -second F (t, s t) (0, v) (0, v)) :
    |iteratedDeriv 2 (fun z => F (z, s z)) t| ≤ B2 * (1 + B2 / μ) ^ 2 := by
  change |iteratedDeriv 2 (fun z => F (lift s z)) t| ≤ _
  rw [value_second hI hs hF hstat ht]
  have hn := norm_second_apply (second F (lift s t)) (velocity s t) (velocity s t)
  have hv := velocity_le hI hs hF hstat ht hμ hB2 h2 hcoercive
  calc
    _ ≤ ‖second F (lift s t)‖ * ‖velocity s t‖ * ‖velocity s t‖ := hn
    _ ≤ B2 * ‖velocity s t‖ * ‖velocity s t‖ := by
      gcongr
      exact h2
    _ = B2 * ‖velocity s t‖ ^ 2 := by ring
    _ ≤ _ := by gcongr

theorem value_third_le {I : Set ℝ} (hI : IsOpen I) (s : ℝ → E)
    (hs : ContDiffOn ℝ 4 s I) (F : ℝ × E → ℝ)
    (hF : ∀ t ∈ I, ContDiffAt ℝ 4 F (t, s t))
    (hstat : ∀ t ∈ I, ∀ v : E, fderiv ℝ F (t, s t) (0, v) = 0)
    {t : ℝ} (ht : t ∈ I) {μ B2 B3 : ℝ} (hμ : 0 < μ) (hB2 : 0 ≤ B2) (hB3 : 0 ≤ B3)
    (h2 : ‖second F (t, s t)‖ ≤ B2) (h3 : ‖third F (t, s t)‖ ≤ B3)
    (hcoercive : ∀ v : E, μ * ‖v‖ ^ 2 ≤ -second F (t, s t) (0, v) (0, v)) :
    |iteratedDeriv 3 (fun z => F (z, s z)) t| ≤ B3 * (1 + B2 / μ) ^ 3 := by
  change |iteratedDeriv 3 (fun z => F (lift s z)) t| ≤ _
  rw [value_third hI hs hF hstat ht]
  have hn := norm_third_apply (third F (lift s t)) (velocity s t) (velocity s t) (velocity s t)
  have hv := velocity_le hI hs hF hstat ht hμ hB2 h2 hcoercive
  calc
    _ ≤ ‖third F (lift s t)‖ * ‖velocity s t‖ * ‖velocity s t‖ * ‖velocity s t‖ := hn
    _ ≤ B3 * ‖velocity s t‖ * ‖velocity s t‖ * ‖velocity s t‖ := by
      gcongr
      exact h3
    _ = B3 * ‖velocity s t‖ ^ 3 := by ring
    _ ≤ _ := by gcongr

/-- Only a local smooth branch is needed, and coercivity is needed only at the base point. -/
theorem value_third_le_at (s : ℝ → E) (hs : ContDiffAt ℝ ∞ s 0) (F : ℝ × E → ℝ)
    (hF : ContDiffAt ℝ ∞ F (0, s 0))
    (hstat : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ v : E, fderiv ℝ F (t, s t) (0, v) = 0)
    {μ B2 B3 : ℝ} (hμ : 0 < μ) (hB2 : 0 ≤ B2) (hB3 : 0 ≤ B3)
    (h2 : ‖second F (0, s 0)‖ ≤ B2) (h3 : ‖third F (0, s 0)‖ ≤ B3)
    (hcoercive : ∀ v : E, μ * ‖v‖ ^ 2 ≤ -second F (0, s 0) (0, v) (0, v)) :
    |iteratedDeriv 3 (fun z => F (z, s z)) 0| ≤ B3 * (1 + B2 / μ) ^ 3 := by
  have hs4 : ContDiffAt ℝ 4 s 0 := hs.of_le
    (WithTop.coe_le_coe.mpr (show (4 : ℕ∞) ≤ ⊤ from le_top))
  have hF4 : ContDiffAt ℝ 4 F (0, s 0) := hF.of_le
    (WithTop.coe_le_coe.mpr (show (4 : ℕ∞) ≤ ⊤ from le_top))
  have hg : Tendsto (fun t => (t, s t)) (𝓝 0) (𝓝 (0, s 0)) :=
    continuousAt_id.tendsto.prodMk_nhds hs.continuousAt.tendsto
  have hgood : ∀ᶠ t in 𝓝 (0 : ℝ), ContDiffAt ℝ 4 s t ∧ ContDiffAt ℝ 4 F (t, s t) ∧
      ∀ v : E, fderiv ℝ F (t, s t) (0, v) = 0 := by
    filter_upwards [hs4.eventually (by norm_num), hg.eventually (hF4.eventually (by norm_num)),
      hstat] with t hst hFt ht
    exact ⟨hst, hFt, ht⟩
  obtain ⟨I, hsub, hI, hzero⟩ := mem_nhds_iff.mp hgood
  exact value_third_le hI s (fun t ht => (hsub ht).1.contDiffWithinAt) F
    (fun t ht => (hsub ht).2.1) (fun t ht => (hsub ht).2.2) hzero
    hμ hB2 hB3 h2 h3 hcoercive

theorem value_second_le_at (s : ℝ → E) (hs : ContDiffAt ℝ ∞ s 0) (F : ℝ × E → ℝ)
    (hF : ContDiffAt ℝ ∞ F (0, s 0))
    (hstat : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ v : E, fderiv ℝ F (t, s t) (0, v) = 0)
    {μ B2 : ℝ} (hμ : 0 < μ) (hB2 : 0 ≤ B2)
    (h2 : ‖second F (0, s 0)‖ ≤ B2)
    (hcoercive : ∀ v : E, μ * ‖v‖ ^ 2 ≤ -second F (0, s 0) (0, v) (0, v)) :
    |iteratedDeriv 2 (fun z => F (z, s z)) 0| ≤ B2 * (1 + B2 / μ) ^ 2 := by
  have hs4 : ContDiffAt ℝ 4 s 0 := hs.of_le
    (WithTop.coe_le_coe.mpr (show (4 : ℕ∞) ≤ ⊤ from le_top))
  have hF4 : ContDiffAt ℝ 4 F (0, s 0) := hF.of_le
    (WithTop.coe_le_coe.mpr (show (4 : ℕ∞) ≤ ⊤ from le_top))
  have hg : Tendsto (fun t => (t, s t)) (𝓝 0) (𝓝 (0, s 0)) :=
    continuousAt_id.tendsto.prodMk_nhds hs.continuousAt.tendsto
  have hgood : ∀ᶠ t in 𝓝 (0 : ℝ), ContDiffAt ℝ 4 s t ∧ ContDiffAt ℝ 4 F (t, s t) ∧
      ∀ v : E, fderiv ℝ F (t, s t) (0, v) = 0 := by
    filter_upwards [hs4.eventually (by norm_num), hg.eventually (hF4.eventually (by norm_num)),
      hstat] with t hst hFt ht
    exact ⟨hst, hFt, ht⟩
  obtain ⟨I, hsub, hI, hzero⟩ := mem_nhds_iff.mp hgood
  exact value_second_le hI s (fun t ht => (hsub ht).1.contDiffWithinAt) F
    (fun t ht => (hsub ht).2.1) (fun t ht => (hsub ht).2.2) hzero
    hμ hB2 h2 hcoercive

end AugmentedHigherRankKS.EnvelopeThird
