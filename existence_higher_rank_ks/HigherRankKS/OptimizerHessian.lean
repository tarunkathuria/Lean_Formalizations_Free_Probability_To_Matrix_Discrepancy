import HigherRankKS.OptimizerResponse
import MatrixSpencer.KSEnvelopeFourth
import HigherRankKS.SourceScalarMetric

/-! The actual envelope Hessian is the maximum of its full tangent
response quadratic. This is a consequence of differentiated stationarity
and the second-order chain rule, rather than a minimax assumption. -/

open MatrixSpencer Set Filter
open scoped Topology ContDiff

noncomputable section
namespace HigherRankKS.OptimizerHessian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem vertical_fderiv (F : ℝ × E → ℝ) (t : ℝ) (y : E)
    (hF : DifferentiableAt ℝ F (t, y)) :
    fderiv ℝ (fun z => F (t, z)) y =
      (fderiv ℝ F (t, y)).comp (ContinuousLinearMap.inr ℝ ℝ E) :=
  (hF.hasFDerivAt.comp y ((hasFDerivAt_const t y).prodMk (hasFDerivAt_id y))).fderiv

theorem vertical_hessian (F : ℝ × E → ℝ) (t : ℝ) (y v : E)
    (hF : ContDiffAt ℝ 2 F (t, y)) :
    fderiv ℝ (fderiv ℝ (fun z => F (t, z))) y v v =
      fderiv ℝ (fderiv ℝ F) (t, y) (0, v) (0, v) := by
  have hslice : ContDiffAt ℝ 2 (fun z => F (t, z)) y :=
    hF.comp y (contDiffAt_const.prodMk contDiffAt_id)
  rw [← SourceScalarMetric.iteratedDeriv_two_line _ y v hslice,
    ← SourceScalarMetric.iteratedDeriv_two_line F (t, y) (0, v) hF]
  congr 1
  funext a
  simp

/-- A stationary direction maximizes a quadratic whose vertical part is
negative semidefinite. The conclusion includes every vertical direction. -/
theorem response_quadratic_le
    (B : (ℝ × E) →L[ℝ] (ℝ × E) →L[ℝ] ℝ)
    (u : E) (hsym : ∀ v w, B v w = B w v)
    (hstat : ∀ v, B (1, u) (0, v) = 0)
    (hneg : ∀ v, B (0, v) (0, v) ≤ 0) (v : E) :
    B (1, v) (1, v) ≤ B (1, u) (1, u) := by
  have heq : ((1 : ℝ), v) = (1, u) + (0, v - u) := by ext <;> simp
  have hcross : B (0, v - u) (1, u) = 0 := by rw [hsym]; exact hstat _
  rw [heq]
  simp only [map_add, ContinuousLinearMap.add_apply, hstat, hcross]
  linarith [hneg (v - u)]

/-- The actual optimized second derivative equals the supremum of the
actual joint Hessian over the complete vertical tangent. -/
theorem envelope_second_eq_sup
    {I : Set ℝ} (hI : IsOpen I) (s : ℝ → E)
    (hs : ContDiffOn ℝ 4 s I) (F : ℝ × E → ℝ)
    (hF : ∀ t ∈ I, ContDiffAt ℝ 4 F (t, s t))
    (hstat : ∀ t ∈ I, ∀ v : E, fderiv ℝ F (t, s t) (0, v) = 0)
    {t : ℝ} (ht : t ∈ I)
    (hneg : ∀ v : E, fderiv ℝ (fderiv ℝ F) (t, s t) (0, v) (0, v) ≤ 0) :
    iteratedDeriv 2 (fun z => F (z, s z)) t =
      sSup (Set.range (fun v : E => fderiv ℝ (fderiv ℝ F) (t, s t) (1, v) (1, v))) := by
  have hvalue := KSEnvelopeFourth.value_second hI hs hF hstat ht
  change iteratedDeriv 2 (fun z => F (z, s z)) t =
    fderiv ℝ (fderiv ℝ F) (t, s t) (1, deriv s t) (1, deriv s t) at hvalue
  rw [hvalue]
  symm
  apply IsGreatest.csSup_eq
  refine ⟨⟨deriv s t, rfl⟩, ?_⟩
  rintro _ ⟨v, rfl⟩
  exact response_quadratic_le _ (deriv s t)
    (fun v w => ((hF t ht).isSymmSndFDerivAt (by norm_num)).eq v w)
    (fun v => KSEnvelopeFourth.stationary_second hI hs hF hstat ht v) hneg v

/-- A local smooth optimizing branch suffices for the exact response
supremum; the required open neighborhood is obtained from smoothness. -/
theorem envelope_second_eq_sup_at
    (s : ℝ → E) (hs : ContDiffAt ℝ ∞ s 0) (F : ℝ × E → ℝ)
    (hF : ContDiffAt ℝ ∞ F (0, s 0))
    (hstat : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ v : E, fderiv ℝ F (t, s t) (0, v) = 0)
    (hneg : ∀ v : E, fderiv ℝ (fderiv ℝ F) (0, s 0) (0, v) (0, v) ≤ 0) :
    iteratedDeriv 2 (fun z => F (z, s z)) 0 =
      sSup (Set.range (fun v : E => fderiv ℝ (fderiv ℝ F) (0, s 0) (1, v) (1, v))) := by
  have hs4 : ContDiffAt ℝ 4 s 0 := hs.of_le
    (WithTop.coe_le_coe.mpr (show (4 : ℕ∞) ≤ ⊤ from le_top))
  have hF4 : ContDiffAt ℝ 4 F (0, s 0) := hF.of_le
    (WithTop.coe_le_coe.mpr (show (4 : ℕ∞) ≤ ⊤ from le_top))
  have hgraph : Tendsto (fun t => (t, s t)) (𝓝 0) (𝓝 (0, s 0)) :=
    continuousAt_id.tendsto.prodMk_nhds hs.continuousAt.tendsto
  have hgood : ∀ᶠ t in 𝓝 (0 : ℝ), ContDiffAt ℝ 4 s t ∧ ContDiffAt ℝ 4 F (t, s t) ∧
      ∀ v : E, fderiv ℝ F (t, s t) (0, v) = 0 := by
    filter_upwards [hs4.eventually (by norm_num), hgraph.eventually (hF4.eventually (by norm_num)),
      hstat] with t hst hFt ht
    exact ⟨hst, hFt, ht⟩
  obtain ⟨I, hsub, hI, hzero⟩ := mem_nhds_iff.mp hgood
  exact envelope_second_eq_sup hI s (fun t ht => (hsub ht).1.contDiffWithinAt) F
    (fun t ht => (hsub ht).2.1) (fun t ht => (hsub ht).2.2) hzero hneg

end HigherRankKS.OptimizerHessian
