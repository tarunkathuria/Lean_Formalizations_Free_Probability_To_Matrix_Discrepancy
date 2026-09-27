import MatrixSpencer.KSFrobeniusTangent
import MatrixSpencer.KSObjectiveUpper
import MatrixSpencer.KSCauchyRealBridge

/-!
# The actual KS density chart inside complex matrix coordinates

The time coordinate is embedded in ℂ and the trace-zero density coordinate
is embedded as its actual Hermitian matrix. The chart is a contraction from
the real product/Frobenius norm to the complex product/operator norm. Thus
the Cauchy-to-real derivative bridge applies to the optimizer coordinates
without an unstated norm equivalence or change of density space.
-/

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator ContDiff
noncomputable section
namespace MatrixSpencer.KSComplexEnvelopeChart

variable (n : Type*) [Fintype n] [DecidableEq n]
local instance : CStarAlgebra (Matrix n n ℂ) := {}

abbrev RealSpace := ℝ × KSFrobeniusTangent.Coordinates n
abbrev ComplexSpace := ℂ × Matrix n n ℂ

def densityEmbedding : KSFrobeniusTangent.Coordinates n →L[ℝ] Matrix n n ℂ :=
  hermitianInclusion.comp (KSFrobeniusTangent.embedding n)

theorem densityEmbedding_apply_norm_le (u : KSFrobeniusTangent.Coordinates n) :
    ‖densityEmbedding n u‖ ≤ ‖u‖ := by
  have h := KSObjectiveUpper.norm_sq_le_trace_square
    (show (densityEmbedding n u).IsHermitian from (KSFrobeniusTangent.embedding n u).property)
  change ‖densityEmbedding n u‖ ^ 2 ≤
    realTrace ((KSFrobeniusTangent.embedding n u : Matrix n n ℂ) *
      (KSFrobeniusTangent.embedding n u : Matrix n n ℂ)) at h
  rw [KSFrobeniusTangent.embedding_trace_square] at h
  nlinarith [norm_nonneg u, norm_nonneg (densityEmbedding n u)]

def jointEmbedding : RealSpace n →L[ℝ] ComplexSpace n :=
  Complex.ofRealCLM.prodMap (densityEmbedding n)

theorem jointEmbedding_apply (z : RealSpace n) :
    jointEmbedding n z = ((z.1 : ℂ), (KSFrobeniusTangent.embedding n z.2 : Matrix n n ℂ)) := rfl

theorem jointEmbedding_norm_le : ‖jointEmbedding n‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  simp only [one_mul, jointEmbedding_apply, Prod.norm_def, Complex.norm_real, Real.norm_eq_abs]
  exact max_le_max le_rfl (densityEmbedding_apply_norm_le n z.2)

theorem realPart_norm_le : ‖Complex.reCLM‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  simpa only [Complex.reCLM_apply, Real.norm_eq_abs, one_mul] using Complex.abs_re_le_norm z

variable [Nonempty n]

def base : ComplexSpace n := (0, (KSFrobeniusTangent.center n : Matrix n n ℂ))

theorem base_add_jointEmbedding (z : RealSpace n) :
    base n + jointEmbedding n z = ((z.1 : ℂ), (KSFrobeniusTangent.chart n z.2 : Matrix n n ℂ)) := by
  ext <;> simp [base, jointEmbedding_apply, KSFrobeniusTangent.chart]

/-- The actual trace-zero optimizer chart receives the generic Cauchy cap.
Only the extension's smoothness and value bound remain analytic premises. -/
theorem chart_derivatives_le_common_cap (F : ComplexSpace n → ℂ)
    {x : RealSpace n} {R K : ℝ} (hR : 0 < R) (hRone : R ≤ 1) (hK : 0 ≤ K)
    (hF : ContDiffOn ℂ ∞ F (Metric.ball (base n + jointEmbedding n x) R))
    (hbound : ∀ y ∈ Metric.ball (base n + jointEmbedding n x) R, ‖F y‖ ≤ K) :
    ∀ k : ℕ, 2 ≤ k → k ≤ 4 →
      ‖iteratedFDeriv ℝ k (fun z : RealSpace n =>
        (F ((z.1 : ℂ), (KSFrobeniusTangent.chart n z.2 : Matrix n n ℂ))).re) x‖ ≤ K * (10 / R) ^ 4 := by
  simpa only [base_add_jointEmbedding, Complex.reCLM_apply] using
    KSCauchyRealBridge.real_affine_chart_derivatives_le_common_cap
      (base n) (jointEmbedding n) Complex.reCLM hR hRone hK
      (jointEmbedding_norm_le n) realPart_norm_le hF hbound

end MatrixSpencer.KSComplexEnvelopeChart
