import MatrixSpencer.KSCompactResolvent
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Topology.Order.ProjIcc

open Matrix MatrixSpencer Set Filter MeasureTheory
open scoped Topology Matrix.Norms.L2Operator unitInterval

noncomputable section
namespace HigherRankKS.WeightedCompactIntegral

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Compactified spectral parameter; the projection only specifies its
irrelevant values outside the positive half-line. -/
def parameter (t : ℝ) : I := Set.projIcc 0 1 zero_le_one (t / (1 + t))

theorem measurable_parameter : Measurable parameter :=
  continuous_projIcc.measurable.comp (measurable_id.div (measurable_const.add measurable_id))

theorem parameter_coe {t : ℝ} (ht : 0 < t) : (parameter t : ℝ) = t / (1 + t) := by
  have hp : 0 < 1 + t := by positivity
  have hm : t / (1 + t) ∈ Icc (0 : ℝ) 1 :=
    ⟨(div_pos ht hp).le, (div_le_one hp).mpr (by linarith)⟩
  simp only [parameter, Set.projIcc_of_mem zero_le_one hm]

theorem weighted_integrable (μ : Measure ℝ) (w : ℝ → ℝ) (hw : Integrable w μ)
    (F : C(I, Matrix n n ℂ)) : Integrable (fun t => w t • F (parameter t)) μ := by
  apply (hw.norm.mul_const ‖F‖).mono'
    (hw.aestronglyMeasurable.smul
      (F.continuous.comp_aestronglyMeasurable measurable_parameter.aestronglyMeasurable))
  filter_upwards [] with t
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (ContinuousMap.norm_coe_le_norm F _) (norm_nonneg _)

/-- Integration with an integrable scalar weight is a bounded linear
functional on continuous compact-parameter matrix functions. -/
def integralCLM (μ : Measure ℝ) (w : ℝ → ℝ) (hw : Integrable w μ) :
    C(I, Matrix n n ℂ) →L[ℝ] Matrix n n ℂ :=
  LinearMap.mkContinuous
    { toFun := fun F => ∫ t, w t • F (parameter t) ∂μ
      map_add' := by
        intro F G
        simp only [ContinuousMap.add_apply, smul_add]
        exact integral_add (weighted_integrable μ w hw F) (weighted_integrable μ w hw G)
      map_smul' := by
        intro r F
        simp only [ContinuousMap.smul_apply, smul_comm (w _) r]
        exact integral_smul r _ }
    (∫ t, ‖w t‖ ∂μ) (by
      intro F
      calc
        ‖∫ t, w t • F (parameter t) ∂μ‖ ≤ ∫ t, ‖w t • F (parameter t)‖ ∂μ :=
          norm_integral_le_integral_norm _
        _ ≤ ∫ t, ‖w t‖ * ‖F‖ ∂μ :=
          integral_mono (weighted_integrable μ w hw F).norm (hw.norm.mul_const ‖F‖)
            (by
              intro t
              change ‖w t • F (parameter t)‖ ≤ ‖w t‖ * ‖F‖
              rw [norm_smul]
              exact mul_le_mul_of_nonneg_left (ContinuousMap.norm_coe_le_norm F _) (norm_nonneg _))
        _ = (∫ t, ‖w t‖ ∂μ) * ‖F‖ := integral_mul_const ‖F‖ _)

@[simp] theorem integralCLM_apply (μ : Measure ℝ) (w : ℝ → ℝ) (hw : Integrable w μ)
    (F : C(I, Matrix n n ℂ)) :
    integralCLM μ w hw F = ∫ t, w t • F (parameter t) ∂μ := rfl

section LinearDifferentiation
variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Iterated actual derivatives commute with a continuous linear map. -/
theorem iteratedDeriv_clm (L : E →L[ℝ] G) {f : ℝ → E} {x : ℝ} {k : ℕ}
    (hf : ContDiffAt ℝ k f x) :
    iteratedDeriv k (fun s => L (f s)) x = L (iteratedDeriv k f x) := by
  have h := L.iteratedFDeriv_comp_left hf (i := k) le_rfl
  exact congrArg (fun A : ContinuousMultilinearMap ℝ (fun _ : Fin k => ℝ) G =>
    A (fun _ => 1)) h

end LinearDifferentiation

/-- Differentiating the compact-algebra curve justifies integration of
its actual pointwise derivatives, at every finite differentiability order. -/
theorem iteratedDeriv_integral (μ : Measure ℝ) (w : ℝ → ℝ) (hw : Integrable w μ)
    {F : ℝ → C(I, Matrix n n ℂ)} {s : ℝ} {k : ℕ} (hF : ContDiffAt ℝ k F s) :
    iteratedDeriv k (fun r => integralCLM μ w hw (F r)) s =
      ∫ t, w t • iteratedDeriv k (fun r => F r (parameter t)) s ∂μ := by
  rw [iteratedDeriv_clm _ hF, integralCLM_apply]
  apply integral_congr_ae
  filter_upwards [] with t
  congr 1
  exact (iteratedDeriv_clm (ContinuousMap.evalCLM ℝ (parameter t)) hF).symm

/-- The differentiated integrand is integrable because it is the
evaluation of a continuous compact-parameter derivative. -/
theorem integrable_iteratedDeriv (μ : Measure ℝ) (w : ℝ → ℝ) (hw : Integrable w μ)
    {F : ℝ → C(I, Matrix n n ℂ)} {s : ℝ} {k : ℕ} (hF : ContDiffAt ℝ k F s) :
    Integrable (fun t => w t • iteratedDeriv k (fun r => F r (parameter t)) s) μ := by
  have h := weighted_integrable μ w hw (iteratedDeriv k F s)
  apply h.congr
  filter_upwards [] with t
  congr 1
  exact (iteratedDeriv_clm (ContinuousMap.evalCLM ℝ (parameter t)) hF).symm

end HigherRankKS.WeightedCompactIntegral
