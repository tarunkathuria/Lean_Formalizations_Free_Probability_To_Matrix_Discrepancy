import HigherRankKS.SourceDerivatives
import HigherRankKS.WeightedCompactIntegral

open scoped Topology ContDiff
noncomputable section
namespace HigherRankKS.LinearDerivative
variable {E F G H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Actual derivatives commute with fixed linear input and output maps. -/
theorem first (L : E →L[ℝ] F) (R : G →L[ℝ] H) (f : F → G) (x u : E)
    (hf : DifferentiableAt ℝ f (L x)) :
    fderiv ℝ (fun y => R (f (L y))) x u = R (fderiv ℝ f (L x) (L u)) := by
  exact DFunLike.congr_fun (R.hasFDerivAt.comp x (hf.hasFDerivAt.comp x L.hasFDerivAt)).fderiv u

/-- The actual diagonal second derivative commutes with fixed linear maps. -/
theorem second (L : E →L[ℝ] F) (R : G →L[ℝ] H) (f : F → G) (x u : E)
    (hf : ContDiffAt ℝ 2 f (L x)) :
    fderiv ℝ (fderiv ℝ (fun y => R (f (L y)))) x u u =
      R (fderiv ℝ (fderiv ℝ f) (L x) (L u) (L u)) := by
  have hg : ContDiffAt ℝ 2 (fun y => R (f (L y))) x :=
    R.contDiff.contDiffAt.comp x (hf.comp x L.contDiff.contDiffAt)
  rw [← SourceDerivatives.iteratedDeriv_two_line_vector _ x u hg]
  have heq : (fun t : ℝ => R (f (L (x + t • u)))) =
      (fun t => R (f (L x + t • L u))) := by simp only [map_add, map_smul]
  rw [heq, WeightedCompactIntegral.iteratedDeriv_clm R]
  · rw [SourceDerivatives.iteratedDeriv_two_line_vector f (L x) (L u) hf]
  · have hb : ContDiffAt ℝ 2 f (L x + (0 : ℝ) • L u) := by simpa using hf
    exact hb.comp 0 (f := fun t : ℝ => L x + t • L u) (by fun_prop)

end HigherRankKS.LinearDerivative
