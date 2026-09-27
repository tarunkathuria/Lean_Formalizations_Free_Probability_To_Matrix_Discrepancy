import MatrixSpencer.MSManuscriptComplexObjective
import MatrixSpencer.MSManuscriptComplexSourceNorm
import MatrixSpencer.KSComplexCompressionBounds
import MatrixSpencer.KSComplexObjectiveBound

/-! An explicit finite polynomial value cap for the actual holomorphic MS objective. -/

open Matrix Set Metric
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
noncomputable section
namespace MatrixSpencer.MSManuscriptComplexValueBound
open MSManuscriptComplexObjective MSManuscriptComplexSourceDomain KSCompactResolvent
variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
local instance {k : Type*} [Fintype k] [DecidableEq k] : CStarAlgebra (Matrix k k ℂ) := {}

theorem support_card_le (A : ι → Matrix n n ℂ) : Fintype.card (Support A) ≤ Fintype.card n := by
  simpa only [Support,Fintype.card_fin,finrank_euclideanSpace] using Submodule.finrank_le (krausSupport A)

def valueCap (ι n : Type*) [Fintype ι] [Fintype n] (R θ : ℝ) : ℝ :=
  KSComplexObjectiveBound.valueCap (Fintype.card n) R 2 (4*(Fintype.card ι : ℝ)^2) θ

theorem valueCap_nonneg {R θ : ℝ} (hR : 0 ≤ R) (hθ : 0 ≤ θ) : 0 ≤ valueCap ι n R θ :=
  KSComplexObjectiveBound.valueCap_nonneg _ hR (by norm_num) hθ

theorem radius_le_one {γ μ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hμ : 0 < μ) (hμ1 : μ ≤ 1) :
    radius γ μ ≤ 1 := by
  have hp := mul_le_mul hγ1 hμ1 hμ.le (by norm_num : (0:ℝ)≤1)
  unfold radius
  linarith

theorem objective_norm_le (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ)
    {θ R : ℝ} (hθ : 0 ≤ θ) (hR : 0 ≤ R) (hH : ‖H‖ ≤ R)
    (p : Space ι n) (hS : ‖p.2‖ ≤ 2)
    (hsource : ‖MSManuscriptComplexCovarianceSource.source A p.1 p.2‖ ≤ 4*(Fintype.card ι : ℝ)^2)
    (hprod : Domain (product A p)) (hdensity : Domain p.2) :
    ‖objective H A θ p‖ ≤ valueCap ι n R θ := by
  have hc : (Fintype.card (Support A) : ℝ) ≤ Fintype.card n := Nat.cast_le.mpr (support_card_le A)
  have hq := KSCompactTraceRoots.traceRoot_product_caps hprod
    ((KSComplexCompressionBounds.compression_norm_le _ (krausSupportEmbedding_isometry A) p.2).trans hS)
    ((KSComplexCompressionBounds.compression_norm_le _ (krausSupportEmbedding_isometry A) _).trans hsource)
  have hq' : ‖traceRoot (product A p)‖ ≤ (Fintype.card n : ℝ)*Real.sqrt (2*(4*(Fintype.card ι : ℝ)^2)) :=
    hq.trans (mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg _))
  have hr := (KSCompactTraceRoots.traceRoot_norm_le hdensity).trans
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hS) (Nat.cast_nonneg _))
  exact KSComplexObjectiveBound.value_norm_le H p.2 (traceRoot (product A p)) (traceRoot p.2)
    hθ hR hH hS hq' hr

/-- Primitive unit matrix caps and actual reference floors discharge every
source-domain and absolute-value premise on the explicit complex ball. -/
theorem objective_norm_le_on_ball (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ)
    (hA : ∀i, (A i).IsHermitian) (hAnorm : ∀i, ‖A i‖ ≤ 1)
    {θ R : ℝ} (hθ : 0 ≤ θ) (hR : 0 ≤ R) (hH : ‖H‖ ≤ R)
    {C₀ : Matrix ι ι ℝ} {S₀ : Matrix n n ℂ} {γ μ : ℝ}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (hC : γ • (1 : Matrix ι ι ℝ) ≤ C₀) (hC1 : C₀ ≤ 1)
    (hS : μ • (1 : Matrix n n ℂ) ≤ S₀) (hS1 : ‖S₀‖ ≤ 1)
    (p : Space ι n) (hp : p ∈ ball (realMatrixEmbedding C₀,S₀) (radius γ μ)) :
    ‖objective H A θ p‖ ≤ valueCap ι n R θ := by
  have hn : ‖p-(realMatrixEmbedding C₀,S₀)‖ < radius γ μ := by
    simpa only [mem_ball,dist_eq_norm] using hp
  have hc : ‖p.1-realMatrixEmbedding C₀‖ ≤ radius γ μ := (le_max_left _ _).trans hn.le
  have hs : ‖p.2-S₀‖ ≤ radius γ μ := (le_max_right _ _).trans hn.le
  have hr := radius_le_one hγ hγ1 hμ hμ1
  have hCp : C₀.PosSemidef := by
    have hh := (Matrix.PosDef.one.smul hγ).add_posSemidef (Matrix.le_iff.mp hC)
    exact (show C₀.PosDef by simpa only [add_sub_cancel] using hh).posSemidef
  have hS2 : ‖p.2‖ ≤ 2 := by
    have hh := norm_add_le (p.2-S₀) S₀
    rw [sub_add_cancel] at hh
    linarith [hs.trans hr]
  have hsource := MSManuscriptComplexSourceNorm.source_norm_le_four_card_sq A hAnorm
    (MSManuscriptComplexSourceNorm.real_coefficient_norm_le_one hCp hC1) hS1 (hc.trans hr) (hs.trans hr)
  have heC : realMatrixEmbedding C₀+(p.1-realMatrixEmbedding C₀)=p.1 := by abel
  have heS : S₀+(p.2-S₀)=p.2 := by abel
  rw [heC,heS] at hsource
  exact objective_norm_le H A hθ hR hH p hS2 hsource
    (product_domain A hA hγ hγ1 hμ hμ1 hC hS p hc hs) (density_domain hγ1 hμ hS hs)

end MatrixSpencer.MSManuscriptComplexValueBound
