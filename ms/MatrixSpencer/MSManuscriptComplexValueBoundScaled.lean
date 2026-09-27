import MatrixSpencer.MSManuscriptComplexObjective
import MatrixSpencer.MSManuscriptComplexSourceNorm
import MatrixSpencer.KSComplexCompressionBounds
import MatrixSpencer.KSComplexObjectiveBound

/-! The actual MS complex objective with arbitrary finite input norm scale L. -/

open Matrix Set Metric
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
noncomputable section
namespace MatrixSpencer.MSManuscriptComplexValueBoundScaled
open MSManuscriptComplexObjective MSManuscriptComplexSourceDomain KSCompactResolvent
variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
local instance {k : Type*} [Fintype k] [DecidableEq k] : CStarAlgebra (Matrix k k ℂ) := {}

/-- Finite entry summation; no source positivity is needed for this cap. -/
theorem source_norm_le (A : ι → Matrix n n ℂ) {L : ℝ} (hL : 0 ≤ L)
    (hA : ∀i, ‖A i‖ ≤ L) (C : Matrix ι ι ℂ) (S : Matrix n n ℂ) :
    ‖MSManuscriptComplexCovarianceSource.source A C S‖ ≤
      (Fintype.card ι : ℝ)^2*L^2*‖C‖*‖S‖ := by
  have ht (i j : ι) : ‖C i j • (A i*S*A j)‖ ≤ L^2*‖C‖*‖S‖ := by
    have hh := (norm_mul_le (A i*S) (A j)).trans
      (mul_le_mul_of_nonneg_right (norm_mul_le (A i) S) (norm_nonneg _))
    have hn : ‖A i‖*‖S‖*‖A j‖ ≤ L*‖S‖*L :=
      mul_le_mul (mul_le_mul_of_nonneg_right (hA i) (norm_nonneg S)) (hA j)
        (norm_nonneg _) (mul_nonneg hL (norm_nonneg S))
    rw [norm_smul]
    calc
      _ ≤ ‖C‖*(L*‖S‖*L) := mul_le_mul (KSObjectiveValueBound.entry_norm_le C i j)
        (hh.trans hn) (norm_nonneg _) (norm_nonneg C)
      _ = _ := by ring
  calc
    _ ≤ ∑i, ‖∑j, C i j • (A i*S*A j)‖ := norm_sum_le _ _
    _ ≤ ∑i, ∑j, ‖C i j • (A i*S*A j)‖ := Finset.sum_le_sum (fun i _ => norm_sum_le _ _)
    _ ≤ ∑i : ι, ∑j : ι, L^2*‖C‖*‖S‖ :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ht i j))
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring

theorem source_norm_le_of_caps (A : ι → Matrix n n ℂ) {L : ℝ} (hL : 0 ≤ L)
    (hA : ∀i, ‖A i‖ ≤ L) {C : Matrix ι ι ℂ} {S : Matrix n n ℂ} {c s : ℝ}
    (hc : ‖C‖ ≤ c) (hs : ‖S‖ ≤ s) :
    ‖MSManuscriptComplexCovarianceSource.source A C S‖ ≤
      (Fintype.card ι : ℝ)^2*L^2*c*s := by
  have hh := mul_le_mul_of_nonneg_left (mul_le_mul hc hs (norm_nonneg S) ((norm_nonneg C).trans hc))
    (mul_nonneg (sq_nonneg (Fintype.card ι : ℝ)) (sq_nonneg L))
  exact (source_norm_le A hL hA C S).trans (by nlinarith)

theorem support_card_le (A : ι → Matrix n n ℂ) : Fintype.card (Support A) ≤ Fintype.card n := by
  simpa only [Support,Fintype.card_fin,finrank_euclideanSpace] using Submodule.finrank_le (krausSupport A)

def valueCap (ι n : Type*) [Fintype ι] [Fintype n] (R θ L : ℝ) : ℝ :=
  KSComplexObjectiveBound.valueCap (Fintype.card n) R 2 (4*(Fintype.card ι : ℝ)^2*L^2) θ

theorem valueCap_nonneg {R θ L : ℝ} (hR : 0 ≤ R) (hθ : 0 ≤ θ) : 0 ≤ valueCap ι n R θ L :=
  KSComplexObjectiveBound.valueCap_nonneg _ hR (by norm_num) hθ

theorem radius_le_one {γ μ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hμ : 0 < μ) (hμ1 : μ ≤ 1) :
    radius γ μ ≤ 1 := by
  have hp := mul_le_mul hγ1 hμ1 hμ.le (by norm_num : (0:ℝ)≤1)
  unfold radius
  linarith

theorem objective_norm_le (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ)
    {θ R L : ℝ} (hθ : 0 ≤ θ) (hR : 0 ≤ R) (hH : ‖H‖ ≤ R)
    (p : Space ι n) (hS : ‖p.2‖ ≤ 2)
    (hsource : ‖MSManuscriptComplexCovarianceSource.source A p.1 p.2‖ ≤ 4*(Fintype.card ι : ℝ)^2*L^2)
    (hprod : Domain (product A p)) (hdensity : Domain p.2) :
    ‖objective H A θ p‖ ≤ valueCap ι n R θ L := by
  have hc : (Fintype.card (Support A) : ℝ) ≤ Fintype.card n := Nat.cast_le.mpr (support_card_le A)
  have hq := KSCompactTraceRoots.traceRoot_product_caps hprod
    ((KSComplexCompressionBounds.compression_norm_le _ (krausSupportEmbedding_isometry A) p.2).trans hS)
    ((KSComplexCompressionBounds.compression_norm_le _ (krausSupportEmbedding_isometry A) _).trans hsource)
  have hq' : ‖traceRoot (product A p)‖ ≤ (Fintype.card n : ℝ)*Real.sqrt (2*(4*(Fintype.card ι : ℝ)^2*L^2)) :=
    hq.trans (mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg _))
  have hr := (KSCompactTraceRoots.traceRoot_norm_le hdensity).trans
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hS) (Nat.cast_nonneg _))
  exact KSComplexObjectiveBound.value_norm_le H p.2 (traceRoot (product A p)) (traceRoot p.2)
    hθ hR hH hS hq' hr

/-- Primitive unit matrix caps and actual reference floors discharge every
source-domain and absolute-value premise on the explicit complex ball. -/
theorem objective_norm_le_on_ball (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ)
    (hA : ∀i, (A i).IsHermitian) {L : ℝ} (hL : 0 ≤ L) (hAnorm : ∀i, ‖A i‖ ≤ L)
    {θ R : ℝ} (hθ : 0 ≤ θ) (hR : 0 ≤ R) (hH : ‖H‖ ≤ R)
    {C₀ : Matrix ι ι ℝ} {S₀ : Matrix n n ℂ} {γ μ : ℝ}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (hC : γ • (1 : Matrix ι ι ℝ) ≤ C₀) (hC1 : C₀ ≤ 1)
    (hS : μ • (1 : Matrix n n ℂ) ≤ S₀) (hS1 : ‖S₀‖ ≤ 1)
    (p : Space ι n) (hp : p ∈ ball (realMatrixEmbedding C₀,S₀) (radius γ μ)) :
    ‖objective H A θ p‖ ≤ valueCap ι n R θ L := by
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
  have hC2 : ‖p.1‖ ≤ 2 := by
    have hh := norm_add_le (p.1-realMatrixEmbedding C₀) (realMatrixEmbedding C₀)
    rw [sub_add_cancel] at hh
    linarith [hc.trans hr, MSManuscriptComplexSourceNorm.real_coefficient_norm_le_one hCp hC1]
  have hsource := source_norm_le_of_caps A hL hAnorm hC2 hS2
  have he : (Fintype.card ι : ℝ)^2*L^2*2*2 = 4*(Fintype.card ι : ℝ)^2*L^2 := by ring
  rw [he] at hsource
  exact objective_norm_le H A hθ hR hH p hS2 hsource
    (product_domain A hA hγ hγ1 hμ hμ1 hC hS p hc hs) (density_domain hγ1 hμ hS hs)

end MatrixSpencer.MSManuscriptComplexValueBoundScaled
