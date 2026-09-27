import MatrixSpencer.MSManuscriptGammaMatrix
import MatrixSpencer.MSManuscriptPaidStep

/-!
# Smoothness of the actual numerical covariance-query segments

A positive coefficient floor supplies the range, positivity and smoothness
premises of the finite-difference query. This module does not claim a numerical
curvature cap; its remaining bound is displayed explicitly in the final bridge.
-/

open Matrix Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
noncomputable section
namespace MatrixSpencer.MSManuscriptGammaSmoothness
open MSManuscriptGammaDifference MSManuscriptGammaMatrix MSManuscriptPaidStep
variable {k d : ℕ}
local instance : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
set_option maxHeartbeats 1200000
attribute [local irreducible] ownerPotential observedOwnedGram

theorem posDef_of_floor {C : Matrix (Fin k) (Fin k) ℝ} {δ : ℝ}
    (hδ : 0 < δ) (hfloor : δ • (1 : Matrix (Fin k) (Fin k) ℝ) ≤ C) : C.PosDef := by
  have hp := (Matrix.PosDef.one.smul hδ).add_posSemidef (Matrix.le_iff.mp hfloor)
  simpa only [add_sub_cancel] using hp

theorem unit_rank_le_one (u : EuclideanSpace ℝ (Fin k)) (hu : ‖u‖ = 1) :
    realRankOne (WithLp.ofLp u) ≤ (1 : Matrix (Fin k) (Fin k) ℝ) := by
  rw [← unitRank_of_norm_one u hu]
  apply unitRank_le_projection Matrix.PosSemidef.one.isHermitian (Matrix.one_mul _)
  · intro he
    have hz : u = 0 := by exact WithLp.ofLp_injective 2 he
    rw [hz, norm_zero] at hu
    norm_num at hu
  · simp

theorem query_floor {C : Matrix (Fin k) (Fin k) ℝ} {δ a : ℝ}
    (hfloor : δ • (1 : Matrix (Fin k) (Fin k) ℝ) ≤ C) (ha : 0 ≤ a)
    (u : EuclideanSpace ℝ (Fin k)) (hu : ‖u‖ = 1) :
    (δ-a) • (1 : Matrix (Fin k) (Fin k) ℝ) ≤ C-a • realRankOne (WithLp.ofLp u) := by
  simpa only [cut, unitRank_of_norm_one u hu] using
    cut_floor hfloor ha (show unitRank (WithLp.ofLp u) ≤ 1 by
      rw [unitRank_of_norm_one u hu]; exact unit_rank_le_one u hu)

theorem query_posDef {C : Matrix (Fin k) (Fin k) ℝ} {δ a : ℝ}
    (hfloor : δ • (1 : Matrix (Fin k) (Fin k) ℝ) ≤ C) (ha : 0 ≤ a) (haδ : a < δ)
    (u : EuclideanSpace ℝ (Fin k)) (hu : ‖u‖ = 1) :
    (C-a • realRankOne (WithLp.ofLp u)).PosDef :=
  posDef_of_floor (sub_pos.mpr haδ) (query_floor hfloor ha u hu)

theorem range_mem_of_posDef {C : Matrix (Fin k) (Fin k) ℝ} (hC : C.PosDef)
    (u : EuclideanSpace ℝ (Fin k)) :
    u ∈ LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℝ) C).toLinearMap := by
  refine ⟨WithLp.toLp 2 (C⁻¹ *ᵥ WithLp.ofLp u), ?_⟩
  apply WithLp.ofLp_injective
  change C *ᵥ (C⁻¹ *ᵥ WithLp.ofLp u) = WithLp.ofLp u
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
    (C.isUnit_iff_isUnit_det.mp hC.isUnit), Matrix.one_mulVec]

theorem curve_contDiffAt [Nonempty (Fin d)]
    (H : Matrix (Fin d) (Fin d) ℂ) (A : Fin k → Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀ i, (A i).IsHermitian) {C : Matrix (Fin k) (Fin k) ℝ}
    (hC : C.IsHermitian) {θ a : ℝ} (hθ : 0 < θ)
    (u : EuclideanSpace ℝ (Fin k)) (hCa : (C-a • realRankOne (WithLp.ofLp u)).PosDef) :
    ContDiffAt ℝ ∞ (curve H A C θ u) a := by
  let Cs : selfAdjoint (Matrix (Fin k) (Fin k) ℝ) := ⟨C,hC⟩
  let R := hermitianRankOne (WithLp.ofLp u)
  have hpath : ContDiff ℝ ∞ (fun t : ℝ => Cs-t • R) := contDiff_const.sub (contDiff_id.smul contDiff_const)
  have hp := contDiffAt_hermitianOwnerPotential H A hA hθ (Cs-a • R) hCa
  exact hp.comp a hpath.contDiffAt

theorem query_contDiffOn [Nonempty (Fin d)]
    (H : Matrix (Fin d) (Fin d) ℂ) (A : Fin k → Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀ i, (A i).IsHermitian) {C : Matrix (Fin k) (Fin k) ℝ}
    {θ δ s : ℝ} (hθ : 0 < θ) (hδ : 0 < δ)
    (hfloor : δ • (1 : Matrix (Fin k) (Fin k) ℝ) ≤ C) (hsδ : s < δ)
    (u : EuclideanSpace ℝ (Fin k)) (hu : ‖u‖ = 1) :
    ContDiffOn ℝ 2 (curve H A C θ u) (Icc 0 s) := by
  intro a ha
  exact ((curve_contDiffAt H A hA (posDef_of_floor hδ hfloor).isHermitian hθ u
    (query_posDef hfloor ha.1 (ha.2.trans_lt hsδ) u hu)).of_le
      (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))).contDiffWithinAt

/-- The sole remaining query obligation is the displayed quantitative bound
on the actual second derivative. The range, PSD and C² hypotheses are derived. -/
theorem querySegments_of_second_bound [Nonempty (Fin d)]
    (H : Matrix (Fin d) (Fin d) ℂ) (A : Fin k → Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀ i, (A i).IsHermitian) {C : Matrix (Fin k) (Fin k) ℝ}
    {θ δ L η : ℝ} (hθ : 0 < θ) (hδ : 0 < δ) (hL : 0 ≤ L) (hη : 0 < η)
    (hfloor : δ • (1 : Matrix (Fin k) (Fin k) ℝ) ≤ C)
    (hsecond : ∀ u : EuclideanSpace ℝ (Fin k), ‖u‖ = 1 →
      ∀ a ∈ Ioo 0 (stepSize δ L η), |iteratedDeriv 2 (curve H A C θ u) a| ≤ L) :
    QuerySegments H A C θ (stepSize δ L η) L := by
  have hsδ : stepSize δ L η < δ :=
    (min_le_left (δ/4) (η/(L+1))).trans_lt (by linarith)
  intro u hu
  exact ⟨range_mem_of_posDef (posDef_of_floor hδ hfloor) u,
    (query_posDef hfloor (stepSize_pos hδ hL hη).le hsδ u hu).posSemidef,
    query_contDiffOn H A hA hθ hδ hfloor hsδ u hu, hsecond u hu⟩

theorem report_accuracy_of_floor [Nonempty (Fin d)]
    (H : selfAdjoint (Matrix (Fin d) (Fin d) ℂ))
    (A : Fin k → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C : Matrix (Fin k) (Fin k) ℝ} {θ δ L η : ℝ}
    (hθ : 0 < θ) (hδ : 0 < δ) (hL : 0 ≤ L) (hη : 0 < η) (hd : 0 < d)
    (hfloor : δ • (1 : Matrix (Fin k) (Fin k) ℝ) ≤ C)
    (hsecond : ∀ u : EuclideanSpace ℝ (Fin k), ‖u‖ = 1 →
      ∀ a ∈ Ioo 0 (stepSize δ L η),
        |iteratedDeriv 2 (curve (H : Matrix (Fin d) (Fin d) ℂ) A C θ u) a| ≤ L) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ)
      (observedOwnedGram H A C θ-report (H : Matrix (Fin d) (Fin d) ℂ) A C θ hd δ L η)‖ ≤
        (k : ℝ)*(2*η) :=
  report_accuracy H A hA (posDef_of_floor hδ hfloor).posSemidef hθ hδ hL hη hd
    (querySegments_of_second_bound (H : Matrix (Fin d) (Fin d) ℂ) A hA hθ hδ hL hη hfloor hsecond)

end MatrixSpencer.MSManuscriptGammaSmoothness
