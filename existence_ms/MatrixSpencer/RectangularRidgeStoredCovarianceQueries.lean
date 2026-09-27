import MatrixSpencer.RectangularRidgeNumericalOptimizerFloor
import MatrixSpencer.RectangularRidgeCovarianceBudget
import MatrixSpencer.RectangularRidgePaidQueries

/-! The polynomial covariance-query cap from original matrix inputs, even
in a stored lower-rank coefficient frame and a singular physical source.
No optimizer-floor or derivative-bound hypothesis remains in the endpoint. -/
open Matrix Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
noncomputable section
namespace MatrixSpencer.RectangularRidgeStoredCovarianceQueries
open RectangularRidgePrimitiveParameters RectangularRidgeNumericalOptimizerFloor
open RectangularRidgeCovarianceQueries MSManuscriptGammaSmoothness
variable {N k d : ℕ} [Nonempty (Fin d)]
local instance ridgeStoredQueryCStar : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
local instance ridgeStoredQuerySpace : NormedSpace ℝ (selfAdjoint (Matrix (Fin d) (Fin d) ℂ)) := inferInstance
attribute [local irreducible] RectangularRidgePotential.optimizer
set_option maxHeartbeats 300000

theorem query_optimizer_floor (H : selfAdjoint (Matrix (Fin d) (Fin d) ℂ))
    (A : Fin N → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ i, (A i).IsHermitian)
    (hAn : ∀ i, ‖A i‖ ≤ 1) (U : Matrix (Fin N) (Fin k) ℝ)
    (hN : 1 ≤ N) (hND : N ≤ d) (hH : ‖(H : Matrix (Fin d) (Fin d) ℂ)‖ ≤ N)
    {C : Matrix (Fin k) (Fin k) ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hfloor : δ • (1 : Matrix (Fin k) (Fin k) ℝ) ≤ C)
    (hphysical : covarianceLift U C ≤ 1)
    (u : EuclideanSpace ℝ (Fin k)) (hu : ‖u‖=1) {a : ℝ} (ha : 0 ≤ a) (haδ : a < δ) :
    RectangularRidgeNumericalParameters.densityFloor (size d N) • (1 : Matrix (Fin d) (Fin d) ℂ) ≤
      RectangularRidgePotential.optimizer (H : Matrix (Fin d) (Fin d) ℂ)
        (covarianceKraus (mixFamily A U) (C-a • realRankOne (WithLp.ofLp u)))
        (RectangularRidgeTuning.depth N d hN) (weight N d hN) (1/(d : ℝ)) := by
  have hCa := (query_posDef hfloor ha haδ u hu).posSemidef
  have hcut : C-a • realRankOne (WithLp.ofLp u) ≤ C :=
    sub_le_self C ((realRankOne_posSemidef (WithLp.ofLp u)).smul ha).nonneg
  have hb := mixed_covariance_budget A hA hAn U hCa
    ((covarianceLift_mono U hcut).trans hphysical)
  simpa only [Fintype.card_fin] using optimizer_floor (H : Matrix (Fin d) (Fin d) ℂ)
    H.property _ hN (by simpa only [Fintype.card_fin] using hND) hH hb

/-- Input-derived polynomial bound on every real short covariance-query segment. -/
theorem query_second_le (H : selfAdjoint (Matrix (Fin d) (Fin d) ℂ))
    (A : Fin N → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ i, (A i).IsHermitian)
    (hAn : ∀ i, ‖A i‖ ≤ 1) (U : Matrix (Fin N) (Fin k) ℝ) (hU : Uᵀ*U=1)
    (hN : 1 ≤ N) (hND : N ≤ d) (hkN : k ≤ N)
    (hH : ‖(H : Matrix (Fin d) (Fin d) ℂ)‖ ≤ N)
    {C : Matrix (Fin k) (Fin k) ℝ} {δ : ℝ} (hδlow : ((2:ℝ)^14)⁻¹ ≤ δ) (hδ1 : δ ≤ 1)
    (hfloor : δ • (1 : Matrix (Fin k) (Fin k) ℝ) ≤ C) (hC1 : C ≤ 1)
    (hphysical : covarianceLift U C ≤ 1)
    (u : EuclideanSpace ℝ (Fin k)) (hu : ‖u‖ = 1) {a : ℝ} (ha : a ∈ Ioo 0 (δ/2)) :
    |iteratedDeriv 2 (curve (H : Matrix (Fin d) (Fin d) ℂ) (mixFamily A U) C
      (RectangularRidgeTuning.depth N d hN) (weight N d hN) (1/(d : ℝ)) u) a| ≤
        RectangularRidgeNumericalParameters.covarianceCap (size d N) := by
  let P := size d N
  let μ := RectangularRidgeNumericalParameters.densityFloor P
  have hd : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hP : 1 ≤ P := by dsimp [P,size]; linarith
  have hPN : (N : ℝ) ≤ P := by dsimp [P,size]; linarith
  have hPd : (d : ℝ) ≤ P := by dsimp [P,size]; linarith
  have hPk : (k : ℝ) ≤ P := (Nat.cast_le.mpr hkN).trans hPN
  have hδ : 0 < δ := lt_of_lt_of_le (by positivity) hδlow
  have hμ : 0 < μ := RectangularRidgeNumericalParameters.small_pos (by linarith) 10 6
  have hμ1 : μ ≤ 1 := RectangularRidgeNumericalParameters.small_le_one hP 10 6
  have hθ := weight_positive hN hND
  have hκ : 0 < 1/(d : ℝ) := by positivity
  have hopt := query_optimizer_floor H A hA hAn U hN hND hH hδ hfloor hphysical u hu ha.1.le (by linarith [ha.2])
  have hh := RectangularRidgeCovarianceQueries.query_second_le H (mixFamily A U)
    (mixFamily_isHermitian A U hA) (Nat.cast_nonneg N) (MSManuscriptFrameFamily.family_norm_le A hAn U hU)
    (RectangularRidgeTuning.depth N d hN) (RectangularRidgeTuning.depth_positive N d hN)
    hθ hκ hδ hδ1 hμ hμ1 hH hfloor hC1 u hu ha hopt
  apply hh.trans
  have hγ : ((2:ℝ)^15)⁻¹ ≤ δ/2 := by norm_num at hδlow ⊢; linarith
  have hiκ : P⁻¹ ≤ 1/(d : ℝ) := by
    rw [one_div]
    exact inv_anti₀ (by linarith) hPd
  exact RectangularRidgeCovarianceBudget.optimized_covariance_cap_le hP
    (by simpa only [Fintype.card_fin] using hPk) (by simpa only [Fintype.card_fin] using hPd)
    (Nat.cast_nonneg N) hPN (Nat.cast_nonneg N) hPN hγ (le_refl μ) hiκ

end MatrixSpencer.RectangularRidgeStoredCovarianceQueries
