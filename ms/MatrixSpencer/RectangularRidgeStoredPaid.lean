import MatrixSpencer.RectangularRidgeStoredCovarianceQueries

/-! Polynomial query precision and paid decrease from original contraction
inputs in a stored coefficient frame. These theorems discharge all optimizer,
derivative and Taylor bounds; only the numerical top direction's Rayleigh
condition enters the paid-cut theorem. -/
open Matrix Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
noncomputable section
namespace MatrixSpencer.RectangularRidgeStoredPaid
open RectangularRidgePrimitiveParameters RectangularRidgeNumericalOptimizerFloor
open RectangularRidgeCovarianceQueries RectangularRidgePaidQueries MSManuscriptGammaSmoothness
variable {N k d : ℕ} [Nonempty (Fin d)]
local instance ridgeStoredPaidCStar : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
local instance ridgeStoredPaidSpace : NormedSpace ℝ (selfAdjoint (Matrix (Fin d) (Fin d) ℂ)) := inferInstance
attribute [local irreducible] RectangularRidgePotential.optimizer
set_option maxHeartbeats 300000

variable (H : selfAdjoint (Matrix (Fin d) (Fin d) ℂ))
    (A : Fin N → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ i, (A i).IsHermitian)
    (hAn : ∀ i, ‖A i‖ ≤ 1) (U : Matrix (Fin N) (Fin k) ℝ) (hU : Uᵀ*U=1)
    (hN : 1 ≤ N) (hND : N ≤ d) (hkN : k ≤ N)
    (hH : ‖(H : Matrix (Fin d) (Fin d) ℂ)‖ ≤ N)
    {C : Matrix (Fin k) (Fin k) ℝ} {δ : ℝ} (hδlow : ((2:ℝ)^14)⁻¹ ≤ δ) (hδ1 : δ ≤ 1)
    (hfloor : δ • (1 : Matrix (Fin k) (Fin k) ℝ) ≤ C) (hC1 : C ≤ 1)
    (hphysical : covarianceLift U C ≤ 1)
    (u : EuclideanSpace ℝ (Fin k)) (hu : ‖u‖ = 1)

include hA hAn hU hND hkN hH hδlow hδ1 hfloor hC1 hphysical hu

theorem probe_accuracy {s : ℝ} (hs : 0 < s) (hsδ : s ≤ δ/4) :
    |probe (H : Matrix (Fin d) (Fin d) ℂ) (mixFamily A U) C
        (RectangularRidgeTuning.depth N d hN) (weight N d hN) (1/(d : ℝ)) s u -
      WithLp.ofLp u ⬝ᵥ (gram H (mixFamily A U) C
        (RectangularRidgeTuning.depth N d hN) (weight N d hN) (1/(d : ℝ)) *ᵥ WithLp.ofLp u)| ≤
      RectangularRidgeNumericalParameters.covarianceCap (size d N)*s/2 := by
  have hδ : 0 < δ := lt_of_lt_of_le (by positivity) hδlow
  have hd : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  let f := curve (H : Matrix (Fin d) (Fin d) ℂ) (mixFamily A U) C
    (RectangularRidgeTuning.depth N d hN) (weight N d hN) (1/(d : ℝ)) u
  have hf : ContDiffOn ℝ 2 f (Icc 0 s) := query_contDiffOn _ _ (mixFamily_isHermitian A U hA)
    _ (RectangularRidgeTuning.depth_positive N d hN) (weight_positive hN hND) (by positivity)
    hδ hfloor (by linarith) u hu
  have hder := curve_derivative_zero H (mixFamily A U) (mixFamily_isHermitian A U hA)
    (posDef_of_floor hδ hfloor) _ (RectangularRidgeTuning.depth_positive N d hN)
    (weight_positive hN hND) (by positivity : 0 < 1/(d : ℝ)) u
  have hsecond : ∀ a ∈ Ioo 0 s, |iteratedDeriv 2 f a| ≤
      RectangularRidgeNumericalParameters.covarianceCap (size d N) := by
    intro a ha
    exact RectangularRidgeStoredCovarianceQueries.query_second_le H A hA hAn U hU hN hND hkN hH
      hδlow hδ1 hfloor hC1 hphysical u hu ⟨ha.1,by linarith [ha.2]⟩
  have hh := MSManuscriptGammaDifference.negativeSlope_accuracy f f (ν := 0) hs hf hder hsecond
    (by simp) (by simp)
  simpa only [probe, f, mul_zero, zero_mul, zero_div, add_zero] using hh

/-- The actual finite query at the fixed polynomial difference scale. -/
theorem numerical_probe_accuracy :
    |probe (H : Matrix (Fin d) (Fin d) ℂ) (mixFamily A U) C
        (RectangularRidgeTuning.depth N d hN) (weight N d hN) (1/(d : ℝ))
        (RectangularRidgeNumericalParameters.differenceStep (size d N)) u -
      WithLp.ofLp u ⬝ᵥ (gram H (mixFamily A U) C
        (RectangularRidgeTuning.depth N d hN) (weight N d hN) (1/(d : ℝ)) *ᵥ WithLp.ofLp u)| ≤
      RectangularRidgeNumericalParameters.derivativeAccuracy (size d N)/8 := by
  let P := size d N
  have hd : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hP : 1 ≤ P := by dsimp [P,size]; linarith
  have hs : 0 < RectangularRidgeNumericalParameters.differenceStep P :=
    RectangularRidgeNumericalParameters.small_pos (by linarith) 322 62
  have hsδ : RectangularRidgeNumericalParameters.differenceStep P ≤ δ/4 := by
    have hh := RectangularRidgeNumericalParameters.differenceStep_le_floor hP
    norm_num at hδlow hh ⊢
    linarith
  have hh := probe_accuracy H A hA hAn U hU hN hND hkN hH hδlow hδ1 hfloor hC1 hphysical u hu hs hsδ
  have hb : RectangularRidgeNumericalParameters.covarianceCap P ≠ 0 :=
    (RectangularRidgeNumericalParameters.big_pos (by linarith) 300 60).ne'
  have he : RectangularRidgeNumericalParameters.covarianceCap P *
      RectangularRidgeNumericalParameters.differenceStep P/2 =
      RectangularRidgeNumericalParameters.derivativeAccuracy P/8 := by
    rw [RectangularRidgeNumericalParameters.differenceStep_accuracy]
    field_simp
    <;> ring
  exact hh.trans_eq he

/-- The literal real rank-one cut at the fixed polynomial paid scale decreases
the actual optimized mixed potential. -/
theorem numerical_paid_drop {price : ℝ} (hprice : 1 / size d N ≤ price)
    (hq : 7*price/8 ≤ WithLp.ofLp u ⬝ᵥ (gram H (mixFamily A U) C
      (RectangularRidgeTuning.depth N d hN) (weight N d hN) (1/(d : ℝ)) *ᵥ WithLp.ofLp u)) :
    RectangularRidgeCovarianceCalculus.ownerPotential (RectangularRidgeTuning.depth N d hN)
        H (mixFamily A U)
        (C-RectangularRidgeNumericalParameters.paidStep (size d N) • realRankOne (WithLp.ofLp u))
        (weight N d hN) (1/(d : ℝ)) +
        5*price*RectangularRidgeNumericalParameters.paidStep (size d N)/8 ≤
      RectangularRidgeCovarianceCalculus.ownerPotential (RectangularRidgeTuning.depth N d hN)
        H (mixFamily A U) C (weight N d hN) (1/(d : ℝ)) := by
  let P := size d N
  let α := RectangularRidgeNumericalParameters.paidStep P
  have hd : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hP : 1 ≤ P := by dsimp [P,size]; linarith
  have hδ : 0 < δ := lt_of_lt_of_le (by positivity) hδlow
  have hα : 0 < α := RectangularRidgeNumericalParameters.small_pos (by linarith) 320 62
  have hαδ : α ≤ δ/4 := by
    have hh := RectangularRidgeNumericalParameters.small_le_dyadic hP 320 62
    have hh' : α ≤ ((2:ℝ)^16)⁻¹ := hh.trans
      (inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) (show 16 ≤ 320 by omega)))
    norm_num at hδlow hh' ⊢
    linarith
  let f := curve (H : Matrix (Fin d) (Fin d) ℂ) (mixFamily A U) C
    (RectangularRidgeTuning.depth N d hN) (weight N d hN) (1/(d : ℝ)) u
  have hf : ContDiffOn ℝ 2 f (Icc 0 α) := query_contDiffOn _ _ (mixFamily_isHermitian A U hA)
    _ (RectangularRidgeTuning.depth_positive N d hN) (weight_positive hN hND) (by positivity)
    hδ hfloor (by linarith) u hu
  have hder := curve_derivative_zero H (mixFamily A U) (mixFamily_isHermitian A U hA)
    (posDef_of_floor hδ hfloor) _ (RectangularRidgeTuning.depth_positive N d hN)
    (weight_positive hN hND) (by positivity : 0 < 1/(d : ℝ)) u
  have hsecond : ∀ a ∈ Ioo 0 α, iteratedDeriv 2 f a ≤ RectangularRidgeNumericalParameters.covarianceCap P := by
    intro a ha
    exact (le_abs_self _).trans (RectangularRidgeStoredCovarianceQueries.query_second_le
      H A hA hAn U hU hN hND hkN hH hδlow hδ1 hfloor hC1 hphysical u hu
      ⟨ha.1,by linarith [ha.2]⟩)
  have hstep : RectangularRidgeNumericalParameters.covarianceCap P*α ≤ price/2 := by
    have hh := RectangularRidgeNumericalParameters.paidStep_curvature_budget hP
    change 2*RectangularRidgeNumericalParameters.covarianceCap P*α ≤ 1/P at hh
    linarith
  have hh := MSManuscriptPaidStep.paid_drop f hα hf hder hsecond hq hstep
  simp only [f,curve,zero_smul,sub_zero] at hh
  linarith

end MatrixSpencer.RectangularRidgeStoredPaid
