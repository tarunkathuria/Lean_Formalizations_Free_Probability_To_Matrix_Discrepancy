import MatrixSpencer.RectangularRidgeSymmetricQueries
import MatrixSpencer.RectangularRidgeStoredGamma

/-! The supported response matrix computed from accurate SDP values. Unlike
the exact-value comparison routine, this definition performs two solver calls
per directional difference, at the proved polynomial precision. All analytic
and finite-difference errors are included in the final operator bound. -/

open Matrix Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
noncomputable section
namespace MatrixSpencer.RectangularRidgeSolverGamma
open RectangularRidgePrimitiveParameters RectangularRidgeNumericalOptimizerFloor
open RectangularRidgeNumericalParameters MSManuscriptGammaSmoothness
variable {N k d : ℕ} [Nonempty (Fin d)]
local instance ridgeSolverGammaCStar : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
local instance ridgeSolverGammaSpace : NormedSpace ℝ (selfAdjoint (Matrix (Fin d) (Fin d) ℂ)) := inferInstance
set_option maxHeartbeats 400000

theorem slope_perturbation (f g : ℝ → ℝ) {s ν : ℝ} (hs : 0<s)
    (h0 : |g 0-f 0|≤ν) (h1 : |g s-f s|≤ν) :
    |MSManuscriptGammaDifference.negativeSlope g s-
      MSManuscriptGammaDifference.negativeSlope f s|≤2*ν/s := by
  have h : |(g 0-g s)-(f 0-f s)|≤2*ν := by
    have hp := abs_sub (g 0-f 0) (g s-f s)
    have he : (g 0-g s)-(f 0-f s)=(g 0-f 0)-(g s-f s) := by ring
    rw [he]
    linarith
  unfold MSManuscriptGammaDifference.negativeSlope
  rw [← sub_div, abs_div, abs_of_pos hs]
  exact div_le_div_of_nonneg_right h hs.le

def valueCurve (O : RectangularRidgeConvexValue.Solver) (m : ℕ) (hm : 1≤m) (a : Fin d)
    (H : Matrix (Fin d) (Fin d) ℂ) (A : Fin k → Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀ i, (A i).IsHermitian) (C : selfAdjoint (Matrix (Fin k) (Fin k) ℝ))
    (θ κ ν : ℝ) (u : EuclideanSpace ℝ (Fin k)) (t : ℝ) : ℝ :=
  RectangularRidgeSymmetricQueries.report O m hm a H A hA
    (C-t • hermitianRankOne (WithLp.ofLp u)) θ κ ν

def probe (O : RectangularRidgeConvexValue.Solver) (m : ℕ) (hm : 1≤m) (a : Fin d)
    (H : Matrix (Fin d) (Fin d) ℂ) (A : Fin k → Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀ i, (A i).IsHermitian) (C : selfAdjoint (Matrix (Fin k) (Fin k) ℝ))
    (θ κ s ν : ℝ) (u : EuclideanSpace ℝ (Fin k)) : ℝ :=
  MSManuscriptGammaDifference.negativeSlope (valueCurve O m hm a H A hA C θ κ ν u) s

theorem probe_perturbation (O : RectangularRidgeConvexValue.Solver)
    (m : ℕ) (hm : 1≤m) (a : Fin d) (H : Matrix (Fin d) (Fin d) ℂ)
    (A : Fin k → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ i, (A i).IsHermitian)
    (C : selfAdjoint (Matrix (Fin k) (Fin k) ℝ))
    {θ κ s ν : ℝ} (hθ : 0<θ) (hκ : 0≤κ) (hs : 0<s) (hν : 0<ν)
    (u : EuclideanSpace ℝ (Fin k)) (hC : (C : Matrix (Fin k) (Fin k) ℝ).PosSemidef)
    (hCs : ((C : Matrix (Fin k) (Fin k) ℝ)-s • realRankOne (WithLp.ofLp u)).PosSemidef) :
    |probe O m hm a H A hA C θ κ s ν u-
      RectangularRidgePaidQueries.probe H A C m θ κ s u|≤2*ν/s := by
  apply slope_perturbation _ _ hs
  · have hh := RectangularRidgeSymmetricQueries.report_accuracy O m hm a H A hA C hC hθ hκ hν
    simpa only [valueCurve, zero_smul, sub_zero, RectangularRidgeCovarianceQueries.curve,
      RectangularRidgeCovarianceCalculus.ownerPotential_eq_densityPotential m H A hA hC] using hh
  · have hh := RectangularRidgeSymmetricQueries.report_accuracy O m hm a H A hA
      (C-s • hermitianRankOne (WithLp.ofLp u)) hCs hθ hκ hν
    simpa only [valueCurve, RectangularRidgeCovarianceQueries.curve,
      RectangularRidgeCovarianceCalculus.ownerPotential_eq_densityPotential m H A hA hCs,
      Submodule.coe_sub, Submodule.coe_smul_of_tower, hermitianRankOne] using hh

variable (O : RectangularRidgeConvexValue.Solver) (a : Fin d)
    (H : selfAdjoint (Matrix (Fin d) (Fin d) ℂ))
    (A : Fin N → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ i, (A i).IsHermitian)
    (hAn : ∀ i, ‖A i‖≤1) (U : Matrix (Fin N) (Fin k) ℝ) (hU : Uᵀ*U=1)
    (hN : 1≤N) (hND : N≤d) (hkN : k≤N)
    (hH : ‖(H : Matrix (Fin d) (Fin d) ℂ)‖≤N)
    (C : selfAdjoint (Matrix (Fin k) (Fin k) ℝ))
    {δ : ℝ} (hδlow : ((2:ℝ)^14)⁻¹≤δ) (hδ1 : δ≤1)
    (hfloor : δ • (1 : Matrix (Fin k) (Fin k) ℝ)≤C) (hC1 : (C : Matrix (Fin k) (Fin k) ℝ)≤1)
    (hphysical : covarianceLift U C≤1)

include hA hAn hU hND hkN hH hδlow hδ1 hfloor hC1 hphysical in
theorem numerical_probe_accuracy (u : EuclideanSpace ℝ (Fin k)) (hu : ‖u‖=1) :
    |probe O (RectangularRidgeTuning.depth N d hN) (RectangularRidgeTuning.depth_positive N d hN)
      a (H : Matrix (Fin d) (Fin d) ℂ) (mixFamily A U) (mixFamily_isHermitian A U hA) C
      (weight N d hN) (1/(d : ℝ)) (differenceStep (size d N)) (valueAccuracy (size d N)) u-
      WithLp.ofLp u ⬝ᵥ (RectangularRidgePaidQueries.gram H (mixFamily A U) C
        (RectangularRidgeTuning.depth N d hN) (weight N d hN) (1/(d : ℝ)) *ᵥ WithLp.ofLp u)|≤
      derivativeAccuracy (size d N)/4 := by
  let P := size d N
  have hP : 1≤P := by dsimp [P,size]; linarith [show (0:ℝ)≤d from Nat.cast_nonneg d,
    show (0:ℝ)≤N from Nat.cast_nonneg N]
  have hP0 : 0<P := by linarith
  have hδ : 0<δ := lt_of_lt_of_le (by positivity) hδlow
  have hs : 0<differenceStep P := small_pos hP0 322 62
  have hν : 0<valueAccuracy P := small_pos hP0 346 64
  have hsδ : differenceStep P<δ := by
    have hb := differenceStep_le_floor hP
    norm_num at hb hδlow
    linarith
  have hex := RectangularRidgeStoredPaid.numerical_probe_accuracy H A hA hAn U hU hN hND hkN hH
    hδlow hδ1 hfloor hC1 hphysical u hu
  have hpert := probe_perturbation O _ (RectangularRidgeTuning.depth_positive N d hN) a
    (H : Matrix (Fin d) (Fin d) ℂ) (mixFamily A U) (mixFamily_isHermitian A U hA) C
    (weight_positive hN hND) (by positivity : 0≤1/(d : ℝ)) hs hν u
    (posDef_of_floor hδ hfloor).posSemidef (query_posDef hfloor hs.le hsδ u hu).posSemidef
  have he : 2*valueAccuracy P/differenceStep P=derivativeAccuracy P/8 := by
    rw [valueAccuracy_eq]
    field_simp
    <;> ring
  rw [he] at hpert
  exact (abs_sub_le _ (RectangularRidgePaidQueries.probe (H : Matrix (Fin d) (Fin d) ℂ)
    (mixFamily A U) C (RectangularRidgeTuning.depth N d hN) (weight N d hN)
      (1/(d : ℝ)) (differenceStep P) u) _).trans (by linarith)

def report : Matrix (Fin k) (Fin k) ℝ :=
  MSManuscriptGammaMatrix.reconstruct (probe O (RectangularRidgeTuning.depth N d hN)
    (RectangularRidgeTuning.depth_positive N d hN) a (H : Matrix (Fin d) (Fin d) ℂ)
    (mixFamily A U) (mixFamily_isHermitian A U hA) C (weight N d hN) (1/(d : ℝ))
    (differenceStep (size d N)) (valueAccuracy (size d N)))

theorem report_isSymm : (report O a H A hA U hN C).IsSymm :=
  MSManuscriptGammaMatrix.reconstruct_isSymm _

include hAn hU hND hkN hH hδlow hδ1 hfloor hC1 hphysical in
theorem report_accuracy {price : ℝ} (hprice : 1/size d N≤price) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ)
      (RectangularRidgePaidQueries.gram H (mixFamily A U) C
        (RectangularRidgeTuning.depth N d hN) (weight N d hN) (1/(d : ℝ))-
        report O a H A hA U hN C)‖≤price/64 := by
  let P := size d N
  have hP : 1≤P := by dsimp [P,size]; linarith [show (0:ℝ)≤d from Nat.cast_nonneg d,
    show (0:ℝ)≤N from Nat.cast_nonneg N]
  have hP0 : 0<P := by linarith
  have hη : 0<derivativeAccuracy P := small_pos hP0 20 2
  have hd : (0:ℝ)<d := by exact_mod_cast (show 0<d by omega)
  have hg := RectangularRidgeStoredGamma.gram_isSymm H (mixFamily A U)
    (mixFamily_isHermitian A U hA) C _ (RectangularRidgeTuning.depth_positive N d hN)
    _ _ (weight_positive hN hND) (by positivity : 0<1/(d : ℝ))
  have herr := MSManuscriptGammaMatrix.reconstruct_operator_error _ hg _
    (show 0≤derivativeAccuracy P/4 from by have := small_pos hP0 20 2; change 0<derivativeAccuracy P at this; positivity)
    (fun u hu => by
      rw [KSRayleighAccuracy.realRayleigh_eq_quadratic]
      exact numerical_probe_accuracy O a H A hA hAn U hU hN hND hkN hH C
        hδlow hδ1 hfloor hC1 hphysical u hu)
  apply herr.trans
  have hkP : (k : ℝ)≤P := by dsimp [P,size]; exact_mod_cast (by omega : k≤d+N+2)
  have he : P*(2*(derivativeAccuracy P/4))=1/((2:ℝ)^21*P) := by
    unfold derivativeAccuracy small big
    field_simp
    <;> ring
  calc
    (k:ℝ)*(2*(derivativeAccuracy P/4))≤P*(2*(derivativeAccuracy P/4)) := by
      exact mul_le_mul_of_nonneg_right hkP (by positivity)
    _ = _ := he
    _ ≤ (1/P)/64 := by
      rw [div_div]
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith
    _ ≤ price/64 := div_le_div_of_nonneg_right hprice (by norm_num)

end MatrixSpencer.RectangularRidgeSolverGamma
