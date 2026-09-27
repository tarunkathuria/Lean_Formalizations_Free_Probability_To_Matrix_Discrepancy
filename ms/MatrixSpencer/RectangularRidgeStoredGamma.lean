import MatrixSpencer.RectangularRidgeStoredPaid

/-! Finite polynomial-precision covariance response reporting and the concrete
Jacobi stopping/direction rule for the primitive-tuned mixed potential. -/
open Matrix Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
noncomputable section
namespace MatrixSpencer.RectangularRidgeStoredGamma
open RectangularRidgePrimitiveParameters RectangularRidgeNumericalOptimizerFloor
open RectangularRidgeCovarianceQueries RectangularRidgePaidQueries MSManuscriptGammaSmoothness
variable {N k d : ℕ} [Nonempty (Fin d)]
local instance ridgeStoredGammaCStar : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
local instance ridgeStoredGammaSpace : NormedSpace ℝ (selfAdjoint (Matrix (Fin d) (Fin d) ℂ)) := inferInstance
attribute [local irreducible] RectangularRidgePotential.optimizer
set_option maxHeartbeats 300000

def report (H : Matrix (Fin d) (Fin d) ℂ) (A : Fin k → Matrix (Fin d) (Fin d) ℂ)
    (C : Matrix (Fin k) (Fin k) ℝ) (N : ℕ) (hN : 1 ≤ N) : Matrix (Fin k) (Fin k) ℝ :=
  MSManuscriptGammaMatrix.reconstruct (probe H A C (RectangularRidgeTuning.depth N d hN)
    (weight N d hN) (1/(d : ℝ)) (RectangularRidgeNumericalParameters.differenceStep (size d N)))

theorem report_isSymm (H : Matrix (Fin d) (Fin d) ℂ) (A : Fin k → Matrix (Fin d) (Fin d) ℂ)
    (C : Matrix (Fin k) (Fin k) ℝ) (N : ℕ) (hN : 1 ≤ N) : (report H A C N hN).IsSymm :=
  MSManuscriptGammaMatrix.reconstruct_isSymm _

theorem gram_isSymm (H : selfAdjoint (Matrix (Fin d) (Fin d) ℂ))
    (A : Fin k → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ i, (A i).IsHermitian)
    (C : Matrix (Fin k) (Fin k) ℝ) (m : ℕ) (hm : 1 ≤ m)
    (θ κ : ℝ) (hθ : 0 < θ) (hκ : 0 < κ) : (gram H A C m θ κ).IsSymm := by
  let S := RectangularRidgePotential.optimizer (H : Matrix (Fin d) (Fin d) ℂ) (covarianceKraus A C) m θ κ
  have hS : S.PosDef := RectangularRidgePotential.optimizer_posDef _ _ hm hθ hκ.le
  have hZ := (RectangularRidgeOwnerFrame.sourceTransport_posDef A hA C hS).posSemidef.mul_mul_conjTranspose_same
    (krausSupportEmbedding (covarianceKraus A C))
  have hg := covarianceGram_posSemidef A hA S _ hS.posSemidef hZ
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hg.isHermitian.eq

attribute [local irreducible] RectangularRidgePaidQueries.gram RectangularRidgePaidQueries.probe

variable (H : selfAdjoint (Matrix (Fin d) (Fin d) ℂ))
    (A : Fin N → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ i, (A i).IsHermitian)
    (hAn : ∀ i, ‖A i‖ ≤ 1) (U : Matrix (Fin N) (Fin k) ℝ) (hU : Uᵀ*U=1)
    (hN : 1 ≤ N) (hND : N ≤ d) (hkN : k ≤ N)
    (hH : ‖(H : Matrix (Fin d) (Fin d) ℂ)‖ ≤ N)
    {C : Matrix (Fin k) (Fin k) ℝ} {δ : ℝ} (hδlow : ((2:ℝ)^14)⁻¹ ≤ δ) (hδ1 : δ ≤ 1)
    (hfloor : δ • (1 : Matrix (Fin k) (Fin k) ℝ) ≤ C) (hC1 : C ≤ 1)
    (hphysical : covarianceLift U C ≤ 1)

include hA hAn hU hND hkN hH hδlow hδ1 hfloor hC1 hphysical

theorem report_accuracy {price : ℝ} (hprice : 1/size d N ≤ price) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ)
      (gram H (mixFamily A U) C (RectangularRidgeTuning.depth N d hN) (weight N d hN) (1/(d : ℝ)) -
        report (H : Matrix (Fin d) (Fin d) ℂ) (mixFamily A U) C N hN)‖ ≤ price/64 := by
  let P := size d N
  let η := RectangularRidgeNumericalParameters.derivativeAccuracy P
  have hd : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hP : 1 ≤ P := by dsimp [P,size]; linarith
  have hP0 : 0 < P := by linarith
  have hη : 0 ≤ η/8 := by
    have hh := RectangularRidgeNumericalParameters.small_pos hP0 20 2
    change 0 < η at hh
    positivity
  have hG := gram_isSymm H (mixFamily A U) (mixFamily_isHermitian A U hA) C (RectangularRidgeTuning.depth N d hN)
    (RectangularRidgeTuning.depth_positive N d hN) (weight N d hN) (1/(d : ℝ))
    (weight_positive hN hND) (by positivity)
  have herr := MSManuscriptGammaMatrix.reconstruct_operator_error _ hG
    (probe (H : Matrix (Fin d) (Fin d) ℂ) (mixFamily A U) C (RectangularRidgeTuning.depth N d hN)
      (weight N d hN) (1/(d : ℝ)) (RectangularRidgeNumericalParameters.differenceStep P)) hη
    (fun u hu => by
      rw [KSRayleighAccuracy.realRayleigh_eq_quadratic]
      exact RectangularRidgeStoredPaid.numerical_probe_accuracy H A hA hAn U hU hN hND hkN hH
        hδlow hδ1 hfloor hC1 hphysical u hu)
  apply herr.trans
  have hkP : (k : ℝ) ≤ P := by
    have hkn : (k : ℝ) ≤ N := by exact_mod_cast hkN
    dsimp [P,size]
    linarith
  have he : P*(2*(η/8)) = 1/((2:ℝ)^22*P) := by
    dsimp [η,RectangularRidgeNumericalParameters.derivativeAccuracy,
      RectangularRidgeNumericalParameters.small,RectangularRidgeNumericalParameters.big]
    field_simp
    <;> ring
  calc
    (k:ℝ)*(2*(η/8)) ≤ P*(2*(η/8)) := mul_le_mul_of_nonneg_right hkP (mul_nonneg (by norm_num) hη)
    _ = _ := he
    _ ≤ (1/P)/64 := by
      rw [div_div]
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith
    _ ≤ price/64 := div_le_div_of_nonneg_right hprice (by norm_num)

/-- The actual finite Jacobi stopping test certifies a genuine covariance cap. -/
theorem stop_sound {price : ℝ} (hprice : 1/size d N ≤ price) (hk : 0 < k)
    (hs : MSManuscriptGammaTop.stop (report (H : Matrix (Fin d) (Fin d) ℂ) (mixFamily A U) C N hN) price hk = true) :
    gram H (mixFamily A U) C (RectangularRidgeTuning.depth N d hN) (weight N d hN) (1/(d : ℝ)) ≤
      price • (1 : Matrix (Fin k) (Fin k) ℝ) := by
  have hd : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hp : 0 < price := lt_of_lt_of_le (by dsimp [size]; positivity) hprice
  exact MSManuscriptGammaTop.stop_sound _ _
    (gram_isSymm H (mixFamily A U) (mixFamily_isHermitian A U hA) C (RectangularRidgeTuning.depth N d hN)
      (RectangularRidgeTuning.depth_positive N d hN) (weight N d hN) (1/(d : ℝ))
      (weight_positive hN hND) (by positivity))
    (report_isSymm _ _ _ _ _) hp hk
    (report_accuracy H A hA hAn U hU hN hND hkN hH hδlow hδ1 hfloor hC1 hphysical hprice) hs

/-- Every concrete continuation direction has the true response needed by the paid cut. -/
theorem continue_sound {price : ℝ} (hprice : 1/size d N ≤ price) (hk : 0 < k)
    (hs : MSManuscriptGammaTop.stop (report (H : Matrix (Fin d) (Fin d) ℂ) (mixFamily A U) C N hN) price hk = false) :
    let u := MSManuscriptGammaTop.vector (report (H : Matrix (Fin d) (Fin d) ℂ) (mixFamily A U) C N hN) price hk
    ‖u‖=1 ∧ 7*price/8 < KSRayleighAccuracy.realRayleigh
      (gram H (mixFamily A U) C (RectangularRidgeTuning.depth N d hN) (weight N d hN) (1/(d : ℝ))) u := by
  have hp : 0 < price := lt_of_lt_of_le (by dsimp [size]; positivity) hprice
  exact MSManuscriptGammaTop.continue_sound _ _ hp hk
    (report_accuracy H A hA hAn U hU hN hND hkN hH hδlow hδ1 hfloor hC1 hphysical hprice) hs

/-- The actual finite report and Jacobi rule choose a paid direction whose
literal covariance cut achieves the claimed decrease of the mixed optimum. -/
theorem continuation_paid_drop {price : ℝ} (hprice : 1/size d N ≤ price) (hk : 0 < k)
    (hs : MSManuscriptGammaTop.stop (report (H : Matrix (Fin d) (Fin d) ℂ) (mixFamily A U) C N hN) price hk = false) :
    let u := MSManuscriptGammaTop.vector (report (H : Matrix (Fin d) (Fin d) ℂ) (mixFamily A U) C N hN) price hk
    RectangularRidgeCovarianceCalculus.ownerPotential (RectangularRidgeTuning.depth N d hN)
        H (mixFamily A U)
        (C-RectangularRidgeNumericalParameters.paidStep (size d N) • realRankOne (WithLp.ofLp u))
        (weight N d hN) (1/(d : ℝ)) +
        5*price*RectangularRidgeNumericalParameters.paidStep (size d N)/8 ≤
      RectangularRidgeCovarianceCalculus.ownerPotential (RectangularRidgeTuning.depth N d hN)
        H (mixFamily A U) C (weight N d hN) (1/(d : ℝ)) := by
  let u := MSManuscriptGammaTop.vector (report (H : Matrix (Fin d) (Fin d) ℂ) (mixFamily A U) C N hN) price hk
  have hu := continue_sound H A hA hAn U hU hN hND hkN hH hδlow hδ1 hfloor hC1 hphysical hprice hk hs
  apply RectangularRidgeStoredPaid.numerical_paid_drop H A hA hAn U hU hN hND hkN hH
    hδlow hδ1 hfloor hC1 hphysical u hu.1 hprice
  rw [← KSRayleighAccuracy.realRayleigh_eq_quadratic]
  exact hu.2.le

end MatrixSpencer.RectangularRidgeStoredGamma
