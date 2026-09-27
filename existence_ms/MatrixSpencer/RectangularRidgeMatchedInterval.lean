import MatrixSpencer.RectangularRidgeMatchedFourth
import MatrixSpencer.MSManuscriptMatchedInterval

/-! Explicit legal real intervals for the primitive mixed matched movement.
The same numerical mesh covers the moving center, stored owner and actual
optimizing density. The symmetric remainder is proved from actual derivatives. -/
open Matrix Set Filter
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff Topology
noncomputable section
namespace MatrixSpencer.RectangularRidgeMatchedInterval
open RectangularRidgeNumericalParameters
open RectangularRidgeNumericalOptimizerFloor (size)
open RectangularRidgePrimitiveParameters
open MSManuscriptMatchedJointBounds (center covariance contDiff_center contDiff_covariance)
variable {N k d : ℕ} [Nonempty (Fin d)]
local instance ridgeMatchedIntervalCStar : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
local instance ridgeMatchedIntervalPhysicalSpace : NormedSpace ℝ (selfAdjoint (Matrix (Fin d) (Fin d) ℂ)) := inferInstance
local instance ridgeMatchedIntervalCoeffSpace : NormedSpace ℝ (selfAdjoint (Matrix (Fin k) (Fin k) ℝ)) := inferInstance
set_option maxHeartbeats 300000
attribute [local irreducible] RectangularRidgePotential.optimizer

def radius (P : ℝ) : ℝ := small P 12 2

theorem radius_pos {P : ℝ} (hP : 0 < P) : 0 < radius P := small_pos hP 12 2

theorem mesh_le_radius_half {P : ℝ} (hP : 1 ≤ P) : mesh P ≤ radius P/2 := by
  have hh := small_mono hP (show 13 ≤ 540 by omega) (show 2 ≤ 104 by omega)
  apply hh.trans_eq
  norm_num [small,big,radius]
  ring

theorem time_bounds {P γ t : ℝ} (hP : 1 ≤ P) (hγ : ((2:ℝ)^14)⁻¹ ≤ γ)
    (ht : |t| ≤ radius P) : |t| ≤ 1 ∧ t^2 ≤ γ/4 ∧ |t| * P^2 ≤ 1 := by
  have hP0 : P ≠ 0 := by linarith
  have hr : radius P ≤ 1/4096 := by
    have hh := small_le_dyadic hP 12 2
    norm_num at hh
    exact hh
  have ht' : |t| ≤ 1/4096 := ht.trans hr
  have he : radius P*P^2 = 1/4096 := by
    dsimp [radius,small,big]
    norm_num
    field_simp
  have hp := mul_le_mul_of_nonneg_right ht (sq_nonneg P)
  rw [he] at hp
  norm_num at hγ
  refine ⟨by linarith,?_,by linarith⟩
  have hab : t^2=|t|^2 := (sq_abs t).symm
  nlinarith [sq_nonneg (|t|-1/4096),abs_nonneg t]

omit [Nonempty (Fin d)] in
/-- Base matrix inequalities give all primitive bounds throughout the explicit
open real query interval; the physical lifted owner may have a kernel. -/
theorem interval_bounds (H B : selfAdjoint (Matrix (Fin d) (Fin d) ℂ))
    (U : Matrix (Fin N) (Fin k) ℝ) (C Q : selfAdjoint (Matrix (Fin k) (Fin k) ℝ))
    {P γ : ℝ} (hP : 1 ≤ P) (hγ : ((2:ℝ)^14)⁻¹ ≤ γ)
    (hH : ‖(H : Matrix (Fin d) (Fin d) ℂ)‖ ≤ (N : ℝ))
    (hB : ‖(B : Matrix (Fin d) (Fin d) ℂ)‖ ≤ P^2)
    (hC : γ • (1 : Matrix (Fin k) (Fin k) ℝ) ≤ (C : Matrix (Fin k) (Fin k) ℝ))
    (hC1 : (C : Matrix (Fin k) (Fin k) ℝ) ≤ 1)
    (hQ : (Q : Matrix (Fin k) (Fin k) ℝ).PosSemidef) (hQ1 : (Q : Matrix (Fin k) (Fin k) ℝ) ≤ 1)
    (hphysical : covarianceLift U C ≤ 1) {t : ℝ} (ht : |t| ≤ radius P) :
    (γ/2) • (1 : Matrix (Fin k) (Fin k) ℝ) ≤ (covariance C Q t : Matrix (Fin k) (Fin k) ℝ) ∧
    (covariance C Q t : Matrix (Fin k) (Fin k) ℝ) ≤ 1 ∧
    covarianceLift U (covariance C Q t) ≤ 1 ∧
    ‖(center H B t : Matrix (Fin d) (Fin d) ℂ)‖ ≤ (N : ℝ)+1 ∧ |t| ≤ 1 := by
  have hb := time_bounds hP hγ ht
  have hq := smul_le_smul_of_nonneg_left hQ1 (sq_nonneg t)
  have hl : (γ/2)•(1 : Matrix (Fin k) (Fin k) ℝ) ≤ (γ-t^2)•(1 : Matrix (Fin k) (Fin k) ℝ) :=
    smul_le_smul_of_nonneg_right (by linarith : γ/2 ≤ γ-t^2) Matrix.PosSemidef.one.nonneg
  have hcut : (covariance C Q t : Matrix (Fin k) (Fin k) ℝ) ≤ C :=
    sub_le_self _ (hQ.smul (sq_nonneg t)).nonneg
  refine ⟨hl.trans (by simpa only [sub_smul] using sub_le_sub hC hq),hcut.trans hC1,
    (covarianceLift_mono U hcut).trans hphysical,?_,hb.1⟩
  change ‖(H : Matrix (Fin d) (Fin d) ℂ)+t•(B : Matrix (Fin d) (Fin d) ℂ)‖ ≤ _
  have hn := norm_add_le (H : Matrix (Fin d) (Fin d) ℂ) (t•(B : Matrix (Fin d) (Fin d) ℂ))
  rw [norm_smul,Real.norm_eq_abs] at hn
  have hm := mul_le_mul_of_nonneg_left hB (abs_nonneg t)
  linarith [hb.2.2]

theorem smooth_and_fourth (H B : selfAdjoint (Matrix (Fin d) (Fin d) ℂ))
    (A : Fin N → Matrix (Fin d) (Fin d) ℂ) (hA : ∀i,(A i).IsHermitian) (hAn : ∀i,‖A i‖≤1)
    (U : Matrix (Fin N) (Fin k) ℝ) (hU : Uᵀ*U=1)
    (hN : 1 ≤ N) (hND : N ≤ d) (hkN : k ≤ N)
    (C Q : selfAdjoint (Matrix (Fin k) (Fin k) ℝ))
    (hQ : (Q : Matrix (Fin k) (Fin k) ℝ).PosSemidef) (hQ1 : (Q : Matrix (Fin k) (Fin k) ℝ) ≤ 1)
    (hH : ‖(H : Matrix (Fin d) (Fin d) ℂ)‖ ≤ (N : ℝ))
    (hB : ‖(B : Matrix (Fin d) (Fin d) ℂ)‖ ≤ (size d N)^2)
    {γ : ℝ} (hγ : ((2:ℝ)^14)⁻¹ ≤ γ) (hγ1 : γ ≤ 1)
    (hC : γ • (1 : Matrix (Fin k) (Fin k) ℝ) ≤ C) (hC1 : (C : Matrix (Fin k) (Fin k) ℝ) ≤ 1)
    (hphysical : covarianceLift U C ≤ 1) :
    let f := fun z => RectangularRidgeCovarianceCalculus.ownerPotential (RectangularRidgeTuning.depth N d hN)
      (center H B z) (mixFamily A U) (covariance C Q z) (weight N d hN) (1/(d : ℝ))
    ContDiffOn ℝ ∞ f (Icc (-mesh (size d N)) (mesh (size d N))) ∧
      ∀t∈Icc (-mesh (size d N)) (mesh (size d N)), |iteratedDeriv 4 f t| ≤ fourthCap (size d N) := by
  let P := size d N
  have hP : 1 ≤ P := by dsimp [P,size]; linarith [(Nat.cast_nonneg d : (0:ℝ) ≤ d), (Nat.cast_nonneg N : (0:ℝ) ≤ N)]
  have hr := radius_pos (by linarith : 0 < P)
  have hs := mesh_le_radius_half hP
  have hsub : Icc (-mesh P) (mesh P) ⊆ Ioo (-radius P) (radius P) := by
    intro z hz
    constructor <;> linarith [hz.1,hz.2]
  have hb (z : ℝ) (hz : z∈Ioo (-radius P) (radius P)) := interval_bounds H B U C Q hP hγ hH hB hC hC1 hQ hQ1 hphysical (abs_lt.mpr hz).le
  have hg : ((2:ℝ)^15)⁻¹ ≤ γ/2 := by norm_num at hγ ⊢; linarith
  have hg0 : 0 < γ/2 := lt_of_lt_of_le (by positivity) hg
  have hpos (z : ℝ) (hz : z∈Ioo (-radius P) (radius P)) : (covariance C Q z : Matrix (Fin k) (Fin k) ℝ).PosDef := by
    simpa only [add_sub_cancel] using (Matrix.PosDef.one.smul hg0).add_posSemidef (Matrix.le_iff.mp (hb z hz).1)
  have hθ := weight_positive hN hND
  have hdp : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hκ : 0 < 1/(d : ℝ) := one_div_pos.mpr hdp
  constructor
  · intro z hz
    exact ((contDiffAt_jointHermitianRidgeOwnerPotential (mixFamily A U) (mixFamily_isHermitian A U hA)
      (RectangularRidgeTuning.depth N d hN) (RectangularRidgeTuning.depth_positive N d hN)
      (weight N d hN) (1/(d : ℝ)) hθ hκ (center H B z) (covariance C Q z) (hpos z (hsub hz))).comp z
      ((contDiff_center H B).contDiffAt.prodMk (contDiff_covariance C Q).contDiffAt)).contDiffWithinAt
  · intro z hz
    exact RectangularRidgeMatchedFourth.potential_fourth_le H B A hA hAn U hU hN hND hkN C Q
      (MSManuscriptComplexSourceNorm.real_coefficient_norm_le_one hQ hQ1) hB hg (by linarith)
      isOpen_Ioo (fun z hz => (hb z hz).1) (fun z hz => (hb z hz).2.1)
      (fun z hz => (hb z hz).2.2.1) (fun z hz => (hb z hz).2.2.2.1)
      (fun z hz => (hb z hz).2.2.2.2) (hsub hz)

attribute [local irreducible] RectangularRidgeCovarianceCalculus.ownerPotential

/-- Both finite random signs use the actual potential, with a fully input-derived
polynomial Taylor remainder at the displayed numerical mesh. -/
theorem symmetric_average_error (H B : selfAdjoint (Matrix (Fin d) (Fin d) ℂ))
    (A : Fin N → Matrix (Fin d) (Fin d) ℂ) (hA : ∀i,(A i).IsHermitian) (hAn : ∀i,‖A i‖≤1)
    (U : Matrix (Fin N) (Fin k) ℝ) (hU : Uᵀ*U=1)
    (hN : 1 ≤ N) (hND : N ≤ d) (hkN : k ≤ N)
    (C Q : selfAdjoint (Matrix (Fin k) (Fin k) ℝ))
    (hQ : (Q : Matrix (Fin k) (Fin k) ℝ).PosSemidef) (hQ1 : (Q : Matrix (Fin k) (Fin k) ℝ) ≤ 1)
    (hH : ‖(H : Matrix (Fin d) (Fin d) ℂ)‖ ≤ (N : ℝ))
    (hB : ‖(B : Matrix (Fin d) (Fin d) ℂ)‖ ≤ (size d N)^2)
    {γ : ℝ} (hγ : ((2:ℝ)^14)⁻¹ ≤ γ) (hγ1 : γ ≤ 1)
    (hC : γ • (1 : Matrix (Fin k) (Fin k) ℝ) ≤ C) (hC1 : (C : Matrix (Fin k) (Fin k) ℝ) ≤ 1)
    (hphysical : covarianceLift U C ≤ 1) :
    let h := mesh (size d N)
    let f := fun z => RectangularRidgeCovarianceCalculus.ownerPotential (RectangularRidgeTuning.depth N d hN)
      (center H B z) (mixFamily A U) (covariance C Q z) (weight N d hN) (1/(d : ℝ))
    |(f h+f (-h))/2-f 0-iteratedDeriv 2 f 0*h^2/2| ≤ fourthCap (size d N)*h^4/24 := by
  have hP : 0 < size d N := by unfold size; positivity
  exact MSManuscriptMatchedInterval.average_of_smooth_and_fourth _ (small_pos hP 540 104)
    (smooth_and_fourth H B A hA hAn U hU hN hND hkN C Q hQ hQ1 hH hB hγ hγ1 hC hC1 hphysical)

end MatrixSpencer.RectangularRidgeMatchedInterval
