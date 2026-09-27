import MatrixSpencer.RectangularRidgeJointOwnerResponse
import MatrixSpencer.RectangularRidgeCoefficientResponse
import MatrixSpencer.MatchedOwnerTaylor
import MatrixSpencer.RegularizedFamilyDeletion

/-! The exact second coefficient of the actual mixed matched path. Its
covariance payment has the sign supplied by the same optimizing density. -/
open Matrix Set Filter
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff Topology
noncomputable section
namespace MatrixSpencer.RectangularRidgeMatchedSecond
open RectangularRidgeCalculus
variable {ι j n : Type*} [Fintype ι] [DecidableEq ι] [Fintype j] [DecidableEq j]
  [Fintype n] [DecidableEq n] [Nonempty n]
local instance ridgeMatchedSecondCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance ridgeMatchedSecondPhysicalGroup : NormedAddCommGroup (selfAdjoint (Matrix n n ℂ)) := inferInstance
local instance ridgeMatchedSecondPhysicalSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance
local instance ridgeMatchedSecondCoeffGroup : NormedAddCommGroup (selfAdjoint (Matrix ι ι ℝ)) := inferInstance
local instance ridgeMatchedSecondCoeffSpace : NormedSpace ℝ (selfAdjoint (Matrix ι ι ℝ)) := inferInstance
set_option maxHeartbeats 300000
attribute [local irreducible] RectangularRidgePotential.optimizer

omit [Nonempty n] in
theorem center_fiber_eq (A : ι → Matrix n n ℂ) (hA : ∀i,(A i).IsHermitian)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (m : ℕ) (θ κ : ℝ) :
    (fun H : selfAdjoint (Matrix n n ℂ) => RectangularRidgeCovarianceCalculus.ownerPotential m H A C θ κ) =
      RectangularRidgeCalculus.ownerPotentialAsCenter A C m θ κ := by
  funext H
  change RectangularRidgeCovarianceCalculus.ownerPotential m (H : Matrix n n ℂ) A C θ κ = _
  unfold RectangularRidgeCalculus.ownerPotentialAsCenter RectangularRidgeCalculus.hermitianPotential
  exact RectangularRidgeCovarianceCalculus.ownerPotential_eq_densityPotential m (H : Matrix n n ℂ) A hA hC θ κ

omit [Nonempty n] in
theorem centerHessian_covarianceLift (A : ι → Matrix n n ℂ) (hA : ∀i,(A i).IsHermitian)
    (U : Matrix ι j ℝ) {K : Matrix j j ℝ} (hK : K.PosSemidef) (m : ℕ) (θ κ : ℝ)
    (H : selfAdjoint (Matrix n n ℂ)) :
    RectangularRidgeCalculus.ownerCenterHessian A (covarianceLift U K) m θ κ H =
      RectangularRidgeCalculus.ownerCenterHessian (mixFamily A U) K m θ κ H := by
  have he : RectangularRidgeCalculus.ownerPotentialAsCenter A (covarianceLift U K) m θ κ =
      RectangularRidgeCalculus.ownerPotentialAsCenter (mixFamily A U) K m θ κ := by
    rw [←center_fiber_eq A hA (covarianceLift_posSemidef U hK),
      ←center_fiber_eq (mixFamily A U) (mixFamily_isHermitian A U hA) hK]
    funext X
    unfold RectangularRidgeCovarianceCalculus.ownerPotential
    exact regularizedOwnerPotential_covarianceLift (X : Matrix n n ℂ) A U K (RectangularRidgeCovarianceCalculus.regularizer m θ κ)
  unfold RectangularRidgeCalculus.ownerCenterHessian
  rw [he]

theorem joint_fderiv_covariance (A : ι → Matrix n n ℂ) (hA : ∀i,(A i).IsHermitian)
    (m : ℕ) (hm : 1 ≤ m) (θ κ : ℝ) (hθ : 0 < θ) (hκ : 0 < κ)
    (H : selfAdjoint (Matrix n n ℂ)) (C Q : selfAdjoint (Matrix ι ι ℝ))
    (hC : (C : Matrix ι ι ℝ).PosDef) :
    fderiv ℝ (jointHermitianRidgeOwnerPotential A m θ κ) (H,C) (0,-Q) =
      -covarianceDerivativeFunctional A C (hermitianOptimizer H (covarianceKraus A C) m θ κ) Q := by
  have hf := (contDiffAt_jointHermitianRidgeOwnerPotential A hA m hm θ κ hθ hκ H C hC).of_le
    (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  rw [←fderiv_fiber_snd_apply _ H C (-Q) hf]
  change fderiv ℝ (hermitianRidgeOwnerPotential H A m θ κ) C (-Q) = _
  rw [(hasFDerivAt_hermitianRidgeOwnerPotential_covariance H A hA m hm θ κ hθ hκ C hC).fderiv,map_neg]

theorem joint_fderiv_fderiv_center (A : ι → Matrix n n ℂ) (hA : ∀i,(A i).IsHermitian)
    (m : ℕ) (hm : 1 ≤ m) (θ κ : ℝ) (hθ : 0 < θ) (hκ : 0 < κ)
    (H B : selfAdjoint (Matrix n n ℂ)) (C : selfAdjoint (Matrix ι ι ℝ))
    (hC : (C : Matrix ι ι ℝ).PosDef) :
    fderiv ℝ (fderiv ℝ (jointHermitianRidgeOwnerPotential A m θ κ)) (H,C) (B,0) (B,0) =
      RectangularRidgeCalculus.ownerCenterHessian A C m θ κ H B B := by
  have hf := (contDiffAt_jointHermitianRidgeOwnerPotential A hA m hm θ κ hθ hκ H C hC).of_le
    (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have hh := fderiv_fderiv_fiber_fst_quadratic (jointHermitianRidgeOwnerPotential A m θ κ) H B C hf
  change _ = fderiv ℝ (fderiv ℝ (fun X : selfAdjoint (Matrix n n ℂ) =>
    RectangularRidgeCovarianceCalculus.ownerPotential m X A C θ κ)) H B B at hh
  rw [center_fiber_eq A hA hC.posSemidef] at hh
  exact hh

theorem second_eq (H B : selfAdjoint (Matrix n n ℂ))
    (A : ι → Matrix n n ℂ) (hA : ∀i,(A i).IsHermitian)
    (C Q : selfAdjoint (Matrix ι ι ℝ)) (m : ℕ) (hm : 1 ≤ m)
    {θ κ : ℝ} (hθ : 0 < θ) (hκ : 0 < κ) (hC : (C : Matrix ι ι ℝ).PosDef) :
    iteratedDeriv 2 (fun t : ℝ => RectangularRidgeCovarianceCalculus.ownerPotential m ((H+t•B : selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ) A (C-t^2•Q) θ κ) 0 / 2 =
      (1/2 : ℝ)*RectangularRidgeCalculus.ownerCenterHessian A C m θ κ H B B -
      covarianceDerivativeFunctional A C (hermitianOptimizer H (covarianceKraus A C) m θ κ) Q := by
  have hf := (contDiffAt_jointHermitianRidgeOwnerPotential A hA m hm θ κ hθ hκ H C hC).of_le
    (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have hh := iteratedDeriv_comp_matchedCurve_two_zero (jointHermitianRidgeOwnerPotential A m θ κ)
    (ownerTaylorEmbedding ((H,C),B,Q)) hf
  simp only [ownerTaylorEmbedding_curve] at hh
  change iteratedDeriv 2 (fun t : ℝ => RectangularRidgeCovarianceCalculus.ownerPotential m ((H+t•B : selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ) A (C-t^2•Q) θ κ) 0 =
    fderiv ℝ (fderiv ℝ (jointHermitianRidgeOwnerPotential A m θ κ)) (H,C) (B,0) (B,0)+
      2*fderiv ℝ (jointHermitianRidgeOwnerPotential A m θ κ) (H,C) (0,-Q) at hh
  rw [joint_fderiv_fderiv_center A hA m hm θ κ hθ hκ H B C hC,
    joint_fderiv_covariance A hA m hm θ κ hθ hκ H C Q hC] at hh
  linarith

theorem second_le (H B : selfAdjoint (Matrix n n ℂ))
    (A : ι → Matrix n n ℂ) (hA : ∀i,(A i).IsHermitian)
    (C Q : selfAdjoint (Matrix ι ι ℝ)) (m : ℕ) (hm : 1 ≤ m)
    {θ κ : ℝ} (hθ : 0 < θ) (hκ : 0 < κ) (hC : (C : Matrix ι ι ℝ).PosDef)
    (hQ : (Q : Matrix ι ι ℝ).PosSemidef) :
    iteratedDeriv 2 (fun t : ℝ => RectangularRidgeCovarianceCalculus.ownerPotential m ((H+t•B : selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ) A (C-t^2•Q) θ κ) 0 / 2 ≤
      (1/2 : ℝ)*RectangularRidgeCalculus.ownerCenterHessian A C m θ κ H B B := by
  rw [second_eq H B A hA C Q m hm hθ hκ hC]
  apply sub_le_self
  rw [covarianceDerivativeFunctional_apply A hA]
  have hS := hermitianOptimizer_posDef H (covarianceKraus A C) m hm θ κ hθ hκ
  exact realTrace_mul_nonneg (covarianceSupportTransport_posSemidef A hA C _ hC hS)
    (covarianceSource_posSemidef A hA hQ hS.posSemidef)

end MatrixSpencer.RectangularRidgeMatchedSecond
