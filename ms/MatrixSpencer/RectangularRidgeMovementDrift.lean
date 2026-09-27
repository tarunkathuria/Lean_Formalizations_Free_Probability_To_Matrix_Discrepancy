import MatrixSpencer.RectangularRidgeMatchedInterval
import MatrixSpencer.RectangularRidgeMatchedSecond
import SimpleMS.UniformMoments
import MatrixSpencer.MSManuscriptSupportedMovement
import MatrixSpencer.MSManuscriptNumericalMovement

/-! Actual uniform-frame matched movement for the primitive ridged rectangular
potential. Its expected increment is controlled by the actual coefficient
response and the explicit numerical Taylor error; no Taylor oracle is assumed. -/
open Matrix Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.RectangularRidgeMovementDrift
open SimpleMS.UniformMoments SimpleMS.UniformSampler
open RectangularRidgeNumericalParameters
open RectangularRidgeNumericalOptimizerFloor (size)
open RectangularRidgePrimitiveParameters
variable {N k d : ℕ} [Nonempty (Fin d)]
local instance ridgeMovementCStar : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
local instance ridgeMovementPhysicalGroup : NormedAddCommGroup (selfAdjoint (Matrix (Fin d) (Fin d) ℂ)) := inferInstance
local instance ridgeMovementPhysicalSpace : NormedSpace ℝ (selfAdjoint (Matrix (Fin d) (Fin d) ℂ)) := inferInstance
local instance ridgeMovementCoeffGroup : NormedAddCommGroup (selfAdjoint (Matrix (Fin k) (Fin k) ℝ)) := inferInstance
local instance ridgeMovementCoeffSpace : NormedSpace ℝ (selfAdjoint (Matrix (Fin k) (Fin k) ℝ)) := inferInstance
set_option maxHeartbeats 300000
set_option maxRecDepth 4096
set_option exponentiation.threshold 2048
attribute [local irreducible] RectangularRidgePotential.optimizer RectangularRidgeCalculus.ownerCenterHessian

/-- The actual potential at the original input's integer tuning. -/
def value {ι : Type*} [Fintype ι] [DecidableEq ι] (hN : 1 ≤ N)
    (H : Matrix (Fin d) (Fin d) ℂ) (A : ι → Matrix (Fin d) (Fin d) ℂ) (C : Matrix ι ι ℝ) : ℝ :=
  RectangularRidgeCovarianceCalculus.ownerPotential (RectangularRidgeTuning.depth N d hN) H A C (weight N d hN) (1/(d : ℝ))

/-- Half the actual optimized center Hessian in the original coefficient coordinates. -/
def response (hN : 1 ≤ N) (A : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀i,(A i).IsHermitian) (C : Matrix (Fin N) (Fin N) ℝ)
    (H : selfAdjoint (Matrix (Fin d) (Fin d) ℂ)) :=
  RectangularRidgeCalculus.ownerCoefficientResponse A hA C (RectangularRidgeTuning.depth N d hN)
    (weight N d hN) (1/(d : ℝ)) H

omit [Nonempty (Fin d)] in
theorem half_hessian_expectation (A : Fin N → Matrix (Fin d) (Fin d) ℂ) (hA : ∀i,(A i).IsHermitian)
    (C : Matrix (Fin N) (Fin N) ℝ) (m : ℕ) (θ κ : ℝ) (H : selfAdjoint (Matrix (Fin d) (Fin d) ℂ))
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin N))) (hQ : (covMatrix W).PosSemidef) (hq : 0<realTrace (covMatrix W)) :
    (∑s,weight W s*((1/2:ℝ)*RectangularRidgeCalculus.ownerCenterHessian A C m θ κ H
      (physical A hA W s) (physical A hA W s))) =
      realTrace ((covMatrix W)*RectangularRidgeCalculus.ownerCoefficientResponse A hA C m θ κ H) := by
  simpa only [RectangularRidgeCalculus.ownerCoefficientResponse_quadratic,physical,ownerPhysicalIncrement] using
    SimpleMS.UniformMoments.quadratic_expectation W hQ hq
      (RectangularRidgeCalculus.ownerCoefficientResponse A hA C m θ κ H)

omit [Nonempty (Fin d)] in
theorem physical_norm_le_size_square (A : Fin N → Matrix (Fin d) (Fin d) ℂ) (hA : ∀i,(A i).IsHermitian)
    (hAn : ∀i,‖A i‖≤1) (hN : 1 ≤ N)
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin N))) (hQ : (covMatrix W).PosSemidef) (hQ1 : (covMatrix W)≤1) (s : Draws W) :
    ‖(physical A hA W s : Matrix (Fin d) (Fin d) ℂ)‖ ≤ (size d N)^2 := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hsqrt : Real.sqrt (N : ℝ) ≤ N := (Real.sqrt_le_iff).mpr ⟨by positivity,by nlinarith⟩
  have hnp : (N : ℝ) ≤ size d N := by unfold size; linarith [(Nat.cast_nonneg d : (0:ℝ) ≤ d)]
  have hh := physical_norm_le A hA (by norm_num : (0:ℝ)≤1) hAn W hQ hQ1 s
  calc
    _ ≤ Real.sqrt (N : ℝ)*(N : ℝ) := by simpa only [directionCap,mul_one] using hh
    _ ≤ (N : ℝ)^2 := by nlinarith [mul_le_mul_of_nonneg_right hsqrt (Nat.cast_nonneg N)]
    _ ≤ (size d N)^2 := pow_le_pow_left₀ (Nat.cast_nonneg N) hnp 2

/-- The two literal signs at the numerical mesh satisfy the actual symmetric
Taylor inequality, after discarding the proved nonnegative covariance payment. -/
theorem pair_bound (H B : selfAdjoint (Matrix (Fin d) (Fin d) ℂ))
    (A : Fin N → Matrix (Fin d) (Fin d) ℂ) (hA : ∀i,(A i).IsHermitian) (hAn : ∀i,‖A i‖≤1)
    (U : Matrix (Fin N) (Fin k) ℝ) (hU : Uᵀ*U=1)
    (hN : 1 ≤ N) (hND : N ≤ d) (hkN : k ≤ N)
    (K L : selfAdjoint (Matrix (Fin k) (Fin k) ℝ))
    (hL : (L : Matrix (Fin k) (Fin k) ℝ).PosSemidef) (hL1 : (L : Matrix (Fin k) (Fin k) ℝ)≤1)
    (hH : ‖(H : Matrix (Fin d) (Fin d) ℂ)‖≤N) (hB : ‖(B : Matrix (Fin d) (Fin d) ℂ)‖≤(size d N)^2)
    {γ : ℝ} (hγ : ((2:ℝ)^14)⁻¹≤γ) (hγ1 : γ≤1)
    (hK : γ•(1 : Matrix (Fin k) (Fin k) ℝ)≤K) (hK1 : (K : Matrix (Fin k) (Fin k) ℝ)≤1)
    (hphysical : covarianceLift U K≤1) :
    let h := mesh (size d N)
    (value hN (H+h•B) A (covarianceLift U K-h^2•covarianceLift U L)+
      value hN (H-h•B) A (covarianceLift U K-h^2•covarianceLift U L))/2-
        value hN H A (covarianceLift U K) ≤
      h^2*((1/2:ℝ)*RectangularRidgeCalculus.ownerCenterHessian A (covarianceLift U K)
        (RectangularRidgeTuning.depth N d hN) (weight N d hN) (1/(d : ℝ)) H B B)+
      fourthCap (size d N)*h^4/24 := by
  let h := mesh (size d N)
  let f : ℝ → ℝ := fun t => value hN ((H+t•B : selfAdjoint (Matrix (Fin d) (Fin d) ℂ)) : Matrix (Fin d) (Fin d) ℂ)
    (mixFamily A U) (K-t^2•L)
  have ht : |(f h+f (-h))/2-f 0-iteratedDeriv 2 f 0*h^2/2| ≤ fourthCap (size d N)*h^4/24 :=
    RectangularRidgeMatchedInterval.symmetric_average_error H B A hA hAn U hU hN hND hkN K L hL hL1 hH hB hγ hγ1 hK hK1 hphysical
  have hγ0 : 0 < γ := lt_of_lt_of_le (by positivity) hγ
  have hKp : (K : Matrix (Fin k) (Fin k) ℝ).PosDef := by
    simpa only [add_sub_cancel] using (Matrix.PosDef.one.smul hγ0).add_posSemidef (Matrix.le_iff.mp hK)
  have hθ := weight_positive hN hND
  have hκ : 0 < 1/(d : ℝ) := by
    have hd : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
    positivity
  have hs := RectangularRidgeMatchedSecond.second_le H B (mixFamily A U) (mixFamily_isHermitian A U hA) K L
    (RectangularRidgeTuning.depth N d hN) (RectangularRidgeTuning.depth_positive N d hN) hθ hκ hKp hL
  rw [←RectangularRidgeMatchedSecond.centerHessian_covarianceLift A hA U hKp.posSemidef] at hs
  have hp : (f h+f (-h))/2-f 0 ≤ h^2*((1/2:ℝ)*RectangularRidgeCalculus.ownerCenterHessian A (covarianceLift U K)
      (RectangularRidgeTuning.depth N d hN) (weight N d hN) (1/(d : ℝ)) H B B)+fourthCap (size d N)*h^4/24 := by
    have hs' := mul_le_mul_of_nonneg_right hs (sq_nonneg h)
    have ht' := (abs_le.mp ht).2
    change iteratedDeriv 2 f 0 / 2 * h^2 ≤ _ at hs'
    nlinarith
  have he (t : ℝ) : f t = value hN ((H+t•B : selfAdjoint (Matrix (Fin d) (Fin d) ℂ)) : Matrix (Fin d) (Fin d) ℂ)
      A (covarianceLift U K-t^2•covarianceLift U L) := by
    rw [←covarianceLift_sub_smul]
    dsimp only [f,value]
    unfold RectangularRidgeCovarianceCalculus.ownerPotential
    exact (regularizedOwnerPotential_covarianceLift _ A U _ _).symm
  rw [he h,he (-h),he 0] at hp
  simpa only [neg_smul,sub_eq_add_neg,neg_sq,zero_smul,neg_zero,add_zero,
    zero_pow (by norm_num : (2:ℕ)≠0),sub_zero] using hp

/-- Exact uniform-frame expected increment on a stored face, with singular ambient
owners permitted and the actual response charge explicitly identified. -/
theorem fixed_frame (H : selfAdjoint (Matrix (Fin d) (Fin d) ℂ))
    (A : Fin N → Matrix (Fin d) (Fin d) ℂ) (hA : ∀i,(A i).IsHermitian) (hAn : ∀i,‖A i‖≤1)
    (U : Matrix (Fin N) (Fin k) ℝ) (hU : Uᵀ*U=1)
    (hN : 1 ≤ N) (hND : N ≤ d) (hkN : k ≤ N)
    (K : selfAdjoint (Matrix (Fin k) (Fin k) ℝ))
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin N))) (hQ : (covMatrix W).PosSemidef) (hQC : (covMatrix W)≤covarianceLift U K)
    (hq : 0<realTrace (covMatrix W)) (hC1 : covarianceLift U K≤1)
    (hH : ‖(H : Matrix (Fin d) (Fin d) ℂ)‖≤N)
    {γ : ℝ} (hγ : ((2:ℝ)^14)⁻¹≤γ) (hγ1 : γ≤1)
    (hK : γ•(1 : Matrix (Fin k) (Fin k) ℝ)≤K) (hK1 : (K : Matrix (Fin k) (Fin k) ℝ)≤1) :
    let h := mesh (size d N)
    (∑s : Draws W,weight W s*(value hN (H+h•physical A hA W s) A (covarianceLift U K-h^2•(covMatrix W))-
      value hN H A (covarianceLift U K))) ≤
      h^2*realTrace ((covMatrix W)*response hN A hA (covarianceLift U K) H)+fourthCap (size d N)*h^4/24 := by
  let h := mesh (size d N)
  have hr := MSManuscriptSupportedMovement.reduced_bounds U hU K hQ hQC hK1
  let L : selfAdjoint (Matrix (Fin k) (Fin k) ℝ) := ⟨MSManuscriptSupportedMovement.reduced (covMatrix W) U,hr.1.isHermitian⟩
  have hqeq : covarianceLift U L=(covMatrix W) := hr.2.2.2
  let e : Draws W → ℝ := fun s => value hN (H+h•physical A hA W s) A (covarianceLift U K-h^2•(covMatrix W))-value hN H A (covarianceLift U K)
  let q : Draws W → ℝ := fun s => h^2*((1/2:ℝ)*RectangularRidgeCalculus.ownerCenterHessian A (covarianceLift U K)
    (RectangularRidgeTuning.depth N d hN) (weight N d hN) (1/(d : ℝ)) H (physical A hA W s) (physical A hA W s))
  have hp (s : Draws W) : (e s+e (flip W s))/2 ≤ q s+fourthCap (size d N)*h^4/24 := by
    have hb := pair_bound H (physical A hA W s) A hA hAn U hU hN hND hkN K L hr.1 hr.2.2.1
      hH (physical_norm_le_size_square A hA hAn hN W hQ (hQC.trans hC1) s) hγ hγ1 hK hK1 hC1
    rw [hqeq] at hb
    dsimp only [e,q]
    rw [physical_flip,smul_neg,←sub_eq_add_neg]
    linarith
  have he := weighted_pair_le W hQ hq e q hp
  have hqsum : (∑s,weight W s*q s)=h^2*realTrace ((covMatrix W)*response hN A hA (covarianceLift U K) H) := by
    rw [response,←half_hessian_expectation A hA (covarianceLift U K) _ _ _ H W hQ hq,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    dsimp only [q]
    ring
  rw [hqsum] at he
  exact he


open MSManuscriptSupportedOwner

/-- The stored owner itself supplies the reduced positive face, including its
singular embedding into the original coefficient universe. -/
theorem stored_owner (H : selfAdjoint (Matrix (Fin d) (Fin d) ℂ))
    (A : Fin N → Matrix (Fin d) (Fin d) ℂ) (hA : ∀i,(A i).IsHermitian) (hAn : ∀i,‖A i‖≤1)
    (hN : 1 ≤ N) (hND : N ≤ d) (O : Owner N) {γ : ℝ} (hO : O.Valid γ)
    (hC1 : O.physical≤1) (hdim : O.dim≤N)
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin N))) (hQ : (covMatrix W).PosSemidef) (hQC : (covMatrix W)≤O.physical) (hq : 0<realTrace (covMatrix W))
    (hH : ‖(H : Matrix (Fin d) (Fin d) ℂ)‖≤N)
    (hγ : ((2:ℝ)^14)⁻¹≤γ) (hγ1 : γ≤1) :
    let h := mesh (size d N)
    (∑s : Draws W,weight W s*(value hN (H+h•physical A hA W s) A (O.physical-h^2•(covMatrix W))-
      value hN H A O.physical)) ≤
      h^2*realTrace ((covMatrix W)*response hN A hA O.physical H)+fourthCap (size d N)*h^4/24 := by
  have hγ0 : 0 < γ := lt_of_lt_of_le (by positivity) hγ
  let K : selfAdjoint (Matrix (Fin O.dim) (Fin O.dim) ℝ) :=
    ⟨O.matrix,(hO.matrix_posSemidef O hγ0.le).isHermitian⟩
  exact fixed_frame H A hA hAn O.frame hO.1 hN hND hdim K W hQ hQC hq hC1 hH hγ hγ1 hO.2
    (MSManuscriptSupportedMovement.owner_matrix_le_one O hO hC1)

theorem fourth_error_le {P : ℝ} (hP : 1 ≤ P) :
    fourthCap P*mesh P^4/24 ≤ mesh P^2/(2:ℝ)^40 := by
  have hb := fourth_mesh_budget_le hP
  have h0 : 0 ≤ fourthCap P*mesh P^2 := by
    have hp := (big_pos (by linarith : 0 < P) 1040 200).le
    exact mul_nonneg hp (sq_nonneg _)
  have he : fourthCap P*mesh P^2/24 ≤ 1/(2:ℝ)^40 := by nlinarith
  have hh := mul_le_mul_of_nonneg_right he (sq_nonneg (mesh P))
  have he1 (a b : ℝ) : a*b^4/24=(a*b^2/24)*b^2 := by ring
  have he2 (b c : ℝ) : (1/c)*b^2=b^2/c := by ring
  rw [he1,←he2]
  exact hh

/-- Propagation of an actual response bound at the concrete numerical mesh.
The finite preparation test supplies this trace bound in the caller. -/
theorem stored_owner_response (H : selfAdjoint (Matrix (Fin d) (Fin d) ℂ))
    (A : Fin N → Matrix (Fin d) (Fin d) ℂ) (hA : ∀i,(A i).IsHermitian) (hAn : ∀i,‖A i‖≤1)
    (hN : 1 ≤ N) (hND : N ≤ d) (O : Owner N) {γ J : ℝ} (hO : O.Valid γ)
    (hC1 : O.physical≤1) (hdim : O.dim≤N)
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin N))) (hQ : (covMatrix W).PosSemidef) (hQC : (covMatrix W)≤O.physical) (hq : 0<realTrace (covMatrix W))
    (hH : ‖(H : Matrix (Fin d) (Fin d) ℂ)‖≤N)
    (hγ : ((2:ℝ)^14)⁻¹≤γ) (hγ1 : γ≤1)
    (hJ : realTrace (O.physical*response hN A hA O.physical H)≤J) :
    let h := mesh (size d N)
    (∑s : Draws W,weight W s*(value hN (H+h•physical A hA W s) A (O.physical-h^2•(covMatrix W))-
      value hN H A O.physical)) ≤ h^2*(J+1/(2:ℝ)^40) := by
  have hγ0 : 0 < γ := lt_of_lt_of_le (by positivity) hγ
  have hκ : 0 < 1/(d : ℝ) := by
    have hd : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
    positivity
  have hj := (RectangularRidgeCalculus.ownerCoefficientResponse_trace_mono A hA
    (hO.physical_posSemidef O hγ0.le) (RectangularRidgeTuning.depth N d hN)
    (RectangularRidgeTuning.depth_positive N d hN) (weight N d hN) (1/(d : ℝ))
    (weight_positive hN hND) hκ H hQC).trans hJ
  have hh := stored_owner H A hA hAn hN hND O hO hC1 hdim W hQ hQC hq hH hγ hγ1
  have hP : 1 ≤ size d N := by unfold size; linarith [(Nat.cast_nonneg d : (0:ℝ) ≤ d),(Nat.cast_nonneg N : (0:ℝ) ≤ N)]
  have he := fourth_error_le hP
  have ht := mul_le_mul_of_nonneg_left hj (sq_nonneg (mesh (size d N)))
  dsimp only at hh ⊢
  change realTrace ((covMatrix W)*response hN A hA O.physical H) ≤ J at hj
  nlinarith

/-- The covariance is half the high-space projection satisfying the frozen and
radial constraints, and the draws are its uniform signed eigenvectors; the original universe and center bound stay fixed. -/
theorem actual_movement (H : selfAdjoint (Matrix (Fin d) (Fin d) ℂ))
    (A : Fin N → Matrix (Fin d) (Fin d) ℂ) (hA : ∀i,(A i).IsHermitian) (hAn : ∀i,‖A i‖≤1)
    (hN : 1 ≤ N) (hND : N ≤ d) (O : Owner N) {γ J : ℝ} (hO : O.Valid γ)
    (hC1 : O.physical≤1) (hdim : O.dim≤N)
    (F : Finset (Fin N)) (x : EuclideanSpace ℝ (Fin N))
    (hq : 0<realTrace (MSManuscriptNumericalMovement.covariance O.physical F x))
    (hH : ‖(H : Matrix (Fin d) (Fin d) ℂ)‖≤N)
    (hγ : ((2:ℝ)^14)⁻¹≤γ) (hγ1 : γ≤1)
    (hJ : realTrace (O.physical*response hN A hA O.physical H)≤J) :
    let h := mesh (size d N)
    (∑s : MSManuscriptNumericalMovement.Draws O.physical F x,
      MSManuscriptNumericalMovement.weight O.physical F x s*(value hN
        (H+h•ownerPhysicalIncrement A hA (MSManuscriptNumericalMovement.increment O.physical F x s))
        A (MSManuscriptNumericalMovement.nextOwner O.physical F x h)-value hN H A O.physical)) ≤
      h^2*(J+1/(2:ℝ)^40) := by
  have hγ0 : 0 < γ := lt_of_lt_of_le (by positivity) hγ
  have hC := hO.physical_posSemidef O hγ0.le
  exact stored_owner_response H A hA hAn hN hND O hO hC1 hdim (SimpleMS.Movement.Space O.physical F x)
    (SimpleMS.Movement.covariance_posSemidef _ F x)
    (SimpleMS.Movement.covariance_le _ hC F x) hq hH hγ hγ1 hJ

end MatrixSpencer.RectangularRidgeMovementDrift
