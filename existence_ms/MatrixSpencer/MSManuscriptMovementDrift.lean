import MatrixSpencer.MSManuscriptMatchedSecond
import MatrixSpencer.MSManuscriptLDLMoments
import MatrixSpencer.MSManuscriptFrameFamily
import MatrixSpencer.MSManuscriptSupportedMovement
import MatrixSpencer.MSManuscriptNumericalMovement
import SimpleMS.UniformMoments

/-!
# Actual finite LDL movement drift

The sampler is the computed LDL-column sampler, the covariance withdrawal is
its exact second moment, and the potential is the original ownerPotential.
The stored-frame version includes singular ambient owners. Its explicit fourth
budget comes from actual complex analyticity and the canonical optimizer;
there is no Taylor, derivative, optimizer, or favorable-draw premise.
-/
open Matrix Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.MSManuscriptMovementDrift
open MSManuscriptLDLMoments MSManuscriptNumericalSamplerData
variable {N k d : ℕ} [Nonempty (Fin d)]
local instance : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
local instance : NormedAddCommGroup (selfAdjoint (Matrix (Fin d) (Fin d) ℂ)) := inferInstance
local instance : NormedSpace ℝ (selfAdjoint (Matrix (Fin d) (Fin d) ℂ)) := inferInstance
local instance : NormedAddCommGroup (selfAdjoint (Matrix (Fin k) (Fin k) ℝ)) := inferInstance
local instance : NormedSpace ℝ (selfAdjoint (Matrix (Fin k) (Fin k) ℝ)) := inferInstance
set_option maxHeartbeats 1200000
attribute [local irreducible] ownerPotential ownerCenterHessian

def movementBudget (N k d : ℕ) (R θ γ : ℝ) : ℝ :=
  MSManuscriptMatchedInterval.fourthBudget (Fin k) (Fin d) R (directionCap N 1) θ γ N

/-- Pairwise Taylor expansion in a stored frame, with the positive covariance
payment discarded only after deriving its exact sign. -/
theorem pair_bound (H B : selfAdjoint (Matrix (Fin d) (Fin d) ℂ))
    (A : Fin N → Matrix (Fin d) (Fin d) ℂ) (hA : ∀i,(A i).IsHermitian) (hAnorm : ∀i,‖A i‖≤1)
    (U : Matrix (Fin N) (Fin k) ℝ) (hU : Uᵀ*U=1)
    (K L : selfAdjoint (Matrix (Fin k) (Fin k) ℝ)) (hL : (L : Matrix (Fin k) (Fin k) ℝ).PosSemidef)
    (hL1 : (L : Matrix (Fin k) (Fin k) ℝ)≤1)
    {θ R b γ h : ℝ} (hθ : 0<θ) (hR : 0≤R) (hb : 0≤b)
    (hH : ‖(H : Matrix (Fin d) (Fin d) ℂ)‖≤R) (hB : ‖(B : Matrix (Fin d) (Fin d) ℂ)‖≤b)
    (hγ : 0<γ) (hγ1 : γ≤1) (hK : γ•(1 : Matrix (Fin k) (Fin k) ℝ)≤K)
    (hK1 : (K : Matrix (Fin k) (Fin k) ℝ)≤1) (hh : 0<h) (hstep : h≤MSManuscriptMatchedInterval.radius γ/2) :
    (ownerPotential (H+h•B) A (covarianceLift U K-h^2•covarianceLift U L) θ+
      ownerPotential (H-h•B) A (covarianceLift U K-h^2•covarianceLift U L) θ)/2-
        ownerPotential H A (covarianceLift U K) θ ≤
      h^2*((1/2:ℝ)*ownerCenterHessian A (covarianceLift U K) θ H B B)+
        MSManuscriptMatchedInterval.fourthBudget (Fin k) (Fin d) R b θ γ N*h^4/24 := by
  let f : ℝ → ℝ := fun t => ownerPotential (MSManuscriptMatchedJointBounds.center H B t)
    (mixFamily A U) (MSManuscriptMatchedJointBounds.covariance K L t) θ
  let M := MSManuscriptMatchedInterval.fourthBudget (Fin k) (Fin d) R b θ γ N
  have hmix := mixFamily_isHermitian A U hA
  have hmixnorm := MSManuscriptFrameFamily.family_norm_le A hAnorm U hU
  have ht : |(f h+f (-h))/2-f 0-iteratedDeriv 2 f 0*h^2/2|≤M*h^4/24 :=
    MSManuscriptMatchedInterval.symmetric_average_error H B (mixFamily A U) hmix (Nat.cast_nonneg N) hmixnorm
      K L hL hL1 hθ hR hb hH hB hγ hγ1 hK hK1 hh hstep
  have hKp : (K : Matrix (Fin k) (Fin k) ℝ).PosDef := by
    simpa only [add_sub_cancel] using (Matrix.PosDef.one.smul hγ).add_posSemidef (Matrix.le_iff.mp hK)
  have hs := MSManuscriptMatchedSecond.second_le H B (mixFamily A U) hmix K L hθ hKp hL
  change iteratedDeriv 2 f 0/2≤(1/2:ℝ)*ownerCenterHessian (mixFamily A U) K θ H B B at hs
  rw [←ownerCenterHessian_covarianceLift A U K θ H] at hs
  have hp : (f h+f (-h))/2-f 0≤h^2*((1/2:ℝ)*ownerCenterHessian A (covarianceLift U K) θ H B B)+M*h^4/24 := by
    have hs' := mul_le_mul_of_nonneg_right hs (sq_nonneg h)
    have ht' := (abs_le.mp ht).2
    nlinarith
  have he (t : ℝ) : f t=ownerPotential (H+t•B) A (covarianceLift U K-t^2•covarianceLift U L) θ := by
    rw [←covarianceLift_sub_smul,ownerPotential_covarianceLift]
    rfl
  rw [he h,he (-h),he 0] at hp
  simpa only [neg_smul,sub_eq_add_neg,neg_sq,zero_smul,neg_zero,add_zero,zero_pow (by norm_num : (2:ℕ)≠0),sub_zero] using hp

/-- Expected drift of the actual finite LDL update on a positive stored face. -/
theorem fixed_frame (H : selfAdjoint (Matrix (Fin d) (Fin d) ℂ))
    (A : Fin N → Matrix (Fin d) (Fin d) ℂ) (hA : ∀i,(A i).IsHermitian) (hAnorm : ∀i,‖A i‖≤1)
    (U : Matrix (Fin N) (Fin k) ℝ) (hU : Uᵀ*U=1)
    (K : selfAdjoint (Matrix (Fin k) (Fin k) ℝ))
    (Q : Matrix (Fin N) (Fin N) ℝ) (hQ : Q.PosSemidef) (hQC : Q≤covarianceLift U K)
    (hq : 0<realTrace Q) (hC1 : covarianceLift U K≤1)
    {θ R γ h : ℝ} (hθ : 0<θ) (hR : 0≤R) (hH : ‖(H : Matrix (Fin d) (Fin d) ℂ)‖≤R)
    (hγ : 0<γ) (hγ1 : γ≤1) (hK : γ•(1 : Matrix (Fin k) (Fin k) ℝ)≤K)
    (hK1 : (K : Matrix (Fin k) (Fin k) ℝ)≤1) (hh : 0<h) (hstep : h≤MSManuscriptMatchedInterval.radius γ/2) :
    (∑s : Draws Q,weight Q s*(
      ownerPotential (H+h•physical A hA Q s) A (covarianceLift U K-h^2•Q) θ-
      ownerPotential H A (covarianceLift U K) θ)) ≤
        h^2*realTrace (Q*ownerCoefficientResponse A hA (covarianceLift U K) θ H)+
          movementBudget N k d R θ γ*h^4/24 := by
  have hr := MSManuscriptSupportedMovement.reduced_bounds U hU K hQ hQC hK1
  let L : selfAdjoint (Matrix (Fin k) (Fin k) ℝ) := ⟨MSManuscriptSupportedMovement.reduced Q U,hr.1.isHermitian⟩
  have hqeq : covarianceLift U L=Q := hr.2.2.2
  let e : Draws Q → ℝ := fun s => ownerPotential (H+h•physical A hA Q s) A (covarianceLift U K-h^2•Q) θ-
    ownerPotential H A (covarianceLift U K) θ
  let q : Draws Q → ℝ := fun s => h^2*((1/2:ℝ)*ownerCenterHessian A (covarianceLift U K) θ H
    (physical A hA Q s) (physical A hA Q s))
  have hp (s : Draws Q) : (e s+e (flip Q s))/2≤q s+movementBudget N k d R θ γ*h^4/24 := by
    have hb := pair_bound H (physical A hA Q s) A hA hAnorm U hU K L hr.1 hr.2.2.1
      hθ hR (directionCap_nonneg (N := N) (by norm_num : (0:ℝ)≤1)) hH
      (physical_norm_le A hA (by norm_num : (0:ℝ)≤1) hAnorm Q hQ (hQC.trans hC1) s)
      hγ hγ1 hK hK1 hh hstep
    rw [hqeq] at hb
    dsimp only [e,q]
    rw [physical_flip,smul_neg,←sub_eq_add_neg]
    dsimp only [movementBudget]
    linarith
  have he := weighted_pair_le Q hQ hq e q hp
  have hqsum : (∑s,weight Q s*q s)=h^2*realTrace (Q*ownerCoefficientResponse A hA (covarianceLift U K) θ H) := by
    rw [←half_hessian_expectation A hA (covarianceLift U K) θ H Q hQ hq,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    dsimp only [q]
    ring
  rw [hqsum] at he
  exact he


theorem movementBudget_nonneg {R θ γ : ℝ} (hR : 0≤R) (hθ : 0<θ) :
    0 ≤ movementBudget N k d R θ γ := by
  have hb := directionCap_nonneg (N := N) (by norm_num : (0:ℝ)≤1)
  exact MSManuscriptMatchedFourth.fourthBudget_nonneg (add_nonneg hR hb) hb hθ

/-- One cap valid for every support dimension encountered in an epoch. -/
def uniformBudget (N d : ℕ) (R θ γ : ℝ) : ℝ :=
  1+∑k∈Finset.range (N+1),movementBudget N k d R θ γ

theorem uniformBudget_pos {R θ γ : ℝ} (hR : 0≤R) (hθ : 0<θ) :
    0<uniformBudget N d R θ γ := by
  have hs : 0≤∑k∈Finset.range (N+1),movementBudget N k d R θ γ :=
    Finset.sum_nonneg (fun k _ => movementBudget_nonneg hR hθ)
  unfold uniformBudget
  linarith

theorem movementBudget_le_uniform {R θ γ : ℝ} (hR : 0≤R) (hθ : 0<θ) (hk : k≤N) :
    movementBudget N k d R θ γ≤uniformBudget N d R θ γ := by
  have hs := Finset.single_le_sum (fun j (_ : j∈Finset.range (N+1)) =>
    movementBudget_nonneg (N := N) (k := j) (d := d) (γ := γ) hR hθ)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
  unfold uniformBudget
  linarith

open MSManuscriptSupportedOwner

/-- The stored owner supplies its frame, reduced lower bound and upper bound;
no reduced-covariance or support correspondence is supplied by the caller. -/
theorem stored_owner (H : selfAdjoint (Matrix (Fin d) (Fin d) ℂ))
    (A : Fin N → Matrix (Fin d) (Fin d) ℂ) (hA : ∀i,(A i).IsHermitian) (hAnorm : ∀i,‖A i‖≤1)
    (O : Owner N) {θ R γ h : ℝ} (hO : O.Valid γ) (hC1 : O.physical≤1)
    (Q : Matrix (Fin N) (Fin N) ℝ) (hQ : Q.PosSemidef) (hQC : Q≤O.physical) (hq : 0<realTrace Q)
    (hθ : 0<θ) (hR : 0≤R) (hH : ‖(H : Matrix (Fin d) (Fin d) ℂ)‖≤R)
    (hγ : 0<γ) (hγ1 : γ≤1) (hh : 0<h) (hstep : h≤MSManuscriptMatchedInterval.radius γ/2) :
    (∑s : Draws Q,weight Q s*(ownerPotential (H+h•physical A hA Q s) A (O.physical-h^2•Q) θ-
      ownerPotential H A O.physical θ)) ≤
        h^2*realTrace (Q*ownerCoefficientResponse A hA O.physical θ H)+
          movementBudget N O.dim d R θ γ*h^4/24 := by
  let K : selfAdjoint (Matrix (Fin O.dim) (Fin O.dim) ℝ) :=
    ⟨O.matrix,(hO.matrix_posSemidef O hγ.le).isHermitian⟩
  exact fixed_frame H A hA hAnorm O.frame hO.1 K Q hQ hQC hq hC1
    hθ hR hH hγ hγ1 hO.2 (MSManuscriptSupportedMovement.owner_matrix_le_one O hO hC1) hh hstep

/-- A supplied scalar response bound is propagated by the actual LDL sampler.
The preparation module proves this response bound from its numerical tests. -/
theorem stored_owner_response (H : selfAdjoint (Matrix (Fin d) (Fin d) ℂ))
    (A : Fin N → Matrix (Fin d) (Fin d) ℂ) (hA : ∀i,(A i).IsHermitian) (hAnorm : ∀i,‖A i‖≤1)
    (O : Owner N) {θ R γ h J : ℝ} (hO : O.Valid γ) (hC1 : O.physical≤1) (hdim : O.dim≤N)
    (Q : Matrix (Fin N) (Fin N) ℝ) (hQ : Q.PosSemidef) (hQC : Q≤O.physical) (hq : 0<realTrace Q)
    (hθ : 0<θ) (hR : 0≤R) (hH : ‖(H : Matrix (Fin d) (Fin d) ℂ)‖≤R)
    (hγ : 0<γ) (hγ1 : γ≤1) (hh : 0<h) (hstep : h≤MSManuscriptMatchedInterval.radius γ/2)
    (hJ : realTrace (O.physical*ownerCoefficientResponse A hA O.physical θ H)≤J) :
    (∑s : Draws Q,weight Q s*(ownerPotential (H+h•physical A hA Q s) A (O.physical-h^2•Q) θ-
      ownerPotential H A O.physical θ)) ≤h^2*J+uniformBudget N d R θ γ*h^4/24 := by
  refine (stored_owner H A hA hAnorm O hO hC1 Q hQ hQC hq hθ hR hH hγ hγ1 hh hstep).trans ?_
  have hj := (ownerCoefficientResponse_trace_mono A hA (hO.physical_posSemidef O hγ.le) hθ H hQC).trans hJ
  have hm := movementBudget_le_uniform (γ := γ) (d := d) hR hθ hdim
  exact add_le_add (mul_le_mul_of_nonneg_left hj (sq_nonneg h))
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hm (by positivity)) (by norm_num))

theorem uniform_fixed_frame (H : selfAdjoint (Matrix (Fin d) (Fin d) ℂ))
    (A : Fin N → Matrix (Fin d) (Fin d) ℂ) (hA : ∀i,(A i).IsHermitian) (hAnorm : ∀i,‖A i‖≤1)
    (U : Matrix (Fin N) (Fin k) ℝ) (hU : Uᵀ*U=1)
    (K : selfAdjoint (Matrix (Fin k) (Fin k) ℝ))
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin N))) (hQ : (SimpleMS.UniformMoments.covMatrix W).PosSemidef) (hQC : (SimpleMS.UniformMoments.covMatrix W)≤covarianceLift U K)
    (hq : 0<realTrace (SimpleMS.UniformMoments.covMatrix W)) (hC1 : covarianceLift U K≤1)
    {θ R γ h : ℝ} (hθ : 0<θ) (hR : 0≤R) (hH : ‖(H : Matrix (Fin d) (Fin d) ℂ)‖≤R)
    (hγ : 0<γ) (hγ1 : γ≤1) (hK : γ•(1 : Matrix (Fin k) (Fin k) ℝ)≤K)
    (hK1 : (K : Matrix (Fin k) (Fin k) ℝ)≤1) (hh : 0<h) (hstep : h≤MSManuscriptMatchedInterval.radius γ/2) :
    (∑s : SimpleMS.UniformSampler.Draws W,SimpleMS.UniformSampler.weight W s*(
      ownerPotential (H+h•SimpleMS.UniformMoments.physical A hA W s) A (covarianceLift U K-h^2•(SimpleMS.UniformMoments.covMatrix W)) θ-
      ownerPotential H A (covarianceLift U K) θ)) ≤
        h^2*realTrace ((SimpleMS.UniformMoments.covMatrix W)*ownerCoefficientResponse A hA (covarianceLift U K) θ H)+
          movementBudget N k d R θ γ*h^4/24 := by
  have hr := MSManuscriptSupportedMovement.reduced_bounds U hU K hQ hQC hK1
  let L : selfAdjoint (Matrix (Fin k) (Fin k) ℝ) := ⟨MSManuscriptSupportedMovement.reduced (SimpleMS.UniformMoments.covMatrix W) U,hr.1.isHermitian⟩
  have hqeq : covarianceLift U L=(SimpleMS.UniformMoments.covMatrix W) := hr.2.2.2
  let e : SimpleMS.UniformSampler.Draws W → ℝ := fun s => ownerPotential (H+h•SimpleMS.UniformMoments.physical A hA W s) A (covarianceLift U K-h^2•(SimpleMS.UniformMoments.covMatrix W)) θ-
    ownerPotential H A (covarianceLift U K) θ
  let q : SimpleMS.UniformSampler.Draws W → ℝ := fun s => h^2*((1/2:ℝ)*ownerCenterHessian A (covarianceLift U K) θ H
    (SimpleMS.UniformMoments.physical A hA W s) (SimpleMS.UniformMoments.physical A hA W s))
  have hp (s : SimpleMS.UniformSampler.Draws W) : (e s+e (SimpleMS.UniformMoments.flip W s))/2≤q s+movementBudget N k d R θ γ*h^4/24 := by
    have hb := pair_bound H (SimpleMS.UniformMoments.physical A hA W s) A hA hAnorm U hU K L hr.1 hr.2.2.1
      hθ hR (directionCap_nonneg (N := N) (by norm_num : (0:ℝ)≤1)) hH
      (SimpleMS.UniformMoments.physical_norm_le A hA (by norm_num : (0:ℝ)≤1) hAnorm W hQ (hQC.trans hC1) s)
      hγ hγ1 hK hK1 hh hstep
    rw [hqeq] at hb
    dsimp only [e,q]
    rw [SimpleMS.UniformMoments.physical_flip,smul_neg,←sub_eq_add_neg]
    dsimp only [movementBudget]
    linarith
  have he := SimpleMS.UniformMoments.weighted_pair_le W hQ hq e q hp
  have hqsum : (∑s,SimpleMS.UniformSampler.weight W s*q s)=h^2*realTrace ((SimpleMS.UniformMoments.covMatrix W)*ownerCoefficientResponse A hA (covarianceLift U K) θ H) := by
    rw [←SimpleMS.UniformMoments.half_hessian_expectation A hA (covarianceLift U K) θ H W hQ hq,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    dsimp only [q]
    ring
  rw [hqsum] at he
  exact he

theorem uniform_stored_owner (H : selfAdjoint (Matrix (Fin d) (Fin d) ℂ))
    (A : Fin N → Matrix (Fin d) (Fin d) ℂ) (hA : ∀i,(A i).IsHermitian) (hAnorm : ∀i,‖A i‖≤1)
    (O : Owner N) {θ R γ h : ℝ} (hO : O.Valid γ) (hC1 : O.physical≤1)
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin N))) (hQ : (SimpleMS.UniformMoments.covMatrix W).PosSemidef) (hQC : (SimpleMS.UniformMoments.covMatrix W)≤O.physical) (hq : 0<realTrace (SimpleMS.UniformMoments.covMatrix W))
    (hθ : 0<θ) (hR : 0≤R) (hH : ‖(H : Matrix (Fin d) (Fin d) ℂ)‖≤R)
    (hγ : 0<γ) (hγ1 : γ≤1) (hh : 0<h) (hstep : h≤MSManuscriptMatchedInterval.radius γ/2) :
    (∑s : SimpleMS.UniformSampler.Draws W,SimpleMS.UniformSampler.weight W s*(ownerPotential (H+h•SimpleMS.UniformMoments.physical A hA W s) A (O.physical-h^2•(SimpleMS.UniformMoments.covMatrix W)) θ-
      ownerPotential H A O.physical θ)) ≤
        h^2*realTrace ((SimpleMS.UniformMoments.covMatrix W)*ownerCoefficientResponse A hA O.physical θ H)+
          movementBudget N O.dim d R θ γ*h^4/24 := by
  let K : selfAdjoint (Matrix (Fin O.dim) (Fin O.dim) ℝ) :=
    ⟨O.matrix,(hO.matrix_posSemidef O hγ.le).isHermitian⟩
  exact uniform_fixed_frame H A hA hAnorm O.frame hO.1 K W hQ hQC hq hC1
    hθ hR hH hγ hγ1 hO.2 (MSManuscriptSupportedMovement.owner_matrix_le_one O hO hC1) hh hstep


theorem uniform_stored_owner_response (H : selfAdjoint (Matrix (Fin d) (Fin d) ℂ))
    (A : Fin N → Matrix (Fin d) (Fin d) ℂ) (hA : ∀i,(A i).IsHermitian) (hAnorm : ∀i,‖A i‖≤1)
    (O : Owner N) {θ R γ h J : ℝ} (hO : O.Valid γ) (hC1 : O.physical≤1) (hdim : O.dim≤N)
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin N))) (hQ : (SimpleMS.UniformMoments.covMatrix W).PosSemidef) (hQC : (SimpleMS.UniformMoments.covMatrix W)≤O.physical) (hq : 0<realTrace (SimpleMS.UniformMoments.covMatrix W))
    (hθ : 0<θ) (hR : 0≤R) (hH : ‖(H : Matrix (Fin d) (Fin d) ℂ)‖≤R)
    (hγ : 0<γ) (hγ1 : γ≤1) (hh : 0<h) (hstep : h≤MSManuscriptMatchedInterval.radius γ/2)
    (hJ : realTrace (O.physical*ownerCoefficientResponse A hA O.physical θ H)≤J) :
    (∑s : SimpleMS.UniformSampler.Draws W,SimpleMS.UniformSampler.weight W s*(ownerPotential (H+h•SimpleMS.UniformMoments.physical A hA W s) A (O.physical-h^2•(SimpleMS.UniformMoments.covMatrix W)) θ-
      ownerPotential H A O.physical θ)) ≤h^2*J+uniformBudget N d R θ γ*h^4/24 := by
  refine (uniform_stored_owner H A hA hAnorm O hO hC1 W hQ hQC hq hθ hR hH hγ hγ1 hh hstep).trans ?_
  have hj := (ownerCoefficientResponse_trace_mono A hA (hO.physical_posSemidef O hγ.le) hθ H hQC).trans hJ
  have hm := movementBudget_le_uniform (γ := γ) (d := d) hR hθ hdim
  exact add_le_add (mul_le_mul_of_nonneg_left hj (sq_nonneg h))
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hm (by positivity)) (by norm_num))



theorem actual_movement (H : selfAdjoint (Matrix (Fin d) (Fin d) ℂ))
    (A : Fin N → Matrix (Fin d) (Fin d) ℂ) (hA : ∀i,(A i).IsHermitian) (hAnorm : ∀i,‖A i‖≤1)
    (O : Owner N) {θ R γ h J : ℝ} (hO : O.Valid γ) (hC1 : O.physical≤1) (hdim : O.dim≤N)
    (F : Finset (Fin N)) (x : EuclideanSpace ℝ (Fin N))
    (hq : 0<realTrace (MSManuscriptNumericalMovement.covariance O.physical F x))
    (hθ : 0<θ) (hR : 0≤R) (hH : ‖(H : Matrix (Fin d) (Fin d) ℂ)‖≤R)
    (hγ : 0<γ) (hγ1 : γ≤1) (hh : 0<h) (hstep : h≤MSManuscriptMatchedInterval.radius γ/2)
    (hJ : realTrace (O.physical*ownerCoefficientResponse A hA O.physical θ H)≤J) :
    (∑s : MSManuscriptNumericalMovement.Draws O.physical F x,
      MSManuscriptNumericalMovement.weight O.physical F x s*(
        ownerPotential (H+h•ownerPhysicalIncrement A hA (MSManuscriptNumericalMovement.increment O.physical F x s))
          A (MSManuscriptNumericalMovement.nextOwner O.physical F x h) θ-
        ownerPotential H A O.physical θ)) ≤h^2*J+uniformBudget N d R θ γ*h^4/24 := by
  have hC := hO.physical_posSemidef O hγ.le
  exact uniform_stored_owner_response H A hA hAnorm O hO hC1 hdim
    (SimpleMS.Movement.Space O.physical F x)
    (SimpleMS.Movement.covariance_posSemidef _ F x)
    (SimpleMS.Movement.covariance_le _ hC F x) hq hθ hR hH hγ hγ1 hh hstep hJ

end MatrixSpencer.MSManuscriptMovementDrift
