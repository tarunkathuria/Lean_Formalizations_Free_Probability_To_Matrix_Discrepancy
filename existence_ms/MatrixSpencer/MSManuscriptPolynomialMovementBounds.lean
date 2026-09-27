import MatrixSpencer.MSManuscriptNumericalWalkBudget
import MatrixSpencer.MSManuscriptNumericalConfig
import MatrixSpencer.MSManuscriptInputRadius
import MatrixSpencer.SigningPotential

/-! Explicit fixed-degree polynomial bounds for the actual square-MS matched
fourth-derivative budget. All derivative quantities are unfolded to the
existing input-derived formulas. This module does not claim a total runtime
bound for the MS numerical algorithm. -/
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.MSManuscriptPolynomialMovementBounds
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
open MSManuscriptNumericalEpochRun MSManuscriptNumericalWalkBudget

/-- These expressions use only additions, multiplications and fixed powers. -/
def direction (N : ℕ) : ℝ := (N:ℝ)*((N:ℝ)+1)
def denominator (N d : ℕ) (R : ℝ) : ℝ := 2*(R+direction N)+2*(N:ℝ)^2+2*((d:ℝ)+1)
def inverseFloor (N d : ℕ) (R : ℝ) : ℝ := 1+(denominator N d R)^2
def value (N d : ℕ) (R : ℝ) : ℝ :=
  2*(d:ℝ)*(R+2*direction N)+16*(d:ℝ)*(N:ℝ)^4+6*(d:ℝ)
def joint (N d : ℕ) (R : ℝ) : ℝ := value N d R*(83886080*inverseFloor N d R)^4
def fourth (N d : ℕ) (R : ℝ) : ℝ :=
  (joint N d R+6*(joint N d R)^2)*(1+2*joint N d R)^4
def uniform (N d : ℕ) (R : ℝ) : ℝ := 1+((N:ℝ)+1)*fourth N d R

lemma sqrt_le_add_one {x : ℝ} (hx : 0≤x) : Real.sqrt x≤x+1 := by
  apply (Real.sqrt_le_iff).mpr
  exact ⟨by linarith,by nlinarith [sq_nonneg x]⟩

lemma direction_le (N : ℕ) : MSManuscriptLDLMoments.directionCap N 1≤direction N := by
  have h:=mul_le_mul_of_nonneg_right (sqrt_le_add_one (Nat.cast_nonneg N)) (Nat.cast_nonneg N)
  simpa [MSManuscriptLDLMoments.directionCap,direction,mul_comm] using h

lemma denominator_pos (N d : ℕ) {R : ℝ} (hR : 0≤R) : 0<denominator N d R := by
  unfold denominator direction
  positivity
lemma inverseFloor_nonneg (N d : ℕ) (R : ℝ) : 0≤ inverseFloor N d R := by unfold inverseFloor;positivity
lemma value_nonneg (N d : ℕ) {R : ℝ} (hR : 0≤R) : 0≤value N d R := by unfold value direction;positivity
lemma joint_nonneg (N d : ℕ) {R : ℝ} (hR : 0≤R) : 0≤joint N d R := by
  exact mul_nonneg (value_nonneg _ _ hR) (pow_nonneg (by have h:=inverseFloor_nonneg N d R;positivity) _)
lemma fourth_nonneg (N d : ℕ) {R : ℝ} (hR : 0≤R) : 0≤fourth N d R := by
  unfold fourth
  have h:=joint_nonneg N d hR
  positivity

lemma floor_inverse_le (N k d : ℕ) (hk : k≤N) (hd : 0<d) {R : ℝ} (hR : 0≤R) :
    (MSManuscriptMatchedFourth.densityFloor (Fin k) (Fin d)
      (R+MSManuscriptLDLMoments.directionCap N 1) 1 N)⁻¹≤ inverseFloor N d R := by
  let b:=MSManuscriptLDLMoments.directionCap N 1
  let D:=2*(R+b)+2*(k:ℝ)*(N:ℝ)+2*Real.sqrt (d:ℝ)
  have hb : 0≤b := by dsimp [b,MSManuscriptLDLMoments.directionCap];positivity
  have hb' : b≤direction N := direction_le N
  have hD : 0<D := by
    have hs:=Real.sqrt_pos.mpr (Nat.cast_pos.mpr hd)
    dsimp [D]
    positivity
  have hDle : D≤denominator N d R := by
    have hk' : (k:ℝ)≤N := Nat.cast_le.mpr hk
    have hs:=sqrt_le_add_one (Nat.cast_nonneg d)
    have hm:=mul_le_mul_of_nonneg_right hk' (Nat.cast_nonneg N)
    dsimp [D,denominator]
    nlinarith
  simp only [MSManuscriptMatchedFourth.densityFloor,MSManuscriptOptimizerFloorScaled.floor,Fintype.card_fin,mul_one]
  change (min 1 ((1/D)^2))⁻¹≤_
  rcases le_total 1 ((1/D)^2) with h|h
  · rw [min_eq_left h]
    simp only [inv_one,le_add_iff_nonneg_right,inverseFloor]
    positivity
  · rw [min_eq_right h]
    have he : ((1/D)^2)⁻¹=D^2 := by field_simp
    rw [he]
    exact (pow_le_pow_left₀ hD.le hDle 2).trans (by unfold inverseFloor;linarith)

lemma actualValue_le (N k d : ℕ) (hk : k≤N) {R : ℝ} (hR : 0≤R) :
    MSManuscriptComplexValueBoundScaled.valueCap (Fin k) (Fin d)
      (R+MSManuscriptLDLMoments.directionCap N 1+MSManuscriptLDLMoments.directionCap N 1) 1 N≤value N d R := by
  have hb:=direction_le N
  have hk' : (k:ℝ)≤N := Nat.cast_le.mpr hk
  have hs:=sqrt_le_add_one (show (0:ℝ)≤8*(k:ℝ)^2*(N:ℝ)^2 by positivity)
  have h2 : Real.sqrt (2:ℝ)≤2 := Real.sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
  have hk2 : (k:ℝ)^2≤(N:ℝ)^2 := pow_le_pow_left₀ (Nat.cast_nonneg k) hk' 2
  have hh : 8*(k:ℝ)^2*(N:ℝ)^2≤8*(N:ℝ)^4 := by nlinarith [mul_le_mul_of_nonneg_right hk2 (sq_nonneg (N:ℝ))]
  unfold MSManuscriptComplexValueBoundScaled.valueCap KSComplexObjectiveBound.valueCap
  simp only [Fintype.card_fin]
  have he : (2:ℝ)*(4*(k:ℝ)^2*(N:ℝ)^2)=8*(k:ℝ)^2*(N:ℝ)^2 := by ring
  rw [he]
  unfold value
  nlinarith [mul_le_mul_of_nonneg_left hs (show (0:ℝ)≤2*d by positivity),
    mul_le_mul_of_nonneg_left h2 (show (0:ℝ)≤2*d by positivity),
    mul_le_mul_of_nonneg_left hh (show (0:ℝ)≤2*d by positivity),
    mul_le_mul_of_nonneg_left hb (show (0:ℝ)≤4*d by positivity)]

lemma joint_le (N k d : ℕ) (hk : k≤N) (hd : 0<d) {R : ℝ} (hR : 0≤R) :
    MSManuscriptMatchedFourth.jointBudget (Fin k) (Fin d)
      (R+MSManuscriptLDLMoments.directionCap N 1) (MSManuscriptLDLMoments.directionCap N 1) 1 ((1/8192)/2) N≤joint N d R := by
  let μ:=MSManuscriptMatchedFourth.densityFloor (Fin k) (Fin d)
    (R+MSManuscriptLDLMoments.directionCap N 1) 1 N
  have hb : 0≤MSManuscriptLDLMoments.directionCap N 1 := by unfold MSManuscriptLDLMoments.directionCap;positivity
  have hμ : 0<μ := by
    simpa only [μ,MSManuscriptMatchedFourth.densityFloor,Fintype.card_fin] using
      MSManuscriptOptimizerFloorScaled.floor_pos (k:=k) hd (Nat.cast_nonneg N) (add_nonneg hR hb) (by norm_num : (0:ℝ)<1)
  have hi:=floor_inverse_le N k d hk hd hR
  have hr : 10/MSManuscriptMatchedComplex.radius ((1/8192)/2) μ=83886080*μ⁻¹ := by
    unfold MSManuscriptMatchedComplex.radius MSManuscriptComplexSourceDomain.radius
    ring
  have hv:=actualValue_le N k d hk hR
  unfold MSManuscriptMatchedFourth.jointBudget MSManuscriptMatchedJointBounds.jointCap
  change _*(10/MSManuscriptMatchedComplex.radius ((1/8192)/2) μ)^4≤_
  rw [hr]
  unfold joint
  exact mul_le_mul hv (pow_le_pow_left₀ (by positivity)
    (mul_le_mul_of_nonneg_left hi (by norm_num)) 4) (by positivity) (value_nonneg _ _ hR)

lemma movement_le (N k d : ℕ) (hk : k≤N) (hd : 0<d) {R : ℝ} (hR : 0≤R) :
    MSManuscriptMovementDrift.movementBudget N k d R 1 (1/8192)≤fourth N d R := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  have hb : 0≤MSManuscriptLDLMoments.directionCap N 1 := by unfold MSManuscriptLDLMoments.directionCap;positivity
  have h:=joint_le N k d hk hd hR
  have hJ:=joint_nonneg N d hR
  have hB:=MSManuscriptMatchedFourth.jointBudget_nonneg (ι:=Fin k) (n:=Fin d)
    (γ:=(1/8192)/2) (L:=(N:ℝ))
    (add_nonneg hR hb) hb (by norm_num : (0:ℝ)≤1)
  let B:=MSManuscriptMatchedFourth.jointBudget (Fin k) (Fin d)
    (R+MSManuscriptLDLMoments.directionCap N 1) (MSManuscriptLDLMoments.directionCap N 1) 1 ((1/8192)/2) N
  change B≤joint N d R at h
  change 0≤B at hB
  have hs:=pow_le_pow_left₀ hB h 2
  have hfirst : B+6*B^2≤joint N d R+6*(joint N d R)^2 := by linarith
  have hlinear : 1+2*B≤1+2*joint N d R := by linarith
  have hpower:=pow_le_pow_left₀ (by linarith : 0≤1+2*B) hlinear 4
  have hp:=mul_le_mul hfirst hpower (pow_nonneg (by linarith : 0≤1+2*B) 4)
    (by positivity : 0≤joint N d R+6*(joint N d R)^2)
  unfold MSManuscriptMovementDrift.movementBudget MSManuscriptMatchedInterval.fourthBudget
    MSManuscriptMatchedFourth.fourthBudget fourth
  change (B+3*B^2/(1/2))*(1+B/(1/2))^4≤_
  convert hp using 1 <;> ring

lemma uniform_le (N d : ℕ) (hd : 0<d) {R : ℝ} (hR : 0≤R) :
    MSManuscriptMovementDrift.uniformBudget N d R 1 (1/8192)≤uniform N d R := by
  unfold MSManuscriptMovementDrift.uniformBudget uniform
  apply add_le_add_left
  calc _≤∑_k∈Finset.range (N+1),fourth N d R := by
          apply Finset.sum_le_sum
          intro k hk
          exact movement_le N k d (by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hk)) hd hR
       _=_ := by simp

lemma uniform_mono (N d : ℕ) {R S : ℝ} (hR : 0≤R) (hRS : R≤S) : uniform N d R≤uniform N d S := by
  have hS : 0≤S := hR.trans hRS
  unfold uniform fourth joint value inverseFloor denominator direction
  gcongr <;> positivity

/-- Entrywise/Frobenius computation of the actual epoch offset is bounded by
its original operator-norm scale. This is a matrix input bound, not a supplied
derivative or optimizer bound. -/
lemma centerCap_le {N d : ℕ} (H : selfAdjoint (Matrix (Fin d) (Fin d) ℂ))
    {B : ℝ} (hB : 0≤B) (hH : ‖(H : Matrix (Fin d) (Fin d) ℂ)‖≤B) :
    MSManuscriptEpochInput.centerCap H (N:=N)≤1+((d:ℝ)+1)*B+(N:ℝ) := by
  have hf:=MSManuscriptInputRadius.frobenius_le (H : Matrix (Fin d) (Fin d) ℂ) H.property
  have hs:=sqrt_le_add_one (Nat.cast_nonneg d)
  have hm:=mul_le_mul hs hH (norm_nonneg _) (by positivity : (0:ℝ)≤(d:ℝ)+1)
  unfold MSManuscriptEpochInput.centerCap KSOwnerInputBounds.matrixBound
  linarith

/-- The actual fourthBudget at its literal numerical tuning is bounded by a
fixed polynomial in label count, dimension, and the offset norm bound. -/
theorem fourthBudget_le {N d : ℕ} (c : Config N d)
    (hθ : c.regularizer=1) (hγ : c.floor=1/8192)
    {B : ℝ} (hB : 0≤B) (hH : ‖(c.offset : Matrix (Fin d) (Fin d) ℂ)‖≤B) :
    fourthBudget c≤uniform N d (1+((d:ℝ)+1)*B+(N:ℝ)) := by
  unfold fourthBudget
  rw [hθ,hγ]
  have hR : 0≤MSManuscriptEpochInput.centerCap c.offset (N:=N) :=
    (MSManuscriptEpochInput.centerCap_pos c.offset (N:=N)).le
  exact (uniform_le N d c.dimension_pos hR).trans
    (uniform_mono N d hR (centerCap_le c.offset hB hH))

theorem ofEpochConfig_fourthBudget_le {N d : ℕ} (cfg : EpochConfig (Fin N) (Fin d)) (hd : 0<d)
    {B : ℝ} (hB : 0≤B) (hH : ‖(cfg.offset : Matrix (Fin d) (Fin d) ℂ)‖≤B) :
    fourthBudget (MSManuscriptNumericalConfig.ofEpochConfig cfg hd)≤
      uniform N d (1+((d:ℝ)+1)*B+(N:ℝ)) :=
  fourthBudget_le _ rfl rfl hB hH

/-- A polynomial mesh reciprocal bound; `M` is the original label count,
whose single global margin is retained when an epoch restricts the live set. -/
def meshCap (N d M : ℕ) (B : ℝ) : ℝ :=
  1000000*((N:ℝ)+1)*((M:ℝ)+1)^2+1000*uniform N d (1+((d:ℝ)+1)*B+(N:ℝ))+200000

lemma fixed_radius_inverse : 4/(MSManuscriptMatchedInterval.radius (1/8192))^2=(131072:ℝ) := by
  have hs : Real.sqrt (1/8192:ℝ)/2≤1/2 := by
    apply (div_le_div_iff_of_pos_right (by norm_num : (0:ℝ)<2)).mpr
    exact (Real.sqrt_le_iff).mpr ⟨by norm_num,by norm_num⟩
  rw [MSManuscriptMatchedInterval.radius,min_eq_right hs,div_pow,
    Real.sq_sqrt (by norm_num : (0:ℝ)≤1/8192)]
  norm_num

theorem mesh_inverse_square_le {N d : ℕ} (c : Config N d)
    (hθ : c.regularizer=1) (hγ : c.floor=1/8192) (he : c.driftError=1/10000)
    (M : ℕ) (hm : c.margin=1/(1000*((M:ℝ)+1)))
    {B : ℝ} (hB : 0≤B) (hH : ‖(c.offset : Matrix (Fin d) (Fin d) ℂ)‖≤B) :
    1/(MSManuscriptNumericalEpochRun.mesh c)^2≤ meshCap N d M B := by
  have h:=MSManuscriptNumericalWalkBudget.mesh_inverse_square_le c
  have hF:=fourthBudget_le c hθ hγ hB hH
  have hF0:0≤fourthBudget c := (fourthBudget_pos c).le
  rw [hγ,he,hm,fixed_radius_inverse] at h
  have heq : ((N:ℝ)+1)/(1/(1000*((M:ℝ)+1)))^2=
      1000000*((N:ℝ)+1)*((M:ℝ)+1)^2 := by field_simp;ring
  rw [heq] at h
  norm_num only [MSManuscriptNumericalEpochLedger.timeLimit] at h
  unfold meshCap
  nlinarith

/-- The original floor-based iteration count, not an alternative mesh. -/
theorem count_le {N d : ℕ} (c : Config N d)
    (hθ : c.regularizer=1) (hγ : c.floor=1/8192) (he : c.driftError=1/10000)
    (M : ℕ) (hm : c.margin=1/(1000*((M:ℝ)+1)))
    {B : ℝ} (hB : 0≤B) (hH : ‖(c.offset : Matrix (Fin d) (Fin d) ℂ)‖≤B) :
    (MSManuscriptNumericalEpochRun.count c : ℝ)≤ meshCap N d M B+1 := by
  have hh:=mesh_inverse_square_le c hθ hγ he M hm hB hH
  have hf:=Nat.floor_le (show 0≤MSManuscriptNumericalEpochLedger.timeLimit/
    (MSManuscriptNumericalEpochRun.mesh c)^2 by
      exact div_nonneg (by norm_num [MSManuscriptNumericalEpochLedger.timeLimit]) (sq_nonneg _))
  have hc : MSManuscriptNumericalEpochLedger.timeLimit/
      (MSManuscriptNumericalEpochRun.mesh c)^2≤1/(MSManuscriptNumericalEpochRun.mesh c)^2 := by
    apply div_le_div_of_nonneg_right (by norm_num [MSManuscriptNumericalEpochLedger.timeLimit]) (sq_nonneg _)
  unfold MSManuscriptNumericalEpochRun.count
  push_cast
  linarith

theorem ofEpochConfig_count_le {N d : ℕ} (cfg : EpochConfig (Fin N) (Fin d)) (hd : 0<d)
    (M : ℕ) (hm : cfg.epsilon=signingEpsilon (Fin M))
    {B : ℝ} (hB : 0≤B) (hH : ‖(cfg.offset : Matrix (Fin d) (Fin d) ℂ)‖≤B) :
    (MSManuscriptNumericalEpochRun.count (MSManuscriptNumericalConfig.ofEpochConfig cfg hd):ℝ)≤ meshCap N d M B+1 := by
  have hm' : (MSManuscriptNumericalConfig.ofEpochConfig cfg hd).margin=
      1/(1000*((M:ℝ)+1)) := by
    simpa only [signingEpsilon,Fintype.card_fin] using hm
  exact count_le (MSManuscriptNumericalConfig.ofEpochConfig cfg hd) rfl rfl rfl M hm' hB hH

end MatrixSpencer.MSManuscriptPolynomialMovementBounds
