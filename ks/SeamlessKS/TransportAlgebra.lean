import SeamlessKS.TransportCurve

/-! Algebra of the supported center with arbitrary coefficient jets. -/
open Matrix Filter Topology
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
noncomputable section
namespace SeamlessKS.TransportAlgebra
open MatrixSpencer MatrixSpencer.KSMovingOwnerHessian MatrixSpencer.KSBalancedSpin
open MatrixSpencer.KSSupportedCenterCurve
open SeamlessKS.TransportCurve

variable {ι n m : Type*} [Fintype ι] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]
local instance {k : Type*} [Fintype k] [DecidableEq k] : CStarAlgebra (Matrix k k ℂ) := {}

theorem curve_coe (V : Matrix n m ℂ)
    (H K : selfAdjoint (Matrix n n ℂ)) (A : ι → selfAdjoint (Matrix n n ℂ))
    {Z U : Matrix m m ℂ} (hZ : Z.IsHermitian) (hU : U.IsHermitian)
    (c : ι → ℝ → ℝ) (q r : ι → ℝ) (t : ℝ) :
    ((TransportCurve.centerCurve (embedding V) H K A Z U c q r t :
      selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ) =
      (H : Matrix n n ℂ)+t • (K : Matrix n n ℂ)+V*(transportLine Z U t)⁻¹*Vᴴ+
        ∑ i, probe (c i) (q i) (r i) t • (A i : Matrix n n ℂ) := by
  simp only [TransportCurve.centerCurve, AddSubgroup.coe_add, selfAdjoint.val_smul,
    AddSubmonoidClass.coe_finset_sum, inverseLine]
  rw [embedding_coe V (transportLine_isHermitian hZ hU t).inv]

theorem velocity_coe (V : Matrix n m ℂ)
    (K : selfAdjoint (Matrix n n ℂ)) (A : ι → selfAdjoint (Matrix n n ℂ))
    {Z U : Matrix m m ℂ} (hZ : Z.IsHermitian) (hU : U.IsHermitian)
    (c cv : ι → ℝ → ℝ) (q r : ι → ℝ) :
    ((TransportCurve.centerVelocity (embedding V) K A Z U c cv q r 0 :
      selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ) =
      (K : Matrix n n ℂ)-V*(Z⁻¹*U*Z⁻¹)*Vᴴ+
        ∑ i, (cv i 0*q i+c i 0*r i) • (A i : Matrix n n ℂ) := by
  simp only [TransportCurve.centerVelocity, AddSubgroup.coe_add, selfAdjoint.val_smul,
    AddSubmonoidClass.coe_finset_sum]
  rw [embedding_coe V (inverseVelocity_isHermitian hZ hU)]
  simp only [inverseVelocity, inverseLine, transportLine, zero_smul, add_zero,
    Matrix.mul_neg, Matrix.neg_mul, ← sub_eq_add_neg, probeVelocity, zero_mul]

theorem acceleration_coe (V : Matrix n m ℂ)
    (A : ι → selfAdjoint (Matrix n n ℂ))
    {Z U : Matrix m m ℂ} (hZ : Z.IsHermitian) (hU : U.IsHermitian)
    (cv ca q r : ι → ℝ) :
    ((TransportCurve.centerAcceleration (embedding V) A Z U cv ca q r :
      selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ) =
      (2:ℝ) • (V*(Z⁻¹*U*Z⁻¹*U*Z⁻¹)*Vᴴ)+
        ∑ i, (ca i*q i+2*cv i*r i) • (A i : Matrix n n ℂ) := by
  simp only [TransportCurve.centerAcceleration, AddSubgroup.coe_add, selfAdjoint.val_smul,
    AddSubmonoidClass.coe_finset_sum]
  rw [embedding_coe V (inverseAcceleration_isHermitian hZ hU)]

theorem velocity_eq_embedded (V : Matrix n m ℂ)
    (K : selfAdjoint (Matrix n n ℂ)) (A : ι → selfAdjoint (Matrix n n ℂ))
    (B : ι → Matrix m m ℂ) (J : Matrix m m ℂ)
    {Z U : Matrix m m ℂ} (hZ : Z.IsHermitian) (hU : U.IsHermitian)
    (u : ℝ) (c cv : ι → ℝ → ℝ) (χ h q : ι → ℝ)
    (hcv : ∀ i, cv i 0 = -2*u*χ i*h i)
    (hA : ∀ i, (A i : Matrix n n ℂ) = V*B i*Vᴴ)
    (hK : (K : Matrix n n ℂ) = V*(∑ i, h i • (J*B i))*Vᴴ) :
    ((TransportCurve.centerVelocity (embedding V) K A Z U c cv q
      (fun i => realTrace (B i*U)) 0 : selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ) =
      V*(physicalForce B J u χ h q-Z⁻¹*U*Z⁻¹+source B (fun i => c i 0) U)*Vᴴ := by
  rw [velocity_coe V K A hZ hU, hK]
  simp_rw [hA]
  have hsum : (∑ i, (cv i 0*q i+c i 0*realTrace (B i*U)) • (V*B i*Vᴴ)) =
      V*((∑ i, (-2*u*χ i*h i*q i) • B i)+source B (fun i => c i 0) U)*Vᴴ := by
    simp only [source, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sum, Matrix.sum_mul,
      Matrix.mul_smul, Matrix.smul_mul, ← Finset.sum_add_distrib, ← add_smul, hcv]
  rw [hsum]
  simp only [physicalForce, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul]
  abel

theorem velocity_zero (V : Matrix n m ℂ)
    (K : selfAdjoint (Matrix n n ℂ)) (A : ι → selfAdjoint (Matrix n n ℂ))
    (B : ι → Matrix m m ℂ) (J : Matrix m m ℂ)
    {Z U : Matrix m m ℂ} (hZ : Z.IsHermitian) (hU : U.IsHermitian)
    (u : ℝ) (c cv : ι → ℝ → ℝ) (χ h q : ι → ℝ)
    (hcv : ∀ i, cv i 0 = -2*u*χ i*h i)
    (hA : ∀ i, (A i : Matrix n n ℂ) = V*B i*Vᴴ)
    (hK : (K : Matrix n n ℂ) = V*(∑ i, h i • (J*B i))*Vᴴ)
    (hzero : physicalForce B J u χ h q-Z⁻¹*U*Z⁻¹+source B (fun i => c i 0) U = 0) :
    TransportCurve.centerVelocity (embedding V) K A Z U c cv q
      (fun i => realTrace (B i*U)) 0 = 0 := by
  apply Subtype.ext
  rw [velocity_eq_embedded V K A B J hZ hU u c cv χ h q hcv hA hK,
    hzero, Matrix.mul_zero, Matrix.zero_mul]
  rfl

theorem acceleration_pairing_le (V : Matrix n m ℂ) (S : Matrix n n ℂ)
    (A : ι → selfAdjoint (Matrix n n ℂ)) (B : ι → Matrix m m ℂ)
    {Z U : Matrix m m ℂ} (hZ : Z.IsHermitian) (hU : U.IsHermitian)
    (u : ℝ) (cv ca χ h q : ι → ℝ)
    (hcv : ∀ i, cv i = -2*u*χ i*h i)
    (hca : ∀ i, ca i ≤ -2*u*h i^2)
    (hpq : ∀ i, 0 ≤ q i * realTrace (S*(A i : Matrix n n ℂ)))
    (hA : ∀ i, (A i : Matrix n n ℂ) = V*B i*Vᴴ) :
    realTrace (S*((TransportCurve.centerAcceleration (embedding V) A Z U cv ca q
      (fun i => realTrace (B i*U)) : selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ)) ≤
      realTrace ((Vᴴ*S*V)*physicalAcceleration B Z U u χ h q) := by
  rw [← MatrixSpencer.KSSupportedCenterCurve.centerAcceleration_pairing V S A B hZ hU u χ h q hA,
    acceleration_coe V A hZ hU,
    MatrixSpencer.KSSupportedCenterCurve.centerAcceleration_coe V A hZ hU]
  simp only [Matrix.mul_add, realTrace_add, Matrix.mul_sum, realTrace_sum,
    Matrix.mul_smul, realTrace_smul]
  apply add_le_add_left
  apply Finset.sum_le_sum
  intro i _
  have hh := mul_le_mul_of_nonneg_right (hca i) (hpq i)
  rw [hcv]
  nlinarith

section SupportedGradient
variable {κ : Type*} [Fintype κ]

theorem curve_eq_supportedGradient (V : Matrix n m ℂ)
    (H K : selfAdjoint (Matrix n n ℂ)) (A : ι → selfAdjoint (Matrix n n ℂ))
    (B : ι → Matrix m m ℂ) (L : κ → Matrix n n ℂ)
    {Z U : Matrix m m ℂ} (hZ : Z.IsHermitian) (hU : U.IsHermitian)
    (c : ι → ℝ → ℝ) (t : ℝ)
    (hsource : KSSafeRetirement.sourceAdjoint L (V*transportLine Z U t*Vᴴ) =
      ∑ i, (c i t*realTrace (B i*transportLine Z U t)) • (A i : Matrix n n ℂ)) :
    ((TransportCurve.centerCurve (embedding V) H K A Z U c
      (fun i => realTrace (Z*B i)) (fun i => realTrace (B i*U)) t :
        selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ) =
      (H : Matrix n n ℂ)+t • (K : Matrix n n ℂ)+
        KSSafeRetirement.supportedGradient L V (transportLine Z U t) := by
  rw [curve_coe V H K A hZ hU]
  unfold KSSafeRetirement.supportedGradient
  rw [hsource, ← add_assoc]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  simp only [probe, transportLine, Matrix.mul_add, Matrix.mul_smul, realTrace_add,
    realTrace_smul, realTrace_mul_comm (B i) Z]

end SupportedGradient
end SeamlessKS.TransportAlgebra
