import MatrixSpencer.KSSpinActualDescent
import MatrixSpencer.KSArbitraryTransportContact

/-! The full Hermitian moving center obtained by embedding a fixed physical support. -/

open Matrix
open Filter Topology
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
noncomputable section
namespace MatrixSpencer.KSSupportedCenterCurve
open KSMovingOwnerHessian KSBalancedSpin

variable {ι n m : Type*} [Fintype ι] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]
local instance {k : Type*} [Fintype k] [DecidableEq k] : CStarAlgebra (Matrix k k ℂ) := {}

def embeddingLinear (V : Matrix n m ℂ) : Matrix m m ℂ →ₗ[ℝ] Matrix n n ℂ where
  toFun X := V * X * Vᴴ
  map_add' X Y := by simp only [Matrix.mul_add, Matrix.add_mul]
  map_smul' a X := by simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]

def embedding (V : Matrix n m ℂ) : Matrix m m ℂ →L[ℝ] selfAdjoint (Matrix n n ℂ) :=
  hermitianProjection.comp (embeddingLinear V).toContinuousLinearMap

theorem embedding_coe (V : Matrix n m ℂ) {X : Matrix m m ℂ} (hX : X.IsHermitian) :
    ((embedding V X : selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ) = V * X * Vᴴ := by
  apply IsSelfAdjoint.coe_selfAdjointPart_apply
  exact Matrix.isHermitian_mul_mul_conjTranspose V hX

theorem transportLine_isHermitian {Z U : Matrix m m ℂ} (hZ : Z.IsHermitian)
    (hU : U.IsHermitian) (t : ℝ) : (transportLine Z U t).IsHermitian := by
  simp only [transportLine, Matrix.IsHermitian, Matrix.conjTranspose_add,
    Matrix.conjTranspose_smul, star_trivial, hZ.eq, hU.eq]

theorem inverseVelocity_isHermitian {Z U : Matrix m m ℂ} (hZ : Z.IsHermitian)
    (hU : U.IsHermitian) : (inverseVelocity Z U 0).IsHermitian := by
  simp only [inverseVelocity, inverseLine, transportLine, zero_smul, add_zero,
    Matrix.IsHermitian, Matrix.conjTranspose_neg, Matrix.conjTranspose_mul, hZ.inv.eq, hU.eq,
    Matrix.mul_assoc]

theorem inverseAcceleration_isHermitian {Z U : Matrix m m ℂ}
    (hZ : Z.IsHermitian) (hU : U.IsHermitian) :
    (Z⁻¹ * U * Z⁻¹ * U * Z⁻¹).IsHermitian := by
  simp only [Matrix.IsHermitian, Matrix.conjTranspose_mul, hZ.inv.eq, hU.eq, Matrix.mul_assoc]

theorem centerCurve_coe (V : Matrix n m ℂ)
    (H K : selfAdjoint (Matrix n n ℂ)) (A : ι → selfAdjoint (Matrix n n ℂ))
    {Z U : Matrix m m ℂ} (hZ : Z.IsHermitian) (hU : U.IsHermitian)
    (u : ℝ) (x h q r : ι → ℝ) (t : ℝ) :
    ((centerCurve (embedding V) H K A Z U u x h q r t : selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ) =
      (H : Matrix n n ℂ) + t • (K : Matrix n n ℂ) + V * (transportLine Z U t)⁻¹ * Vᴴ +
        ∑ i, ownerProbe u (x i) (h i) (q i) (r i) t • (A i : Matrix n n ℂ) := by
  simp only [centerCurve, AddSubgroup.coe_add, selfAdjoint.val_smul,
    AddSubmonoidClass.coe_finset_sum, inverseLine]
  rw [embedding_coe V (transportLine_isHermitian hZ hU t).inv]

theorem centerVelocity_coe (V : Matrix n m ℂ)
    (K : selfAdjoint (Matrix n n ℂ)) (A : ι → selfAdjoint (Matrix n n ℂ))
    {Z U : Matrix m m ℂ} (hZ : Z.IsHermitian) (hU : U.IsHermitian)
    (u : ℝ) (x h q r : ι → ℝ) :
    ((centerVelocity (embedding V) K A Z U u x h q r 0 : selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ) =
      (K : Matrix n n ℂ) - V * (Z⁻¹ * U * Z⁻¹) * Vᴴ +
        ∑ i, (u * (-2 * h i * x i * q i + (1 - x i ^ 2) * r i)) • (A i : Matrix n n ℂ) := by
  simp only [centerVelocity, AddSubgroup.coe_add, selfAdjoint.val_smul,
    AddSubmonoidClass.coe_finset_sum]
  rw [embedding_coe V (inverseVelocity_isHermitian hZ hU)]
  simp only [inverseVelocity, inverseLine, transportLine, zero_smul, add_zero,
    Matrix.mul_neg, Matrix.neg_mul, ← sub_eq_add_neg, ownerProbeVelocity, zero_mul]

theorem centerAcceleration_coe (V : Matrix n m ℂ)
    (A : ι → selfAdjoint (Matrix n n ℂ))
    {Z U : Matrix m m ℂ} (hZ : Z.IsHermitian) (hU : U.IsHermitian)
    (u : ℝ) (x h q r : ι → ℝ) :
    ((centerAcceleration (embedding V) A Z U u x h q r : selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ) =
      (2 : ℝ) • (V * (Z⁻¹ * U * Z⁻¹ * U * Z⁻¹) * Vᴴ) +
        ∑ i, (-2 * u * h i ^ 2 * q i - 4 * u * x i * h i * r i) • (A i : Matrix n n ℂ) := by
  simp only [centerAcceleration, AddSubgroup.coe_add, selfAdjoint.val_smul,
    AddSubmonoidClass.coe_finset_sum]
  rw [embedding_coe V (inverseAcceleration_isHermitian hZ hU)]

theorem centerVelocity_eq_embedded (V : Matrix n m ℂ)
    (K : selfAdjoint (Matrix n n ℂ)) (A : ι → selfAdjoint (Matrix n n ℂ))
    (B : ι → Matrix m m ℂ) (J : Matrix m m ℂ)
    {Z U : Matrix m m ℂ} (hZ : Z.IsHermitian) (hU : U.IsHermitian)
    (u : ℝ) (c x h q : ι → ℝ) (hc : ∀ i, c i = u * (1 - x i ^ 2))
    (hA : ∀ i, (A i : Matrix n n ℂ) = V * B i * Vᴴ)
    (hK : (K : Matrix n n ℂ) = V * (∑ i, h i • (J * B i)) * Vᴴ) :
    ((centerVelocity (embedding V) K A Z U u x h q
      (fun i => realTrace (B i * U)) 0 : selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ) =
      V * (physicalForce B J u x h q - Z⁻¹ * U * Z⁻¹ + source B c U) * Vᴴ := by
  rw [centerVelocity_coe V K A hZ hU, hK]
  simp_rw [hA]
  have hsum : (∑ i, (u * (-2 * h i * x i * q i + (1 - x i ^ 2) * realTrace (B i * U))) •
      (V * B i * Vᴴ)) = V *
      ((∑ i, (-2 * u * x i * h i * q i) • B i) + source B c U) * Vᴴ := by
    simp only [source, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sum, Matrix.sum_mul,
      Matrix.mul_smul, Matrix.smul_mul, ← Finset.sum_add_distrib, ← add_smul]
    apply Finset.sum_congr rfl
    intro i _
    rw [hc]
    congr 1
    ring
  rw [hsum]
  simp only [physicalForce, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul]
  abel

theorem centerVelocity_zero (V : Matrix n m ℂ)
    (K : selfAdjoint (Matrix n n ℂ)) (A : ι → selfAdjoint (Matrix n n ℂ))
    (B : ι → Matrix m m ℂ) (J : Matrix m m ℂ)
    {Z U : Matrix m m ℂ} (hZ : Z.IsHermitian) (hU : U.IsHermitian)
    (u : ℝ) (c x h q : ι → ℝ) (hc : ∀ i, c i = u * (1 - x i ^ 2))
    (hA : ∀ i, (A i : Matrix n n ℂ) = V * B i * Vᴴ)
    (hK : (K : Matrix n n ℂ) = V * (∑ i, h i • (J * B i)) * Vᴴ)
    (hzero : physicalForce B J u x h q - Z⁻¹ * U * Z⁻¹ + source B c U = 0) :
    centerVelocity (embedding V) K A Z U u x h q (fun i => realTrace (B i * U)) 0 = 0 := by
  apply Subtype.ext
  rw [centerVelocity_eq_embedded V K A B J hZ hU u c x h q hc hA hK, hzero,
    Matrix.mul_zero, Matrix.zero_mul]
  rfl

theorem centerAcceleration_eq_embedded (V : Matrix n m ℂ)
    (A : ι → selfAdjoint (Matrix n n ℂ)) (B : ι → Matrix m m ℂ)
    {Z U : Matrix m m ℂ} (hZ : Z.IsHermitian) (hU : U.IsHermitian)
    (u : ℝ) (x h q : ι → ℝ)
    (hA : ∀ i, (A i : Matrix n n ℂ) = V * B i * Vᴴ) :
    ((centerAcceleration (embedding V) A Z U u x h q
      (fun i => realTrace (B i * U)) : selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ) =
      V * physicalAcceleration B Z U u x h q * Vᴴ := by
  rw [centerAcceleration_coe V A hZ hU]
  simp only [hA, physicalAcceleration, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_sum, Matrix.sum_mul]

theorem centerAcceleration_pairing (V : Matrix n m ℂ) (S : Matrix n n ℂ)
    (A : ι → selfAdjoint (Matrix n n ℂ)) (B : ι → Matrix m m ℂ)
    {Z U : Matrix m m ℂ} (hZ : Z.IsHermitian) (hU : U.IsHermitian)
    (u : ℝ) (x h q : ι → ℝ)
    (hA : ∀ i, (A i : Matrix n n ℂ) = V * B i * Vᴴ) :
    realTrace (S * ((centerAcceleration (embedding V) A Z U u x h q
      (fun i => realTrace (B i * U)) : selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ)) =
      realTrace ((Vᴴ * S * V) * physicalAcceleration B Z U u x h q) := by
  rw [centerAcceleration_eq_embedded V A B hZ hU u x h q hA, realTrace_mul_comm]
  rw [KSSafeRetirement.realTrace_embedded_mul, realTrace_mul_comm]

section SupportedGradient
variable {κ : Type*} [Fintype κ]

theorem centerCurve_eq_supportedGradient (V : Matrix n m ℂ)
    (H K : selfAdjoint (Matrix n n ℂ)) (A : ι → selfAdjoint (Matrix n n ℂ))
    (B : ι → Matrix m m ℂ) (L : κ → Matrix n n ℂ)
    {Z U : Matrix m m ℂ} (hZ : Z.IsHermitian) (hU : U.IsHermitian)
    (u : ℝ) (x h : ι → ℝ) (t : ℝ)
    (hsource : KSSafeRetirement.sourceAdjoint L (V * transportLine Z U t * Vᴴ) =
      ∑ i, (u * (1 - (x i + t * h i) ^ 2) * realTrace (B i * transportLine Z U t)) •
        (A i : Matrix n n ℂ)) :
    ((centerCurve (embedding V) H K A Z U u x h
      (fun i => realTrace (Z * B i)) (fun i => realTrace (B i * U)) t :
        selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ) =
      (H : Matrix n n ℂ) + t • (K : Matrix n n ℂ) +
        KSSafeRetirement.supportedGradient L V (transportLine Z U t) := by
  rw [centerCurve_coe V H K A hZ hU]
  unfold KSSafeRetirement.supportedGradient
  rw [hsource, ← add_assoc]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  simp only [ownerProbe, transportLine, Matrix.mul_add, Matrix.mul_smul, realTrace_add,
    realTrace_smul, realTrace_mul_comm (B i) Z]

end SupportedGradient

section ActualLocalMinimum
variable {κ : Type*} [Fintype κ] [Nonempty n]

/-- The supported explicit curve excludes a local minimum of the actual
full-density value. Contact is proved in the chosen isometric source frame,
so no identification with a separately chosen canonical frame is required. -/
theorem not_isLocalMin_of_supported_curve
    (Hactual : ℝ → Matrix n n ℂ) (L : ℝ → κ → Matrix n n ℂ)
    (V : Matrix n m ℂ) (hV : Vᴴ * V = 1)
    (H K : selfAdjoint (Matrix n n ℂ)) (A : ι → selfAdjoint (Matrix n n ℂ))
    {Z U : Matrix m m ℂ} (hZ : Z.PosDef) (hU : U.IsHermitian)
    (u : ℝ) (x h q r : ι → ℝ) {θ : ℝ} (hθ : 0 < θ)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (ht : realTrace (S : Matrix n n ℂ) = 1)
    (hmax : ∀ T ∈ densitySet,
      densityObjective (Hactual 0) (L 0) θ T ≤ densityObjective (Hactual 0) (L 0) θ S)
    (hM : (Vᴴ * krausChannel (L 0) S * V).PosDef)
    (hsolve : Z * (Vᴴ * krausChannel (L 0) S * V) * Z = Vᴴ * (S : Matrix n n ℂ) * V)
    (hsupport0 : ∀ X : Matrix n n ℂ, X.PosSemidef →
      V * (Vᴴ * krausChannel (L 0) X * V) * Vᴴ = krausChannel (L 0) X)
    (hsupport : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ X ∈ densitySet,
      V * (Vᴴ * krausChannel (L t) X * V) * Vᴴ = krausChannel (L t) X)
    (hcenter : ∀ᶠ t in 𝓝 (0 : ℝ),
      ((centerCurve (embedding V) H K A Z U u x h q r t : selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ) =
        Hactual t + KSSafeRetirement.supportedGradient (L t) V (transportLine Z U t))
    (hlegal : centerVelocity (embedding V) K A Z U u x h q r 0 = 0)
    (hnegative : realTrace ((S : Matrix n n ℂ) *
      ((centerAcceleration (embedding V) A Z U u x h q r : selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ)) < 0) :
    ¬ IsLocalMin (fun t => densityPotential (Hactual t) (L t) θ) 0 := by
  let G := centerCurve (embedding V) H K A Z U u x h q r
  have hG : ContDiffAt ℝ 2 G 0 :=
    (contDiffAt_centerCurve (embedding V) H K A Z U hZ.isUnit u x h q r).of_le
      (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have hZ0 : IsUnit (transportLine Z U 0) := by simpa only [transportLine, zero_smul, add_zero] using hZ.isUnit
  have hcritical : deriv G 0 = 0 := by
    rw [(hasDerivAt_centerCurve (embedding V) H K A Z U u x h q r 0 hZ0).deriv]
    exact hlegal
  have hcenter0 : (G 0 : Matrix n n ℂ) = Hactual 0 + KSSafeRetirement.supportedGradient (L 0) V Z := by
    simpa only [transportLine, zero_smul, add_zero] using hcenter.self_of_nhds
  have hf : ContDiffAt ℝ 2 (hermitianDensityPotential (KSSafeRetirement.zeroKraus (n := n)) θ) (G 0) :=
    (contDiffAt_hermitianDensityPotential_source_unrestricted (G 0) KSSafeRetirement.zeroKraus hθ).of_le
      (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  apply not_isLocalMin_of_critical_majorant _
    (hermitianDensityPotential KSSafeRetirement.zeroKraus θ) G hf hG hcritical
  · simp only [hermitianDensityPotential]
    rw [hcenter0]
    simpa only [baseDensityPotential, KSSafeRetirement.zeroKraus] using
      (KSArbitraryTransportContact.basePotential_contact (Hactual 0) (L 0) V hV hθ
        S hS ht hmax hZ hM hsolve hsupport0).symm
  · filter_upwards [eventually_posDef_transportLine hZ hU, hsupport, hcenter] with t htZ htSupp htCent
    simp only [hermitianDensityPotential]
    rw [htCent]
    simpa only [baseDensityPotential, KSSafeRetirement.zeroKraus] using
      KSSafeRetirement.densityPotential_le_supported (Hactual t) (L t) V hV htZ θ htSupp
  · rw [(hasFDerivAt_hermitianDensityPotential_source_unrestricted
      (G 0) KSSafeRetirement.zeroKraus hθ).fderiv]
    have hopt := KSArbitraryTransportContact.baseOptimizer_eq_actual (Hactual 0) (L 0)
      V hV hθ S hS ht hmax hZ hM hsolve hsupport0
    have hopt' : densityOptimizer (G 0) KSSafeRetirement.zeroKraus θ = (S : Matrix n n ℂ) := by
      rw [hcenter0]
      exact congrArg (fun X : selfAdjoint (Matrix n n ℂ) => (X : Matrix n n ℂ)) hopt
    change realTrace (densityOptimizer (G 0) KSSafeRetirement.zeroKraus θ *
      ((iteratedDeriv 2 G (0 : ℝ) : selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ)) < 0
    rw [hopt', iteratedDeriv_two_centerCurve (embedding V) H K A Z U hZ.isUnit u x h q r]
    exact hnegative

end ActualLocalMinimum
end MatrixSpencer.KSSupportedCenterCurve
