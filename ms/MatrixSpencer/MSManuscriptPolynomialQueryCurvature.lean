import MatrixSpencer.MSManuscriptFactoryPolynomialMesh

/-! Fixed-degree natural polynomial bounds for the actual square-MS
covariance-query curvature formulas, uniform in every stored owner dimension.
-/
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.MSManuscriptPolynomialQueryCurvature
open MSManuscriptPolynomialMovementBounds
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

def center (N d : ℕ) : ℕ := 1 + (d+1)*N + N
def denominator (N d : ℕ) : ℕ := 2*(center N d+N*(N+1))+2*N^2+2*(d+1)
def value (N d : ℕ) : ℕ := 2*d*(center N d+2*N*(N+1))+16*d*N^4+6*d
def joint (N d : ℕ) : ℕ := value N d*(83886080*(1+(denominator N d)^2))^4
def second (N d : ℕ) : ℕ := joint N d*(1+2*joint N d)
def curvature (N d : ℕ) : ℕ := 1+(N+1)*second N d

@[simp] theorem cast_center (N d : ℕ) : (center N d : ℝ) = 1+((d:ℝ)+1)*N+N := by
  simp [center]

theorem cast_joint (N d : ℕ) : (joint N d : ℝ) =
    MSManuscriptPolynomialMovementBounds.joint N d (center N d) := by
  simp [joint, value, denominator, MSManuscriptPolynomialMovementBounds.joint,
    MSManuscriptPolynomialMovementBounds.value, inverseFloor,
    MSManuscriptPolynomialMovementBounds.denominator, direction, mul_assoc]

theorem floor_inverse_le {N k L d : ℕ} (hk : k ≤ N) (hL : L ≤ N) (hd : 0 < d)
    {R : ℝ} (hR : 0 ≤ R) (hRN : R ≤ center N d) :
    (MSManuscriptOptimizerFloorScaled.floor k d R 1 L)⁻¹ ≤
      MSManuscriptPolynomialMovementBounds.inverseFloor N d (center N d) := by
  let D := 2*R+2*(k:ℝ)*(L:ℝ)+2*Real.sqrt (d:ℝ)
  have hD : 0 < D := by
    have hs := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hd)
    dsimp [D]
    positivity
  have hDle : D ≤ MSManuscriptPolynomialMovementBounds.denominator N d (center N d) := by
    have hk' : (k:ℝ) ≤ N := Nat.cast_le.mpr hk
    have hL' : (L:ℝ) ≤ N := Nat.cast_le.mpr hL
    have hm := mul_le_mul hk' hL' (Nat.cast_nonneg L) (Nat.cast_nonneg N)
    have hs := sqrt_le_add_one (Nat.cast_nonneg d)
    unfold MSManuscriptPolynomialMovementBounds.denominator direction
    dsimp [D]
    nlinarith
  simp only [MSManuscriptOptimizerFloorScaled.floor, mul_one, one_mul]
  change (min 1 ((1/D)^2))⁻¹ ≤ _
  rcases le_total 1 ((1/D)^2) with h | h
  · rw [min_eq_left h]
    simp only [inv_one, inverseFloor]
    exact le_add_of_nonneg_right (sq_nonneg _)
  · rw [min_eq_right h]
    have he : ((1/D)^2)⁻¹ = D^2 := by field_simp
    rw [he]
    exact (pow_le_pow_left₀ hD.le hDle 2).trans (by unfold inverseFloor; linarith)

theorem value_le {N k L d : ℕ} (hk : k ≤ N) (hL : L ≤ N)
    {R : ℝ} (hR : 0 ≤ R) (hRN : R ≤ center N d) :
    MSManuscriptComplexValueBoundScaled.valueCap (Fin k) (Fin d) R 1 L ≤
      MSManuscriptPolynomialMovementBounds.value N d (center N d) := by
  have hv := actualValue_le N N d le_rfl (Nat.cast_nonneg (center N d))
  apply le_trans ?_ hv
  have hk' : (k:ℝ) ≤ N := Nat.cast_le.mpr hk
  have hL' : (L:ℝ) ≤ N := Nat.cast_le.mpr hL
  have hR' : R ≤ (center N d : ℝ)+MSManuscriptLDLMoments.directionCap N 1+
      MSManuscriptLDLMoments.directionCap N 1 := by
    have hb : 0 ≤ MSManuscriptLDLMoments.directionCap N 1 := by
      unfold MSManuscriptLDLMoments.directionCap
      positivity
    linarith
  unfold MSManuscriptComplexValueBoundScaled.valueCap KSComplexObjectiveBound.valueCap
  simp only [Fintype.card_fin]
  gcongr

theorem jointCap_le {N k L d : ℕ} (hk : k ≤ N) (hL : L ≤ N) (hd : 0 < d)
    {R : ℝ} (hR : 0 ≤ R) (hRN : R ≤ center N d) :
    MSManuscriptGammaInputBoundScaled.jointCap k d R 1 (1/8192) L ≤ joint N d := by
  let μ := MSManuscriptOptimizerFloorScaled.floor k d R 1 L
  have hμ : 0 < μ := MSManuscriptOptimizerFloorScaled.floor_pos hd
    (Nat.cast_nonneg L) hR (by norm_num)
  have hi := floor_inverse_le hk hL hd hR hRN
  have hv := value_le hk hL hR hRN
  have hr : 10/MSManuscriptComplexSourceDomain.radius ((1/8192)/2) μ =
      20971520*μ⁻¹ := by unfold MSManuscriptComplexSourceDomain.radius; ring
  have hs : 20971520*μ⁻¹ ≤ 83886080*inverseFloor N d (center N d) := by
    have hi0 := inverseFloor_nonneg N d (center N d)
    nlinarith
  rw [cast_joint]
  unfold MSManuscriptGammaInputBoundScaled.jointCap MSManuscriptAffineJointBoundsScaled.jointCap
  change MSManuscriptComplexValueBoundScaled.valueCap (Fin k) (Fin d) R 1 L *
    (10/MSManuscriptComplexSourceDomain.radius ((1/8192)/2) μ)^4 ≤ _
  rw [hr]
  exact mul_le_mul hv (pow_le_pow_left₀ (by positivity) hs 4) (by positivity)
    (MSManuscriptPolynomialMovementBounds.value_nonneg _ _ (Nat.cast_nonneg _))

theorem secondCap_le {N k L d : ℕ} (hk : k ≤ N) (hL : L ≤ N) (hd : 0 < d)
    {R : ℝ} (hR : 0 ≤ R) (hRN : R ≤ center N d) :
    MSManuscriptGammaInputBoundScaled.secondCap k d R 1 (1/8192) L ≤ second N d := by
  have h := jointCap_le hk hL hd hR hRN
  have h0 := MSManuscriptGammaInputBoundScaled.jointCap_nonneg
    (k:=k) (d:=d) (δ:=(1/8192)) (L:=(L:ℝ)) hR (by norm_num : (0:ℝ)≤1)
  unfold MSManuscriptGammaInputBoundScaled.secondCap second
  push_cast
  calc
    _ = MSManuscriptGammaInputBoundScaled.jointCap k d R 1 (1/8192) L *
      (1+2*MSManuscriptGammaInputBoundScaled.jointCap k d R 1 (1/8192) L) := by ring
    _ ≤ _ := by gcongr

theorem curvatureBudget_le {m N d : ℕ} (P : MSManuscriptSupportedGamma.Parameters m d)
    (hm : m ≤ N) (hθ : P.regularizer = 1) (hδ : P.floor = 1/8192)
    (hR : 0 ≤ P.centerCap) (hRN : P.centerCap ≤ center N d) :
    MSManuscriptSupportedPaid.curvatureBudget P ≤ curvature N d := by
  have hs : (∑ j : Fin (m+1), MSManuscriptGammaInputBoundScaled.secondCap j d
      P.centerCap P.regularizer P.floor m) ≤ (m+1:ℕ)*(second N d:ℝ) := by
    calc
      _ ≤ ∑ _j : Fin (m+1), (second N d:ℝ) := by
        apply Finset.sum_le_sum
        intro j _
        rw [hθ, hδ]
        exact secondCap_le (N:=N) (k:=j.val) (L:=m) (d:=d)
          (by have hj := j.isLt; omega) hm P.physicalDimension_pos hR hRN
      _ = _ := by simp
  have hm' : (m:ℝ) ≤ N := Nat.cast_le.mpr hm
  unfold MSManuscriptSupportedPaid.curvatureBudget curvature
  push_cast at hs ⊢
  nlinarith [show (0:ℝ) ≤ second N d from Nat.cast_nonneg _]

end MatrixSpencer.MSManuscriptPolynomialQueryCurvature
