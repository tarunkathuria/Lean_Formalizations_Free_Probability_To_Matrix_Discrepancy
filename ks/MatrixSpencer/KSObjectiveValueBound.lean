import MatrixSpencer.KSOptimizerParameters

/-!
# Explicit objective-value error from Frobenius distance

The positive supported fidelity gradient and inverse-square-root gradient
are bounded by their contact pairings with a density having an explicit
floor. This proves an actual gradient bound without any lower bound on a
nonzero source eigenvalue. Integrating it on the convex density-floor set
converts the optimizer's distance accuracy into objective-value accuracy.
-/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSObjectiveValueBound

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
local instance : CStarAlgebra (Matrix n n ℂ) := {}
local instance : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance

theorem entry_norm_le (A : Matrix n n ℂ) (i j : n) : ‖A i j‖ ≤ ‖A‖ := by
  have h := (PiLp.norm_apply_le (Matrix.toEuclideanCLM (𝕜 := ℂ) A
    (EuclideanSpace.single j 1)) i).trans
      ((Matrix.toEuclideanCLM (𝕜 := ℂ) A).le_opNorm (EuclideanSpace.single j 1))
  have he : (Matrix.toEuclideanCLM (𝕜 := ℂ) A (EuclideanSpace.single j 1)) i = A i j := by
    change (A *ᵥ Pi.single j 1) i = _
    rw [Matrix.mulVec_single_one]
    rfl
  rw [he, EuclideanSpace.norm_single, norm_one, mul_one] at h
  exact h

theorem abs_realTrace_le (A : Matrix n n ℂ) :
    |realTrace A| ≤ (Fintype.card n : ℝ) * ‖A‖ := by
  have he : realTrace A = ∑ i, (A i i).re := by
    simp only [realTrace, Matrix.trace, Matrix.diag, map_sum, RCLike.re_eq_complex_re]
  rw [he]
  calc
    _ ≤ ∑ i, |(A i i).re| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : n, ‖A‖ := Finset.sum_le_sum fun i _ =>
      (Complex.abs_re_le_norm _).trans (entry_norm_le A i i)
    _ = _ := by simp

theorem abs_realTrace_mul_le (H X : Matrix n n ℂ) :
    |realTrace (H * X)| ≤ (Fintype.card n : ℝ) * ‖H‖ * ‖X‖ :=
  (abs_realTrace_le _).trans (by
    have h := mul_le_mul_of_nonneg_left (norm_mul_le H X) (Nat.cast_nonneg (Fintype.card n) : (0 : ℝ) ≤ _)
    simpa only [mul_assoc] using h)

/-- Positive trace pairing only requires order bounds on the other factor. -/
theorem abs_positive_pairing_le {G X : Matrix n n ℂ} (hG : G.PosSemidef) (hX : X.IsHermitian) :
    |realTrace (G * X)| ≤ ‖X‖ * realTrace G := by
  have hu := realTrace_mul_mono hG (show IsSelfAdjoint X from hX).le_algebraMap_norm_self
  have hl := realTrace_mul_mono hG (show IsSelfAdjoint X from hX).neg_algebraMap_norm_le_self
  simp only [Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, Matrix.mul_one,
    realTrace_smul, Matrix.mul_neg, realTrace_neg] at hu hl
  apply abs_le.mpr
  constructor <;> linarith

open KSSafeRetirement KSOptimizerFloor

theorem supportedGradient_trace_le (B : ι → Matrix n n ℂ)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (htr : realTrace (S : Matrix n n ℂ) = 1) {a κ : ℝ} (ha : 0 < a) (hκ : 0 ≤ κ)
    (hfloor : a • (1 : Matrix n n ℂ) ≤ (S : Matrix n n ℂ))
    (hbudget : (∑ i, (B i)ᴴ * B i) ≤ κ • (1 : Matrix n n ℂ)) :
    realTrace (actualSupportedGradient B S) ≤ 2 * Real.sqrt κ / a := by
  have ht := realTrace_mul_mono (actualSupportedGradient_posSemidef B hS) hfloor
  rw [Matrix.mul_smul, Matrix.mul_one, realTrace_smul, actualSupportedGradient_contact B hS] at ht
  have hf := KSObjectiveUpper.fidelity_le_sqrt_budget_mul_trace B hκ hbudget hS.posSemidef
  rw [htr, mul_one] at hf
  apply (le_div_iff₀ ha).mpr
  nlinarith

theorem inverseSqrt_posSemidef (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) : (inverseSqrt S).PosSemidef :=
  hS.posDef_sqrt.inv.posSemidef

theorem inverseSqrt_trace_le (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) (htr : realTrace (S : Matrix n n ℂ) = 1)
    {a : ℝ} (ha : 0 < a) (hfloor : a • (1 : Matrix n n ℂ) ≤ (S : Matrix n n ℂ)) :
    realTrace (inverseSqrt S) ≤ Real.sqrt (Fintype.card n : ℝ) / a := by
  have ht := realTrace_mul_mono (inverseSqrt_posSemidef S hS) hfloor
  rw [Matrix.mul_smul, Matrix.mul_one, realTrace_smul, inverseSqrt_mul_self S hS] at ht
  have hr := density_trace_sqrt_le_sqrt_card (show (S : Matrix n n ℂ) ∈ densitySet from
    ⟨hS.posSemidef, htr⟩)
  apply (le_div_iff₀ ha).mpr
  nlinarith

def regularizedGradient (B : ι → Matrix n n ℂ) (θ : ℝ)
    (S : selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ :=
  actualSupportedGradient B S + θ • inverseSqrt S

theorem regularizedGradient_posSemidef (B : ι → Matrix n n ℂ) {θ : ℝ} (hθ : 0 ≤ θ)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef) :
    (regularizedGradient B θ S).PosSemidef :=
  (actualSupportedGradient_posSemidef B hS).add ((inverseSqrt_posSemidef S hS).smul hθ)

theorem regularizedGradient_trace_le (B : ι → Matrix n n ℂ) {θ : ℝ} (hθ : 0 ≤ θ)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (htr : realTrace (S : Matrix n n ℂ) = 1) {a κ : ℝ} (ha : 0 < a) (hκ : 0 ≤ κ)
    (hfloor : a • (1 : Matrix n n ℂ) ≤ (S : Matrix n n ℂ))
    (hbudget : (∑ i, (B i)ᴴ * B i) ≤ κ • (1 : Matrix n n ℂ)) :
    realTrace (regularizedGradient B θ S) ≤
      (2 * Real.sqrt κ + θ * Real.sqrt (Fintype.card n : ℝ)) / a := by
  have hg := supportedGradient_trace_le B S hS htr ha hκ hfloor hbudget
  have ht := mul_le_mul_of_nonneg_left (inverseSqrt_trace_le S hS htr ha hfloor) hθ
  unfold regularizedGradient
  rw [realTrace_add, realTrace_smul]
  calc
    _ ≤ 2 * Real.sqrt κ / a + θ * (Real.sqrt (Fintype.card n : ℝ) / a) := add_le_add hg ht
    _ = _ := by ring

/-- A cap expressed only in the input center bound, floor, source budget,
dimension, and regularizer. -/
def valueCoefficient (R a κ θ : ℝ) : ℝ :=
  (Fintype.card n : ℝ) * R + (2 * Real.sqrt κ + θ * Real.sqrt (Fintype.card n : ℝ)) / a

omit [DecidableEq n] in
theorem valueCoefficient_nonneg {R a κ θ : ℝ} (hR : 0 ≤ R) (ha : 0 ≤ a) (hθ : 0 ≤ θ) :
    0 ≤ valueCoefficient (n := n) R a κ θ := by unfold valueCoefficient; positivity

theorem physical_fderiv_bound (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    {θ R a κ : ℝ} (hθ : 0 ≤ θ) (hR : ‖H‖ ≤ R) (ha : 0 < a) (hκ : 0 ≤ κ)
    (S X : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (htr : realTrace (S : Matrix n n ℂ) = 1)
    (hfloor : a • (1 : Matrix n n ℂ) ≤ (S : Matrix n n ℂ))
    (hbudget : (∑ i, (B i)ᴴ * B i) ≤ κ • (1 : Matrix n n ℂ)) :
    |fderiv ℝ (hermitianDensityObjective H B θ) S X| ≤
      valueCoefficient (n := n) R a κ θ * ‖(X : Matrix n n ℂ)‖ := by
  have he : fderiv ℝ (hermitianDensityObjective H B θ) S X =
      realTrace (H * (X : Matrix n n ℂ)) +
        realTrace (regularizedGradient B θ S * (X : Matrix n n ℂ)) := by
    rw [fderiv_hermitianDensityObjective_eq_source_unrestricted H B θ S hS,
      fderiv_krausSourceFidelity_eq_supportedGradient B S hS, fderiv_tsallisPotential_eq θ S hS]
    change realTrace (H * (X : Matrix n n ℂ)) +
      realTrace (actualSupportedGradient B S * (X : Matrix n n ℂ)) +
      θ * realTrace (inverseSqrt S * (X : Matrix n n ℂ)) = _
    simp only [regularizedGradient, Matrix.add_mul, Matrix.smul_mul, realTrace_add, realTrace_smul]
    ring
  rw [he]
  have hc := (abs_realTrace_mul_le H (X : Matrix n n ℂ)).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hR (Nat.cast_nonneg _)) (norm_nonneg _))
  have hg := (abs_positive_pairing_le (regularizedGradient_posSemidef B hθ S hS) X.property).trans
    (mul_le_mul_of_nonneg_left
      (regularizedGradient_trace_le B hθ S hS htr ha hκ hfloor hbudget) (norm_nonneg _))
  calc
    _ ≤ |realTrace (H * (X : Matrix n n ℂ))| +
        |realTrace (regularizedGradient B θ S * (X : Matrix n n ℂ))| := abs_add_le _ _
    _ ≤ _ := by unfold valueCoefficient; nlinarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
open KSObjectiveChart

theorem objective_fderiv_norm_le (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    {θ R a κ : ℝ} (hθ : 0 ≤ θ) (hR : ‖H‖ ≤ R) (ha : 0 < a) (hκ : 0 ≤ κ)
    (e : E →L[ℝ] selfAdjoint (Matrix n n ℂ))
    (hisometry : ∀ v, realTrace ((e v : Matrix n n ℂ) * (e v : Matrix n n ℂ)) = ‖v‖ ^ 2)
    (hbudget : (∑ i, (B i)ᴴ * B i) ≤ κ • (1 : Matrix n n ℂ))
    (x : E) (hx : x ∈ densityFloor e a) :
    ‖fderiv ℝ (objective H B θ e) x‖ ≤ valueCoefficient (n := n) R a κ θ := by
  have hcoef := valueCoefficient_nonneg (n := n) (κ := κ) ((norm_nonneg _).trans hR) ha.le hθ
  apply ContinuousLinearMap.opNorm_le_bound _ hcoef
  intro v
  have hS := densityFloor_posDef e ha hx
  have he : fderiv ℝ (objective H B θ e) x v =
      fderiv ℝ (hermitianDensityObjective H B θ) (e x) (e v) := by
    rw [objective, fderiv_comp x
      ((contDiffAt_hermitianDensityObjective_source_unrestricted H B θ (e x) hS).differentiableAt
        (by simp)) e.differentiableAt]
    simp only [ContinuousLinearMap.fderiv, ContinuousLinearMap.comp_apply]
  rw [Real.norm_eq_abs, he]
  have hv : ‖(e v : Matrix n n ℂ)‖ ≤ ‖v‖ := by
    have hs := KSObjectiveUpper.norm_sq_le_trace_square (e v).property
    rw [hisometry v] at hs
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hs
  exact (physical_fderiv_bound H B hθ hR ha hκ (e x) (e v) hS hx.2 hx.1 hbudget).trans
    (mul_le_mul_of_nonneg_left hv hcoef)

/-- Distance-to-value conversion on the actual convex density-floor set. -/
theorem objective_value_error (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    {θ R a κ : ℝ} (hθ : 0 ≤ θ) (hR : ‖H‖ ≤ R) (ha : 0 < a) (hκ : 0 ≤ κ)
    (e : E →L[ℝ] selfAdjoint (Matrix n n ℂ))
    (hisometry : ∀ v, realTrace ((e v : Matrix n n ℂ) * (e v : Matrix n n ℂ)) = ‖v‖ ^ 2)
    (hbudget : (∑ i, (B i)ᴴ * B i) ≤ κ • (1 : Matrix n n ℂ))
    {x y : E} (hx : x ∈ densityFloor e a) (hy : y ∈ densityFloor e a) :
    |objective H B θ e x - objective H B θ e y| ≤
      valueCoefficient (n := n) R a κ θ * dist x y := by
  have h := (densityFloor_convex e a).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z hz => ((objective_contDiffAt H B θ e z (densityFloor_posDef e ha hz)).differentiableAt
      (by simp)).hasFDerivAt.hasFDerivWithinAt)
    (fun z hz => objective_fderiv_norm_le H B hθ hR ha hκ e hisometry hbudget z hz) hy hx
  simpa only [Real.norm_eq_abs, dist_eq_norm] using h

def distanceAccuracy (R a κ θ ε : ℝ) : ℝ := ε / (valueCoefficient (n := n) R a κ θ + 1)

omit [DecidableEq n] in
theorem distanceAccuracy_pos {R a κ θ ε : ℝ} (hR : 0 ≤ R) (ha : 0 ≤ a)
    (hθ : 0 ≤ θ) (hε : 0 < ε) : 0 < distanceAccuracy (n := n) R a κ θ ε :=
  div_pos hε (by have := valueCoefficient_nonneg (n := n) (κ := κ) hR ha hθ; linarith)

/-- The selected positive distance tolerance guarantees the requested
value error; the extra `1` also covers a zero coefficient. -/
theorem objective_value_error_of_distance (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    {θ R a κ ε : ℝ} (hθ : 0 ≤ θ) (hR : ‖H‖ ≤ R) (ha : 0 < a) (hκ : 0 ≤ κ)
    (hε : 0 < ε) (e : E →L[ℝ] selfAdjoint (Matrix n n ℂ))
    (hisometry : ∀ v, realTrace ((e v : Matrix n n ℂ) * (e v : Matrix n n ℂ)) = ‖v‖ ^ 2)
    (hbudget : (∑ i, (B i)ᴴ * B i) ≤ κ • (1 : Matrix n n ℂ))
    {x y : E} (hx : x ∈ densityFloor e a) (hy : y ∈ densityFloor e a)
    (hd : dist x y ≤ distanceAccuracy (n := n) R a κ θ ε) :
    |objective H B θ e x - objective H B θ e y| ≤ ε := by
  have hcoef := valueCoefficient_nonneg (n := n) (κ := κ) ((norm_nonneg _).trans hR) ha.le hθ
  have hpos : 0 < valueCoefficient (n := n) R a κ θ + 1 := by linarith
  apply (objective_value_error H B hθ hR ha hκ e hisometry hbudget hx hy).trans
  apply (mul_le_mul_of_nonneg_left hd hcoef).trans
  unfold distanceAccuracy
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hpos).mpr
  nlinarith

end MatrixSpencer.KSObjectiveValueBound
