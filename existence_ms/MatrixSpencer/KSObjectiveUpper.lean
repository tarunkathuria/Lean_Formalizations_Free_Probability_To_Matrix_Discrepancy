import MatrixSpencer.KSFidelityUpper
import MatrixSpencer.KSOptimizerFloor
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Explicit upper curvature of the actual regularized density objective

For a positive density with `a I ≤ S`, trace at most `c`, and Kraus budget
`∑ Bᵢᴴ Bᵢ ≤ κ I`, the actual Hessian has Frobenius operator norm at most
`(2 c √κ + (θ/2) √(dim · c)) / a²`. This conservative constant is independent
of the smallest nonzero source eigenvalue. All derivatives are derivatives
of the original objective, including for singular Kraus sources.

The coordinate wrapper directly supplies the quantitative upper-Hessian
input of the projected optimizer. Numerical gradient and projection reports
remain separate computations with separate accuracy theorems.
-/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSObjectiveUpper
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
local instance : CStarAlgebra (Matrix n n ℂ) := {}
local instance : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance

/-- Operator-norm control by the actual squared Frobenius trace. -/
theorem norm_sq_le_trace_square {X : Matrix n n ℂ} (hX : X.IsHermitian) :
    ‖X‖ ^ 2 ≤ realTrace (X * X) := by
  have hXX : (X * X).PosSemidef := by
    simpa only [hX.eq] using Matrix.posSemidef_conjTranspose_mul_self X
  have ht : X * X ≤ realTrace (X * X) • (1 : Matrix n n ℂ) := by
    simpa only [Algebra.algebraMap_eq_smul_one] using posSemidef_le_trace_identity hXX
  have hn : ‖X * X‖ ≤ realTrace (X * X) := by
    apply (CStarAlgebra.norm_le_iff_le_algebraMap _ (realTrace_nonneg hXX) hXX.nonneg).mpr
    simpa only [Algebra.algebraMap_eq_smul_one] using ht
  have he := CStarRing.norm_star_mul_self (x := X)
  rw [Matrix.star_eq_conjTranspose, hX.eq] at he
  nlinarith

/-- A physical spectral floor converts absolute tangent size to relative order. -/
theorem relative_bounds_of_floor {S X : Matrix n n ℂ} (hX : X.IsHermitian)
    {a : ℝ} (ha : 0 < a) (hfloor : a • (1 : Matrix n n ℂ) ≤ S) :
    -(‖X‖ / a) • S ≤ X ∧ X ≤ (‖X‖ / a) • S := by
  have hscale : (‖X‖ / a) • (a • (1 : Matrix n n ℂ)) = ‖X‖ • (1 : Matrix n n ℂ) := by
    rw [smul_smul, div_mul_cancel₀ _ ha.ne']
  have hcap : ‖X‖ • (1 : Matrix n n ℂ) ≤ (‖X‖ / a) • S := by
    rw [← hscale]
    exact smul_le_smul_of_nonneg_left hfloor (div_nonneg (norm_nonneg X) ha.le)
  have hlo : -‖X‖ • (1 : Matrix n n ℂ) ≤ X := by
    simpa only [Algebra.algebraMap_eq_smul_one, neg_smul] using
      (show IsSelfAdjoint X from hX).neg_algebraMap_norm_le_self
  have hhi : X ≤ ‖X‖ • (1 : Matrix n n ℂ) := by
    simpa only [Algebra.algebraMap_eq_smul_one] using
      (show IsSelfAdjoint X from hX).le_algebraMap_norm_self
  constructor
  · have hh := neg_le_neg hcap
    simp only [← neg_smul] at hh
    exact hh.trans hlo
  · exact hhi.trans hcap

/-- A relative upper Hessian bound for the actual Tsallis regularizer. -/
theorem tsallis_negativeHessian_relative_le (θ : ℝ) (hθ : 0 < θ)
    (S X : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hlo : -δ • (S : Matrix n n ℂ) ≤ (X : Matrix n n ℂ))
    (hhi : (X : Matrix n n ℂ) ≤ δ • (S : Matrix n n ℂ)) :
    -fderiv ℝ (fun A => fderiv ℝ (tsallisPotential θ (n := n)) A) S X X ≤
      θ / 2 * δ ^ 2 * realTrace (CFC.sqrt (S : Matrix n n ℂ)) := by
  let Q := CFC.sqrt (S : Matrix n n ℂ)
  let U := (sylvesterEquiv Q hS.posDef_sqrt).symm (X : Matrix n n ℂ)
  have hU : U.IsHermitian := sylvester_inverse_isHermitian Q hS.posDef_sqrt X.property
  have hUX : Q * U + U * Q = (X : Matrix n n ℂ) := sylvester_inverse_solve Q hS.posDef_sqrt X
  have hQQ : Q * Q = (S : Matrix n n ℂ) := CFC.sqrt_mul_sqrt_self _ hS.posSemidef.nonneg
  have hl : -(2 * (δ / 2)) • (Q * Q) ≤ Q * U + U * Q := by
    simpa only [hQQ, hUX, mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using hlo
  have hu : Q * U + U * Q ≤ (2 * (δ / 2)) • (Q * Q) := by
    have heq : 2 * (δ / 2) = δ := by ring
    simpa only [hQQ, hUX, heq] using hhi
  have hb := KSSylvesterOrder.solution_trace_energy_le hS.posDef_sqrt hU
    (div_nonneg hδ (by norm_num : (0 : ℝ) ≤ 2)) hl hu
  rw [fderiv_fderiv_tsallisPotential_apply θ hθ.ne' S X X hS]
  rw [realTrace_mul_comm (negativeTsallisHessianEquiv θ hθ.ne' S hS X : Matrix n n ℂ)
    (X : Matrix n n ℂ)]
  rw [negativeTsallisHessianEquiv_apply, fderiv_hermitianSqrt_eq S hS,
    Matrix.mul_smul, realTrace_smul]
  change -( - (θ * realTrace ((X : Matrix n n ℂ) * (Q⁻¹ * U * Q⁻¹)))) ≤ _
  conv_lhs => rw [← hUX, realTrace_sylvester_conjugate Q U hS.posDef_sqrt.isUnit]
  nlinarith [mul_le_mul_of_nonneg_left hb hθ.le]

/-- Relative upper curvature of the actual regularized density objective. -/
theorem density_negativeHessian_relative_le (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (θ : ℝ) (hθ : 0 < θ) (S X : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) {δ : ℝ} (hδ : 0 ≤ δ)
    (hlo : -δ • (S : Matrix n n ℂ) ≤ (X : Matrix n n ℂ))
    (hhi : (X : Matrix n n ℂ) ≤ δ • (S : Matrix n n ℂ)) :
    densityNegativeHessian H B θ S X X ≤
      (2 * fidelity S (krausChannel B S) + θ / 2 * realTrace (CFC.sqrt (S : Matrix n n ℂ))) * δ ^ 2 := by
  have hf := KSFidelityUpper.kraus_negativeHessian_relative_le B S X hS hδ hlo hhi
  have ht := tsallis_negativeHessian_relative_le θ hθ S X hS hδ hlo hhi
  change -fderiv ℝ (fun A => fderiv ℝ (hermitianDensityObjective H B θ) A) S X X ≤ _
  rw [fderiv_fderiv_hermitianDensityObjective_apply_source_unrestricted H B θ S X X hS]
  nlinarith

/-- An explicit floor gives an upper Hessian bound in the actual Frobenius
quadratic form; its coefficient still displays the actual value terms. -/
theorem density_negativeHessian_floor_le (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (θ : ℝ) (hθ : 0 < θ) (S X : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) {a : ℝ} (ha : 0 < a)
    (hfloor : a • (1 : Matrix n n ℂ) ≤ (S : Matrix n n ℂ)) :
    densityNegativeHessian H B θ S X X ≤
      ((2 * fidelity S (krausChannel B S) + θ / 2 * realTrace (CFC.sqrt (S : Matrix n n ℂ))) / a ^ 2) *
        realTrace ((X : Matrix n n ℂ) * (X : Matrix n n ℂ)) := by
  obtain ⟨hl, hu⟩ := relative_bounds_of_floor X.property ha hfloor
  have hh := density_negativeHessian_relative_le H B θ hθ S X hS
    (div_nonneg (norm_nonneg (X : Matrix n n ℂ)) ha.le) hl hu
  have hc : 0 ≤ 2 * fidelity (S : Matrix n n ℂ) (krausChannel B S) +
      θ / 2 * realTrace (CFC.sqrt (S : Matrix n n ℂ)) := by
    have hf := fidelity_nonneg (S : Matrix n n ℂ) (krausChannel B S)
    have ht := realTrace_nonneg (CFC.sqrt_nonneg (S : Matrix n n ℂ)).posSemidef
    positivity
  have hb := mul_le_mul_of_nonneg_left (norm_sq_le_trace_square X.property)
    (div_nonneg hc (sq_nonneg a))
  apply hh.trans
  convert hb using 1; ring

/-- The source trace budget on the full positive cone. -/
theorem kraus_trace_le_mul_trace (B : ι → Matrix n n ℂ) {κ : ℝ}
    (hbudget : (∑ i, (B i)ᴴ * B i) ≤ κ • (1 : Matrix n n ℂ))
    {S : Matrix n n ℂ} (hS : S.PosSemidef) :
    realTrace (krausChannel B S) ≤ κ * realTrace S := by
  have htr : realTrace (krausChannel B S) = realTrace ((∑ i, (B i)ᴴ * B i) * S) := by
    simpa only [KSSafeRetirement.sourceAdjoint, Matrix.mul_one, Matrix.one_mul] using
      (KSSafeRetirement.realTrace_sourceAdjoint B 1 S).symm
  have hb := realTrace_mul_mono hS hbudget
  rw [realTrace_mul_comm S (∑ i, (B i)ᴴ * B i), Matrix.mul_smul, Matrix.mul_one,
    realTrace_smul] at hb
  rwa [htr]

/-- Fidelity budget with arbitrary unnormalized positive densities. -/
theorem fidelity_le_sqrt_budget_mul_trace (B : ι → Matrix n n ℂ) {κ : ℝ}
    (hκ : 0 ≤ κ) (hbudget : (∑ i, (B i)ᴴ * B i) ≤ κ • (1 : Matrix n n ℂ))
    {S : Matrix n n ℂ} (hS : S.PosSemidef) :
    fidelity S (krausChannel B S) ≤ Real.sqrt κ * realTrace S := by
  have hf := fidelity_sq_le_trace_mul hS (krausChannel_posSemidef B hS)
  have hb := mul_le_mul_of_nonneg_left (kraus_trace_le_mul_trace B hbudget hS)
    (realTrace_nonneg hS)
  have hr := Real.sq_sqrt hκ
  apply (sq_le_sq₀ (fidelity_nonneg S _) (mul_nonneg (Real.sqrt_nonneg κ) (realTrace_nonneg hS))).mp
  calc fidelity S (krausChannel B S) ^ 2 ≤ realTrace S * realTrace (krausChannel B S) := hf
    _ ≤ realTrace S * (κ * realTrace S) := hb
    _ = (Real.sqrt κ * realTrace S) ^ 2 := by rw [mul_pow, hr]; ring

/-- A fully explicit upper Hessian coefficient. It uses only the spectral
floor, a source budget, the density trace cap, the dimension and regularizer. -/
def upperCoefficient (a κ θ c : ℝ) : ℝ :=
  (2 * c * Real.sqrt κ + θ / 2 * Real.sqrt ((Fintype.card n : ℝ) * c)) / a ^ 2

omit [DecidableEq n] in
theorem upperCoefficient_nonneg {a κ θ c : ℝ} (hθ : 0 ≤ θ) (hc : 0 ≤ c) :
    0 ≤ upperCoefficient (n := n) a κ θ c := by
  unfold upperCoefficient
  positivity

/-- Explicit source-gap-independent Frobenius Hessian bound, valid also at
nearby numerical queries whose density trace is at most `c`. -/
theorem density_negativeHessian_le_explicit (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (θ : ℝ) (hθ : 0 < θ) (S X : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) {a κ c : ℝ} (ha : 0 < a) (hκ : 0 ≤ κ)
    (hfloor : a • (1 : Matrix n n ℂ) ≤ (S : Matrix n n ℂ))
    (hbudget : (∑ i, (B i)ᴴ * B i) ≤ κ • (1 : Matrix n n ℂ))
    (htrace : realTrace (S : Matrix n n ℂ) ≤ c) :
    densityNegativeHessian H B θ S X X ≤ upperCoefficient (n := n) a κ θ c *
      realTrace ((X : Matrix n n ℂ) * (X : Matrix n n ℂ)) := by
  apply (density_negativeHessian_floor_le H B θ hθ S X hS ha hfloor).trans
  have hc : 0 ≤ c := (realTrace_nonneg hS.posSemidef).trans htrace
  have hf := (fidelity_le_sqrt_budget_mul_trace B hκ hbudget hS.posSemidef).trans
    (mul_le_mul_of_nonneg_left htrace (Real.sqrt_nonneg κ))
  have ht : realTrace (CFC.sqrt (S : Matrix n n ℂ)) ≤
      Real.sqrt ((Fintype.card n : ℝ) * c) := by
    apply (Real.le_sqrt (realTrace_nonneg (CFC.sqrt_nonneg (S : Matrix n n ℂ)).posSemidef)
      (mul_nonneg (Nat.cast_nonneg _) hc)).mpr
    exact (trace_sqrt_sq_le_card_mul_trace hS.posSemidef).trans
      (mul_le_mul_of_nonneg_left htrace (Nat.cast_nonneg _))
  apply mul_le_mul_of_nonneg_right _ (by
    have he : (X : Matrix n n ℂ)ᴴ = X := X.property
    simpa only [he] using realTrace_conjTranspose_mul_self_nonneg (X : Matrix n n ℂ))
  apply div_le_div_of_nonneg_right _ (sq_nonneg a)
  dsimp [upperCoefficient]
  nlinarith [mul_le_mul_of_nonneg_left ht (div_nonneg hθ.le (by norm_num : (0 : ℝ) ≤ 2))]

/-- The actual negative Hessian is nonnegative also in the zero direction. -/
theorem density_negativeHessian_nonneg (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (θ : ℝ) (hθ : 0 < θ) (S X : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) : 0 ≤ densityNegativeHessian H B θ S X X := by
  by_cases hX : X = 0
  · subst X
    simp
  · exact (negativeDensityHessian_quadratic_pos_source_unrestricted H B θ hθ S X hS hX).le

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem bilinear_norm_le_of_quadratic (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hsymm : ∀ x y, B x y = B y x) {L : ℝ} (hL : 0 ≤ L)
    (hquad : ∀ x, |B x x| ≤ L * ‖x‖ ^ 2) : ‖B‖ ≤ L := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hL
  intro x hx
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hL
  intro y hy
  rw [Real.norm_eq_abs]
  have hp := abs_le.mp (hquad (x + y))
  have hm := abs_le.mp (hquad (x - y))
  have hn : ‖x + y‖ ^ 2 + ‖x - y‖ ^ 2 = 4 := by
    rw [norm_add_sq_real, norm_sub_sq_real, hx, hy]
    ring
  have heq : 4 * B x y = B (x + y) (x + y) - B (x - y) (x - y) := by
    simp only [map_add, map_sub, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
      hsymm y x]
    ring
  apply abs_le.mpr
  constructor <;> nlinarith [congrArg (fun t : ℝ => L * t) hn]

/-- The full operator norm of the actual coordinate Hessian has the same
explicit coefficient as its Frobenius quadratic form. -/
theorem objective_hessian_norm_le_explicit (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (θ : ℝ) (hθ : 0 < θ) (e : E →L[ℝ] selfAdjoint (Matrix n n ℂ))
    (hisometry : ∀ v, realTrace ((e v : Matrix n n ℂ) * (e v : Matrix n n ℂ)) = ‖v‖ ^ 2)
    (x : E) (hS : (e x : Matrix n n ℂ).PosDef) {a κ c : ℝ} (ha : 0 < a) (hκ : 0 ≤ κ)
    (hfloor : a • (1 : Matrix n n ℂ) ≤ (e x : Matrix n n ℂ))
    (hbudget : (∑ i, (B i)ᴴ * B i) ≤ κ • (1 : Matrix n n ℂ))
    (htrace : realTrace (e x : Matrix n n ℂ) ≤ c) :
    ‖fderiv ℝ (fderiv ℝ (KSObjectiveChart.objective H B θ e)) x‖ ≤
      upperCoefficient (n := n) a κ θ c := by
  have hc : 0 ≤ c := (realTrace_nonneg hS.posSemidef).trans htrace
  apply bilinear_norm_le_of_quadratic _
    ((KSObjectiveChart.objective_contDiffAt H B θ e x hS).isSymmSndFDerivAt (by
      rw [minSmoothness_of_isRCLikeNormedField]
      exact WithTop.coe_le_coe.mpr le_top))
    (upperCoefficient_nonneg hθ.le hc)
  intro v
  rw [KSObjectiveChart.objective_hessian H B θ e x v v hS]
  have hn := density_negativeHessian_nonneg H B θ hθ (e x) (e v) hS
  have hb := density_negativeHessian_le_explicit H B θ hθ (e x) (e v) hS ha hκ hfloor hbudget htrace
  rw [hisometry v] at hb
  change 0 ≤ -fderiv ℝ (fderiv ℝ (hermitianDensityObjective H B θ)) (e x) (e v) (e v) at hn
  change -fderiv ℝ (fderiv ℝ (hermitianDensityObjective H B θ)) (e x) (e v) (e v) ≤ _ at hb
  rw [abs_of_nonpos (by linarith)]
  exact hb

/-- Direct discharge of the upper-Hessian input on the density-floor feasible
set used by the existing projected optimizer. -/
theorem objective_floor_hessian_norm_le_explicit (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (θ : ℝ) (hθ : 0 < θ) (e : E →L[ℝ] selfAdjoint (Matrix n n ℂ))
    (hisometry : ∀ v, realTrace ((e v : Matrix n n ℂ) * (e v : Matrix n n ℂ)) = ‖v‖ ^ 2)
    {a κ : ℝ} (ha : 0 < a) (hκ : 0 ≤ κ)
    (hbudget : (∑ i, (B i)ᴴ * B i) ≤ κ • (1 : Matrix n n ℂ))
    (x : E) (hx : x ∈ KSObjectiveChart.densityFloor e a) :
    ‖fderiv ℝ (fderiv ℝ (KSObjectiveChart.objective H B θ e)) x‖ ≤
      upperCoefficient (n := n) a κ θ 1 :=
  objective_hessian_norm_le_explicit H B θ hθ e hisometry x
    (KSObjectiveChart.densityFloor_posDef e ha hx) ha hκ hx.1 hbudget hx.2.le

end MatrixSpencer.KSObjectiveUpper
