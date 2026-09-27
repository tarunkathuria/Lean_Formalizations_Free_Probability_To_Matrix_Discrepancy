import MatrixSpencer.RectangularRidgePotential
import MatrixSpencer.RectangularRidgeParameters
import MatrixSpencer.KSOptimizerFloor
import MatrixSpencer.DyadicDensityCalculus
import MatrixSpencer.RectangularRidgeCalculus
import MatrixSpencer.MSManuscriptOptimizerFloor

/-! Quantitative conditioning for the mixed rectangular objective.
The floor follows from the actual first-order stationarity equation. -/

open Matrix Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.RectangularRidgeOptimizerFloor

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
local instance : CStarAlgebra (Matrix n n ℂ) := {}
local instance : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance

open KSSafeRetirement KSOptimizerFloor RectangularRidgePotential

theorem inverseDyadicRoot_mul_self (m : ℕ)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef) :
    inverseDyadicRoot m S * (S : Matrix n n ℂ) =
      dyadicRoot m (S : Matrix n n ℂ) ^ (2 ^ m - 1) := by
  have hp : 1 ≤ 2 ^ m := Nat.one_le_pow _ _ (by norm_num)
  have he : 2 ^ m = (2 ^ m - 1) + 1 := by omega
  change (dyadicRoot m (S : Matrix n n ℂ))⁻¹ * (S : Matrix n n ℂ) = _
  calc
    _ = (dyadicRoot m (S : Matrix n n ℂ))⁻¹ *
        dyadicRoot m (S : Matrix n n ℂ) ^ (2 ^ m) := by
      rw [dyadicRoot_pow m hS.posSemidef]
    _ = _ := by
      rw [he, pow_succ', ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _
        ((dyadicRoot m (S : Matrix n n ℂ)).isUnit_iff_isUnit_det.mp
          (dyadicRoot_posDef m hS).isUnit), Matrix.one_mul]
      simp

theorem dyadic_gradient_contact_le (m : ℕ) (hm : 1 ≤ m) {θ : ℝ} (hθ : 0 ≤ θ)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef) :
    θ * realTrace (inverseDyadicRoot m S * (S : Matrix n n ℂ)) ≤
      dyadicTsallisRegularizer m θ (S : Matrix n n ℂ) := by
  rw [inverseDyadicRoot_mul_self m S hS]
  have ht := realTrace_nonneg ((dyadicRoot_posSemidef m hS.posSemidef).pow (2 ^ m - 1))
  have hp : (2 : ℝ) ≤ 2 ^ m := by exact_mod_cast dyadic_order_two_le hm
  have hcoef : θ ≤ θ * (2 ^ m : ℝ) / ((2 ^ m : ℝ) - 1) := by
    apply (le_div_iff₀ (by linarith : 0 < (2 ^ m : ℝ) - 1)).mpr
    nlinarith
  exact mul_le_mul_of_nonneg_right hcoef ht

/-- Only the genuine tangent-stationarity identity is used here. The matrix
gradient of the additional dyadic term is positive and its Euler contact is
at most that term's value. -/
theorem inverseSqrt_pairing_le_of_stationary
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (B : ι → Matrix n n ℂ)
    (m : ℕ) (hm : 1 ≤ m) {θ κ : ℝ} (hθ : 0 ≤ θ) (hκ : 0 < κ)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (htr : realTrace (S : Matrix n n ℂ) = 1)
    (hstat : ∀ X : selfAdjoint (Matrix n n ℂ), realTrace (X : Matrix n n ℂ) = 0 →
      realTrace (H * (X : Matrix n n ℂ)) +
      realTrace (actualSupportedGradient B S * (X : Matrix n n ℂ)) +
      θ * realTrace (inverseDyadicRoot m S * (X : Matrix n n ℂ)) +
      κ * realTrace (inverseSqrt S * (X : Matrix n n ℂ)) = 0)
    {T : Matrix n n ℂ} (hT : T ∈ densitySet) :
    κ * realTrace (inverseSqrt S * T) ≤ objective H B m θ κ S + ‖H‖ := by
  let T' : selfAdjoint (Matrix n n ℂ) := ⟨T, hT.1.isHermitian⟩
  have hzero := hstat (T' - S) (by
    change realTrace (T - (S : Matrix n n ℂ)) = 0
    rw [realTrace_sub, hT.2, htr, sub_self])
  change realTrace (H * (T - (S : Matrix n n ℂ))) +
    realTrace (actualSupportedGradient B S * (T - (S : Matrix n n ℂ))) +
    θ * realTrace (inverseDyadicRoot m S * (T - (S : Matrix n n ℂ))) +
    κ * realTrace (inverseSqrt S * (T - (S : Matrix n n ℂ))) = 0 at hzero
  simp only [Matrix.mul_sub, realTrace_sub] at hzero
  rw [actualSupportedGradient_contact B hS, inverseSqrt_mul_self S hS] at hzero
  have hG := realTrace_mul_nonneg (actualSupportedGradient_posSemidef B hS) hT.1
  have hQ := mul_nonneg hθ (realTrace_mul_nonneg (dyadicRoot_posDef m hS).inv.posSemidef hT.1)
  have hHlo := (abs_le.mp (abs_realTrace_mul_density_le_norm hH hT)).1
  have hroot := mul_nonneg hκ.le
    (realTrace_nonneg (CFC.sqrt_nonneg (S : Matrix n n ℂ)).posSemidef)
  have hcontact := dyadic_gradient_contact_le m hm hθ S hS
  change 0 ≤ θ * realTrace (inverseDyadicRoot m S * T) at hQ
  dsimp [objective, dyadicDensityObjective]
  linarith

theorem floor_of_stationary_objective_cap
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (B : ι → Matrix n n ℂ)
    (m : ℕ) (hm : 1 ≤ m) {θ κ K : ℝ} (hθ : 0 ≤ θ) (hκ : 0 < κ) (hK : 0 < K)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (htr : realTrace (S : Matrix n n ℂ) = 1)
    (hstat : ∀ X : selfAdjoint (Matrix n n ℂ), realTrace (X : Matrix n n ℂ) = 0 →
      realTrace (H * (X : Matrix n n ℂ)) +
      realTrace (actualSupportedGradient B S * (X : Matrix n n ℂ)) +
      θ * realTrace (inverseDyadicRoot m S * (X : Matrix n n ℂ)) +
      κ * realTrace (inverseSqrt S * (X : Matrix n n ℂ)) = 0)
    (hcap : objective H B m θ κ S + ‖H‖ ≤ K) :
    (κ / K) ^ 2 • (1 : Matrix n n ℂ) ≤ (S : Matrix n n ℂ) := by
  have hinv : inverseSqrt S ≤ (K / κ) • (1 : Matrix n n ℂ) := by
    apply le_scalar_of_density_pairings hS.posDef_sqrt.inv.isHermitian
    intro T hT
    apply (le_div_iff₀ hκ).mpr
    have hp := inverseSqrt_pairing_le_of_stationary H hH B m hm hθ hκ S hS htr hstat hT
    change realTrace (inverseSqrt S * T) * κ ≤ K
    nlinarith
  simpa only [inv_div] using floor_of_inverseSqrt_le S hS (div_pos hK hκ) hinv

theorem objective_le_input_bound
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (B : ι → Matrix n n ℂ)
    (m : ℕ) (hm : 1 ≤ m) {θ κ R v : ℝ} (hθ : 0 ≤ θ) (hκ : 0 ≤ κ)
    (hR : ‖H‖ ≤ R) (hbudget : (∑ i, (B i)ᴴ * B i) ≤ v • (1 : Matrix n n ℂ))
    {S : Matrix n n ℂ} (hS : S ∈ densitySet) :
    objective H B m θ κ S ≤ R + 2 * Real.sqrt v +
      θ * (Fintype.card n : ℝ) ^ (1 / (2 ^ m : ℝ)) / (1 - 1 / (2 ^ m : ℝ)) +
      2 * κ * Real.sqrt (Fintype.card n : ℝ) := by
  have hlin := (realTrace_mul_density_le_norm hH hS).trans hR
  have hfid := fidelity_le_sqrt_trace_mul hS.1 (krausChannel_posSemidef B hS.1)
  rw [hS.2, one_mul] at hfid
  have hf := hfid.trans (Real.sqrt_le_sqrt (kraus_trace_le_of_budget B hbudget hS))
  have hq := dyadicTsallisRegularizer_density_bound_reciprocal hm hθ hS
  have hr := mul_le_mul_of_nonneg_left (density_trace_sqrt_le_sqrt_card hS)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hκ)
  dsimp [objective, dyadicDensityObjective]
  linarith

theorem maximizer_stationary_expanded
    (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (m : ℕ) (hm : 1 ≤ m) (θ κ : ℝ)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (htr : realTrace (S : Matrix n n ℂ) = 1)
    (hmax : ∀ T ∈ densitySet, objective H B m θ κ T ≤ objective H B m θ κ S) :
    ∀ X : selfAdjoint (Matrix n n ℂ), realTrace (X : Matrix n n ℂ) = 0 →
      realTrace (H * (X : Matrix n n ℂ)) +
      realTrace (actualSupportedGradient B S * (X : Matrix n n ℂ)) +
      θ * realTrace (inverseDyadicRoot m S * (X : Matrix n n ℂ)) +
      κ * realTrace (inverseSqrt S * (X : Matrix n n ℂ)) = 0 := by
  intro X hX
  have hs := RectangularRidgeCalculus.maximizer_stationary H B m θ κ S hS htr hmax
  have hh := congrArg (fun F : densityTangent (n := n) →L[ℝ] ℝ => F ⟨X, hX⟩) hs
  change fderiv ℝ (RectangularRidgeCalculus.hermitianObjective H B m θ κ) S X = 0 at hh
  rw [RectangularRidgeCalculus.fderiv_hermitianObjective_eq H B m hm θ κ S hS,
    fderiv_krausSourceFidelity_eq_supportedGradient B S hS] at hh
  exact hh

/-- The actual canonical optimizer has a quantitative floor from its actual
objective cap. There is no assumed stationarity or assumed optimizer floor. -/
theorem optimizer_floor_of_objective_cap [Nonempty n]
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (B : ι → Matrix n n ℂ)
    (m : ℕ) (hm : 1 ≤ m) {θ κ K : ℝ} (hθ : 0 < θ) (hκ : 0 < κ) (hK : 0 < K)
    (hcap : objective H B m θ κ (optimizer H B m θ κ) + ‖H‖ ≤ K) :
    (κ / K) ^ 2 • (1 : Matrix n n ℂ) ≤ optimizer H B m θ κ := by
  let S := RectangularRidgeCalculus.hermitianOptimizer H B m θ κ
  have hS : (S : Matrix n n ℂ).PosDef := optimizer_posDef H B hm hθ hκ.le
  have htr : realTrace (S : Matrix n n ℂ) = 1 := (optimizer_mem H B m θ κ).2
  have hmax : ∀ T ∈ densitySet, objective H B m θ κ T ≤ objective H B m θ κ S :=
    optimizer_max H B m θ κ
  exact floor_of_stationary_objective_cap H hH B m hm hθ.le hκ hK S hS htr
    (maximizer_stationary_expanded H B m hm θ κ S hS htr hmax) hcap

/-- A uniform polynomial floor for the actual mixed optimizer with the actual
dyadic exponent and strength. The input assumptions are norm and source
budgets, rather than an assumed bound on the maximizing density. -/
theorem optimizer_polynomial_floor [Nonempty n]
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (B : ι → Matrix n n ℂ)
    {N : ℝ} (hN : 1 ≤ N) (hHn : ‖H‖ ≤ N)
    (hbudget : (∑ i, (B i)ᴴ * B i) ≤ N ^ 2 • (1 : Matrix n n ℂ)) :
    RectangularRidgeParameters.densityFloor (Fintype.card n : ℝ) N • (1 : Matrix n n ℂ) ≤
      optimizer H B (RectangularParameters.dyadicDepth (Fintype.card n : ℝ) N)
        (RectangularRidgeParameters.θ (Fintype.card n : ℝ) N)
        (RectangularRidgeParameters.ridge (Fintype.card n : ℝ)) := by
  let D : ℝ := Fintype.card n
  let Q := RectangularRidgeParameters.size D N
  let m := RectangularParameters.dyadicDepth D N
  let θ := RectangularRidgeParameters.θ D N
  let κ := RectangularRidgeParameters.ridge D
  have hD : 1 ≤ D := by
    have hh : 1 ≤ Fintype.card n := Fintype.card_pos
    change (1 : ℝ) ≤ (Fintype.card n : ℝ)
    exact_mod_cast hh
  have hD0 : 0 < D := by linarith
  have hN0 : 0 ≤ N := by linarith
  have hQ : 0 < Q := RectangularRidgeParameters.size_pos hD hN
  have hm : 1 ≤ m := RectangularParameters.dyadicDepth_pos D N
  have hθ : 0 < θ := RectangularRidgeParameters.weight_positive hD hN
  have hκ : 0 < κ := by dsimp [κ, RectangularRidgeParameters.ridge]; positivity
  have hq : 1 / (2 ^ m : ℝ) = RectangularRidgeParameters.q D N := by
    simp [m, RectangularRidgeParameters.q, RectangularParameters.dyadicOrder]
  have hr := RectangularRidgeParameters.regularizer_budget_le hD hN
  have hroot := RectangularRidgeParameters.ridge_overhead_le_two hD
  have hin := objective_le_input_bound H hH B m hm hθ.le hκ.le hHn hbudget
    (optimizer_mem H B m θ κ)
  rw [Real.sqrt_sq hN0, hq] at hin
  have hcap : objective H B m θ κ (optimizer H B m θ κ) + ‖H‖ ≤ 100 * Q := by
    change objective H B m θ κ (optimizer H B m θ κ) ≤
      N + 2 * N + θ * D ^ RectangularRidgeParameters.q D N /
        (1 - RectangularRidgeParameters.q D N) + 2 * κ * Real.sqrt D at hin
    change θ * D ^ RectangularRidgeParameters.q D N /
      (1 - RectangularRidgeParameters.q D N) ≤ 81 * Q at hr
    change 2 * κ * Real.sqrt D ≤ 2 at hroot
    have hNQ : N + 1 ≤ Q := by dsimp [Q, RectangularRidgeParameters.size]; linarith
    linarith
  have hbase := optimizer_floor_of_objective_cap H hH B m hm hθ hκ
    (by positivity : 0 < 100 * Q) hcap
  have hDQ : D ≤ Q := by dsimp [Q, RectangularRidgeParameters.size]; linarith
  have hden : D * (100 * Q) ≤ 100 * Q ^ 2 := by nlinarith
  have hratio : 1 / (100 * Q ^ 2) ≤ κ / (100 * Q) := by
    dsimp [κ, RectangularRidgeParameters.ridge]
    rw [div_div]
    exact one_div_le_one_div_of_le (by positivity) hden
  have hs := mul_self_le_mul_self (by positivity : 0 ≤ 1 / (100 * Q ^ 2)) hratio
  have hid : (1 / (100 * Q ^ 2)) ^ 2 = RectangularRidgeParameters.densityFloor D N := by
    dsimp [RectangularRidgeParameters.densityFloor]
    change (1 / (100 * Q ^ 2)) ^ 2 = 1 / (10000 * Q ^ 4)
    field_simp
    <;> ring
  have hscalar : RectangularRidgeParameters.densityFloor D N ≤ (κ / (100 * Q)) ^ 2 := by
    simpa only [← pow_two, hid] using hs
  refine le_trans ?_ hbase
  apply Matrix.le_iff.mpr
  rw [← sub_smul]
  exact Matrix.PosSemidef.one.smul (sub_nonneg.mpr hscalar)

/-- The source budget in the polynomial floor is proved from a contraction
input family and a PSD owner bounded by the identity. The global original
coordinate count `N` may exceed the currently retained family size. -/
theorem covariance_optimizer_polynomial_floor [Nonempty n] [DecidableEq ι]
    (H : Matrix n n ℂ) (hH : H.IsHermitian)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) (hAn : ∀ i, ‖A i‖ ≤ 1)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (hC1 : C ≤ 1)
    {N : ℝ} (hN : 1 ≤ N) (hcount : (Fintype.card ι : ℝ) ≤ N) (hHn : ‖H‖ ≤ N) :
    RectangularRidgeParameters.densityFloor (Fintype.card n : ℝ) N • (1 : Matrix n n ℂ) ≤
      optimizer H (covarianceKraus A C)
        (RectangularParameters.dyadicDepth (Fintype.card n : ℝ) N)
        (RectangularRidgeParameters.θ (Fintype.card n : ℝ) N)
        (RectangularRidgeParameters.ridge (Fintype.card n : ℝ)) := by
  apply optimizer_polynomial_floor H hH (covarianceKraus A C) hN hHn
  refine (MSManuscriptOptimizerFloor.covariance_budget A hA hAn hC hC1).trans ?_
  apply Matrix.le_iff.mpr
  rw [← sub_smul]
  apply Matrix.PosSemidef.one.smul
  exact sub_nonneg.mpr (by
    nlinarith [show (0 : ℝ) ≤ (Fintype.card ι : ℝ) from Nat.cast_nonneg _])

end MatrixSpencer.RectangularRidgeOptimizerFloor
