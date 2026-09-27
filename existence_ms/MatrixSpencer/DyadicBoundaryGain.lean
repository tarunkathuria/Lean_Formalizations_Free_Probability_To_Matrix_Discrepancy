import MatrixSpencer.DyadicTsallisHessian
import MatrixSpencer.DensityFaithfulness
import MatrixSpencer.RegularizedOwnerPotential

/-!
# Boundary gain for the actual dyadic Tsallis regularizer

Repeated positive square roots preserve an orthogonal kernel projection.
Scalar iterated roots express the exact mixing identity without requiring
an independent matrix real-power calculus.
-/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

namespace MatrixSpencer
namespace DyadicBoundaryGain

def scalarRoot : ℕ → ℝ → ℝ
  | 0, a => a
  | m + 1, a => Real.sqrt (scalarRoot m a)

theorem scalarRoot_nonneg (m : ℕ) {a : ℝ} (ha : 0 ≤ a) : 0 ≤ scalarRoot m a := by
  cases m with
  | zero => exact ha
  | succ m => exact Real.sqrt_nonneg _

theorem scalarRoot_le_one (m : ℕ) {a : ℝ} (ha : a ≤ 1) : scalarRoot m a ≤ 1 := by
  induction m with
  | zero => exact ha
  | succ m ih =>
    simpa only [scalarRoot, Real.sqrt_one] using Real.sqrt_le_sqrt ih

theorem scalarRoot_pow (m : ℕ) {a : ℝ} (ha : 0 ≤ a) : scalarRoot m a ^ (2 ^ m) = a := by
  induction m with
  | zero => simp [scalarRoot]
  | succ m ih =>
    rw [Nat.pow_succ, Nat.mul_comm (2 ^ m) 2, pow_mul]
    change ((Real.sqrt (scalarRoot m a)) ^ 2) ^ (2 ^ m) = a
    rw [Real.sq_sqrt (scalarRoot_nonneg m ha), ih]

theorem scalarRoot_of_pow (m : ℕ) {r : ℝ} (hr : 0 ≤ r) : scalarRoot m (r ^ (2 ^ m)) = r := by
  induction m generalizing r with
  | zero => simp [scalarRoot]
  | succ m ih =>
    have he : r ^ (2 ^ (m + 1)) = (r ^ 2) ^ (2 ^ m) := by
      rw [← pow_mul, Nat.pow_succ, Nat.mul_comm (2 ^ m) 2]
    rw [scalarRoot, he, ih (sq_nonneg r), Real.sqrt_sq hr]

theorem order_ge_two {m : ℕ} (hm : 1 ≤ m) : 2 ≤ 2 ^ m := by
  calc
    2 = 2 ^ (1 : ℕ) := by norm_num
    _ ≤ 2 ^ m := Nat.pow_le_pow_right (by omega) hm

theorem scalarRoot_power_lower {m : ℕ} (hm : 1 ≤ m) {a : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1) : a ≤ scalarRoot m a ^ (2 ^ m - 1) := by
  have hp := order_ge_two hm
  have he : (2 ^ m - 1) + 1 = 2 ^ m := by omega
  have h := mul_le_mul_of_nonneg_left (scalarRoot_le_one m ha1)
    (pow_nonneg (scalarRoot_nonneg m ha) (2 ^ m - 1))
  rw [← pow_succ, he, scalarRoot_pow m ha, mul_one] at h
  exact h

variable {n : Type*} [Fintype n] [DecidableEq n]
local instance dyadicBoundaryCStar : CStarAlgebra (Matrix n n ℂ) := {}

theorem sqrt_projection_zero {S U : Matrix n n ℂ}
    (hS : S.PosSemidef) (hU : U.PosSemidef) (hSU : S * U = 0) :
    CFC.sqrt S * U = 0 ∧ U * CFC.sqrt S = 0 := by
  have hroot := (CFC.sqrt_nonneg S).posSemidef.isHermitian
  have hleft : CFC.sqrt S * U = 0 := by
    apply (realTrace_conjTranspose_mul_self_eq_zero_iff (CFC.sqrt S * U)).mp
    rw [Matrix.conjTranspose_mul, hroot.eq, hU.isHermitian.eq]
    calc
      _ = realTrace (U * (CFC.sqrt S * CFC.sqrt S) * U) := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [CFC.sqrt_mul_sqrt_self S hS.nonneg, Matrix.mul_assoc,
        hSU, Matrix.mul_zero, realTrace_zero]
  refine ⟨hleft, ?_⟩
  have h := congrArg Matrix.conjTranspose hleft
  simpa only [Matrix.conjTranspose_mul, hroot.eq, hU.isHermitian.eq,
    Matrix.conjTranspose_zero] using h

theorem root_projection_zero (m : ℕ) {S U : Matrix n n ℂ}
    (hS : S.PosSemidef) (hU : U.PosSemidef) (hSU : S * U = 0) (hUS : U * S = 0) :
    dyadicRoot m S * U = 0 ∧ U * dyadicRoot m S = 0 := by
  induction m with
  | zero => exact ⟨hSU, hUS⟩
  | succ m ih => exact sqrt_projection_zero (dyadicRoot_posSemidef m hS) hU ih.1

/-- Exact matrix mixing with scalar iterated-root coefficients. -/
theorem root_orthogonal_projection_mix (m : ℕ) {S U : Matrix n n ℂ}
    (hS : S.PosSemidef) (hU : U.PosSemidef) (hUU : U * U = U)
    (hSU : S * U = 0) (hUS : U * S = 0) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    dyadicRoot m (a • S + b • U) =
      scalarRoot m a • dyadicRoot m S + scalarRoot m b • U := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [dyadicRoot_succ, ih]
    exact sqrt_orthogonal_projection_mix (dyadicRoot_posSemidef m hS) hU hUU
      (root_projection_zero (m + 1) hS hU hSU hUS).1
      (root_projection_zero (m + 1) hS hU hSU hUS).2
      (scalarRoot_nonneg m ha) (scalarRoot_nonneg m hb)

theorem power_mul_zero {T U : Matrix n n ℂ} (hTU : T * U = 0)
    {j : ℕ} (hj : 0 < j) : T ^ j * U = 0 := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj.ne'
  rw [pow_succ, Matrix.mul_assoc, hTU, Matrix.mul_zero]

/-- Positive powers split exactly because all cross products vanish. -/
theorem power_orthogonal_projection_mix {T U : Matrix n n ℂ}
    (hUU : U * U = U) (hTU : T * U = 0) (hUT : U * T = 0)
    (a b : ℝ) {j : ℕ} (hj : 0 < j) :
    (a • T + b • U) ^ j = a ^ j • T ^ j + b ^ j • U := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj.ne'
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ, ih (Nat.succ_pos r)]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
      hUU, hUT, power_mul_zero hTU (Nat.succ_pos r), smul_zero, add_zero,
      zero_add, smul_smul, ← pow_succ, ← pow_succ']

def tracePower (m : ℕ) (S : Matrix n n ℂ) : ℝ :=
  realTrace (dyadicRoot m S ^ (2 ^ m - 1))

theorem tracePower_nonneg (m : ℕ) {S : Matrix n n ℂ} (hS : S.PosSemidef) :
    0 ≤ tracePower m S := realTrace_nonneg ((dyadicRoot_posSemidef m hS).pow _)

/-- Exact unscaled Tsallis mixing, including singular endpoints. -/
theorem tracePower_orthogonal_projection_mix {m : ℕ} (hm : 1 ≤ m)
    {S U : Matrix n n ℂ} (hS : S.PosSemidef) (hU : U.PosSemidef)
    (htrace : realTrace U = 1) (hUU : U * U = U)
    (hSU : S * U = 0) (hUS : U * S = 0) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    tracePower m (a • S + b • U) =
      scalarRoot m a ^ (2 ^ m - 1) * tracePower m S + scalarRoot m b ^ (2 ^ m - 1) := by
  have hp : 0 < 2 ^ m - 1 := by have := order_ge_two hm; omega
  unfold tracePower
  rw [root_orthogonal_projection_mix m hS hU hUU hSU hUS ha hb,
    power_orthogonal_projection_mix hUU (root_projection_zero m hS hU hSU hUS).1
      (root_projection_zero m hS hU hSU hUS).2 _ _ hp,
    realTrace_add, realTrace_smul, realTrace_smul, htrace, mul_one]

theorem tracePower_kernel_perturbation_lower {m : ℕ} (hm : 1 ≤ m)
    {S U : Matrix n n ℂ} (hS : S.PosSemidef) (hU : U.PosSemidef)
    (htrace : realTrace U = 1) (hUU : U * U = U)
    (hSU : S * U = 0) (hUS : U * S = 0) {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    (1 - r ^ (2 ^ m)) * tracePower m S + r ^ (2 ^ m - 1) ≤
      tracePower m ((1 - r ^ (2 ^ m)) • S + r ^ (2 ^ m) • U) := by
  have hrpow : r ^ (2 ^ m) ≤ 1 := pow_le_one₀ hr hr1
  have ha : 0 ≤ 1 - r ^ (2 ^ m) := by linarith
  rw [tracePower_orthogonal_projection_mix hm hS hU htrace hUU hSU hUS ha
    (pow_nonneg hr _), scalarRoot_of_pow m hr]
  apply add_le_add_right
  exact mul_le_mul_of_nonneg_right
    (scalarRoot_power_lower hm ha (by linarith [pow_nonneg hr (2 ^ m)])) (tracePower_nonneg m hS)

def scale (m : ℕ) (θ : ℝ) : ℝ := θ * (2 ^ m : ℝ) / ((2 ^ m : ℝ) - 1)

theorem scale_nonneg {m : ℕ} (hm : 1 ≤ m) {θ : ℝ} (hθ : 0 ≤ θ) : 0 ≤ scale m θ := by
  have hp : (2 : ℝ) ≤ (2 : ℝ) ^ m := by exact_mod_cast order_ge_two hm
  unfold scale
  exact div_nonneg (mul_nonneg hθ (by positivity)) (by linarith)

theorem scale_pos {m : ℕ} (hm : 1 ≤ m) {θ : ℝ} (hθ : 0 < θ) : 0 < scale m θ := by
  have hp : (2 : ℝ) ≤ (2 : ℝ) ^ m := by exact_mod_cast order_ge_two hm
  unfold scale
  exact div_pos (mul_pos hθ (by positivity)) (by linarith)

theorem regularizer_kernel_perturbation_lower {m : ℕ} (hm : 1 ≤ m) {θ : ℝ} (hθ : 0 ≤ θ)
    {S U : Matrix n n ℂ} (hS : S.PosSemidef) (hU : U.PosSemidef)
    (htrace : realTrace U = 1) (hUU : U * U = U)
    (hSU : S * U = 0) (hUS : U * S = 0) {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    (1 - r ^ (2 ^ m)) * dyadicTsallisRegularizer m θ S + scale m θ * r ^ (2 ^ m - 1) ≤
      dyadicTsallisRegularizer m θ ((1 - r ^ (2 ^ m)) • S + r ^ (2 ^ m) • U) := by
  have h := mul_le_mul_of_nonneg_left
    (tracePower_kernel_perturbation_lower hm hS hU htrace hUU hSU hUS hr hr1)
    (scale_nonneg hm hθ)
  simpa only [dyadicTsallisRegularizer, tracePower, scale, mul_add,
    mul_assoc, mul_left_comm] using h

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The genuine owner objective gains at order r^(p-1), while the other terms lose at order r^p. -/
theorem ownerObjective_kernel_perturbation_lower (H : Matrix n n ℂ)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) {m : ℕ} (hm : 1 ≤ m)
    {θ : ℝ} (hθ : 0 ≤ θ) {S U : Matrix n n ℂ}
    (hS : S.PosSemidef) (hU : U.PosSemidef) (htrace : realTrace U = 1)
    (hUU : U * U = U) (hSU : S * U = 0) (hUS : U * S = 0)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    (1 - r ^ (2 ^ m)) * regularizedOwnerObjective H A C (dyadicTsallisRegularizer m θ) S +
      r ^ (2 ^ m) * realTrace (H * U) + scale m θ * r ^ (2 ^ m - 1) ≤
      regularizedOwnerObjective H A C (dyadicTsallisRegularizer m θ)
        ((1 - r ^ (2 ^ m)) • S + r ^ (2 ^ m) • U) := by
  have hrpow : r ^ (2 ^ m) ≤ 1 := pow_le_one₀ hr hr1
  have ha : 0 ≤ 1 - r ^ (2 ^ m) := by linarith
  have hb : 0 ≤ r ^ (2 ^ m) := pow_nonneg hr _
  have hf := fidelity_concave hS hU (covarianceSource_posSemidef A hA hC hS)
    (covarianceSource_posSemidef A hA hC hU) ha hb (by ring)
  have hfU := mul_nonneg hb (fidelity_nonneg U (covarianceSource A C U))
  have hreg := regularizer_kernel_perturbation_lower hm hθ hS hU htrace hUU hSU hUS hr hr1
  simp only [regularizedOwnerObjective, covarianceSource_weighted_add, Matrix.mul_add,
    Matrix.mul_smul, realTrace_add, realTrace_smul]
  nlinarith

/-- Every actual maximizing density is faithful for a positive dyadic Tsallis scale.
No positivity conclusion or boundary-repulsion estimate is an input. -/
theorem owner_maximizer_posDef (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) {C : Matrix ι ι ℝ} (hC : C.PosSemidef)
    {m : ℕ} (hm : 1 ≤ m) {θ : ℝ} (hθ : 0 < θ)
    {S : Matrix n n ℂ} (hS : S ∈ densitySet)
    (hmax : ∀ T ∈ densitySet,
      regularizedOwnerObjective H A C (dyadicTsallisRegularizer m θ) T ≤
        regularizedOwnerObjective H A C (dyadicTsallisRegularizer m θ) S) : S.PosDef := by
  by_contra hn
  obtain ⟨U, hU, htrace, hUU, hrootU, hUroot⟩ := exists_kernel_density_projection hS.1 hn
  have hSU : S * U = 0 := by
    calc
      _ = CFC.sqrt S * (CFC.sqrt S * U) := by
        rw [← Matrix.mul_assoc, CFC.sqrt_mul_sqrt_self S hS.1.nonneg]
      _ = 0 := by rw [hrootU, Matrix.mul_zero]
  have hUS : U * S = 0 := by
    calc
      _ = (U * CFC.sqrt S) * CFC.sqrt S := by
        rw [Matrix.mul_assoc, CFC.sqrt_mul_sqrt_self S hS.1.nonneg]
      _ = 0 := by rw [hUroot, Matrix.zero_mul]
  let K := |realTrace (H * U) - regularizedOwnerObjective H A C (dyadicTsallisRegularizer m θ) S|
  have hK : 0 ≤ K := abs_nonneg _
  have hK1 : 0 < K + 1 := by linarith
  have hc : 0 < scale m θ := scale_pos hm hθ
  have hsmall : 0 < min 1 (scale m θ / (K + 1)) :=
    lt_min (by norm_num) (div_pos hc hK1)
  obtain ⟨r, hr, hrsmall⟩ := exists_between hsmall
  have hr1 : r < 1 := (lt_min_iff.mp hrsmall).1
  have hrK1 : r * (K + 1) < scale m θ :=
    (lt_div_iff₀ hK1).mp (lt_min_iff.mp hrsmall).2
  have hrK : K * r < scale m θ := by nlinarith
  have he : (2 ^ m - 1) + 1 = 2 ^ m := by have := order_ge_two hm; omega
  have hgain : 0 < scale m θ * r ^ (2 ^ m - 1) - r ^ (2 ^ m) * K := by
    calc
      0 < r ^ (2 ^ m - 1) * (scale m θ - K * r) :=
        mul_pos (pow_pos hr _) (sub_pos.mpr hrK)
      _ = scale m θ * r ^ (2 ^ m - 1) - r ^ (2 ^ m) * K := by
        have hpow : r ^ (2 ^ m) = r ^ (2 ^ m - 1) * r := by rw [← pow_succ, he]
        rw [hpow]
        ring
  have hrpow : r ^ (2 ^ m) ≤ 1 := pow_le_one₀ hr.le hr1.le
  have ha : 0 ≤ 1 - r ^ (2 ^ m) := by linarith
  have hb : 0 ≤ r ^ (2 ^ m) := pow_nonneg hr.le _
  have hmix : (1 - r ^ (2 ^ m)) • S + r ^ (2 ^ m) • U ∈ densitySet :=
    densitySet_convex hS ⟨hU, htrace⟩ ha hb (by ring)
  have hlower := ownerObjective_kernel_perturbation_lower H A hA hC hm hθ.le
    hS.1 hU htrace hUU hSU hUS hr.le hr1.le
  have hupper := hmax ((1 - r ^ (2 ^ m)) • S + r ^ (2 ^ m) • U) hmix
  have herr : -K ≤ realTrace (H * U) -
      regularizedOwnerObjective H A C (dyadicTsallisRegularizer m θ) S := neg_abs_le _
  have herr' := mul_le_mul_of_nonneg_left herr hb
  nlinarith

end DyadicBoundaryGain
end MatrixSpencer
