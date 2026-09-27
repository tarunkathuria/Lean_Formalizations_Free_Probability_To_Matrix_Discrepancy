import MatrixSpencer.DyadicRoot
import MatrixSpencer.DensityDomain
import Mathlib.Analysis.MeanInequalities

/-!
# Bounds for the actual dyadic trace-power regularizer

The proof diagonalizes the actual positive dyadic root and applies the
proved scalar Hölder inequality to its eigenvalues. No matrix trace
concavity or Hölder assertion is assumed.
-/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer

variable {n : Type*} [Fintype n] [DecidableEq n]
local instance dyadicTraceBoundsCStar : CStarAlgebra (Matrix n n ℂ) := {}

theorem unitary_conjugate_natPower (U : unitary (Matrix n n ℂ)) (D : Matrix n n ℂ) (p : ℕ) :
    ((U : Matrix n n ℂ) * D * star (U : Matrix n n ℂ)) ^ p =
      (U : Matrix n n ℂ) * D ^ p * star (U : Matrix n n ℂ) := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [pow_succ, ih, pow_succ]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (star (U : Matrix n n ℂ)) (U : Matrix n n ℂ),
      unitary.star_mul_self_of_mem U.property, Matrix.one_mul]

theorem realTrace_natPower_eq_sum_eigenvalues (p : ℕ) (Q : Matrix n n ℂ)
    (hQ : Q.IsHermitian) :
    realTrace (Q ^ p) = ∑ i, (hQ.eigenvalues i) ^ p := by
  conv_lhs => rw [hQ.spectral_theorem]
  rw [unitary_conjugate_natPower, realTrace_mul_cycle]
  rw [unitary.star_mul_self_of_mem hQ.eigenvectorUnitary.property, Matrix.one_mul,
    Matrix.diagonal_pow]
  simp [realTrace, Matrix.trace_diagonal, Function.comp_def]
  apply Finset.sum_congr rfl
  intro i _
  norm_cast

omit [DecidableEq n] in
theorem sum_pred_powers_le_of_sum_power_eq_one {p : ℕ} (hp : 2 ≤ p)
    (x : n → ℝ) (hx : ∀ i, 0 ≤ x i) (hsum : ∑ i, x i ^ p = 1) :
    ∑ i, x i ^ (p - 1) ≤ (Fintype.card n : ℝ) ^ (1 / (p : ℝ)) := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by omega)
  have hpne : (p : ℝ) - 1 ≠ 0 := by linarith
  have hpow : ∀ i, (x i ^ (p - 1)) ^ ((p : ℝ) / ((p : ℝ) - 1)) = x i ^ p := by
    intro i
    rw [← Real.rpow_natCast (x i) (p - 1), ← Real.rpow_mul (hx i),
      Nat.cast_sub (show 1 ≤ p by omega), Nat.cast_one, ← Real.rpow_natCast (x i) p]
    congr 1
    field_simp [hpne]
  have h := Real.inner_le_Lp_mul_Lq_of_nonneg (s := Finset.univ)
    (f := fun _ : n => (1 : ℝ)) (g := fun i => x i ^ (p - 1))
    (Real.HolderConjugate.conjExponent hpR) (by intro i _; norm_num)
    (by intro i _; exact pow_nonneg (hx i) _)
  simpa only [Real.conjExponent, one_mul, hpow, hsum, Real.one_rpow, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one] using h

/-- The natural-power trace inequality applies directly to the actual positive root. -/
theorem realTrace_pred_power_le_of_trace_power_eq_one {p : ℕ} (hp : 2 ≤ p)
    (Q : Matrix n n ℂ) (hQ : Q.PosSemidef) (htrace : realTrace (Q ^ p) = 1) :
    realTrace (Q ^ (p - 1)) ≤ (Fintype.card n : ℝ) ^ (1 / (p : ℝ)) := by
  rw [realTrace_natPower_eq_sum_eigenvalues (p - 1) Q hQ.isHermitian]
  apply sum_pred_powers_le_of_sum_power_eq_one hp hQ.isHermitian.eigenvalues hQ.eigenvalues_nonneg
  rwa [realTrace_natPower_eq_sum_eigenvalues p Q hQ.isHermitian] at htrace

/-- The unscaled trace used by the dyadic Tsallis regularizer. -/
def dyadicTracePower (m : ℕ) (S : Matrix n n ℂ) : ℝ :=
  realTrace ((dyadicRoot m S) ^ (2 ^ m - 1))

theorem continuous_dyadicTracePower_of_psd {X : Type*} [TopologicalSpace X]
    {S : X → Matrix n n ℂ} (hS : Continuous S) (hpos : ∀ x, (S x).PosSemidef) (m : ℕ) :
    Continuous (fun x => dyadicTracePower m (S x)) :=
  continuous_realTrace.comp ((continuous_dyadicRoot_of_psd hS hpos m).pow _)

theorem continuousOn_dyadicTracePower (m : ℕ) :
    ContinuousOn (dyadicTracePower (n := n) m) {S | S.PosSemidef} := by
  rw [continuousOn_iff_continuous_restrict]
  exact continuous_dyadicTracePower_of_psd continuous_subtype_val (fun S => S.property) m

theorem dyadicTracePower_nonneg (m : ℕ) {S : Matrix n n ℂ} (hS : S.PosSemidef) :
    0 ≤ dyadicTracePower m S :=
  realTrace_nonneg ((dyadicRoot_posSemidef m hS).pow _)

theorem dyadicTracePower_le_dimension_rpow {m : ℕ} (hm : 1 ≤ m)
    {S : Matrix n n ℂ} (hS : S.PosSemidef) (htrace : realTrace S = 1) :
    dyadicTracePower m S ≤ (Fintype.card n : ℝ) ^ (1 / ((2 ^ m : ℕ) : ℝ)) := by
  apply realTrace_pred_power_le_of_trace_power_eq_one
  · exact (show 2 ^ 1 ≤ 2 ^ m from Nat.pow_le_pow_right (by norm_num) hm)
  · exact dyadicRoot_posSemidef m hS
  · rwa [dyadicRoot_pow m hS]

theorem dyadicRoot_eq_of_idempotent (m : ℕ) {S : Matrix n n ℂ}
    (hS : S.PosSemidef) (hidem : S * S = S) : dyadicRoot m S = S := by
  induction m with
  | zero => rfl
  | succ m ih => rw [dyadicRoot_succ, ih]; exact CFC.sqrt_unique hidem hS.nonneg

/-- In particular the trace regularizer equals one at every rank-one density projection. -/
theorem dyadicTracePower_eq_trace_of_idempotent {m : ℕ} (hm : 1 ≤ m)
    {S : Matrix n n ℂ} (hS : S.PosSemidef) (hidem : S * S = S) :
    dyadicTracePower m S = realTrace S := by
  have hp : 2 ≤ 2 ^ m := (show 2 ^ 1 ≤ 2 ^ m from Nat.pow_le_pow_right (by norm_num) hm)
  rw [dyadicTracePower, dyadicRoot_eq_of_idempotent m hS hidem,
    (show IsIdempotentElem S from hidem).pow_eq (show 2 ^ m - 1 ≠ 0 by omega)]

theorem dyadicTracePower_eq_one_of_density_projection {m : ℕ} (hm : 1 ≤ m)
    {S : Matrix n n ℂ} (hS : S.PosSemidef) (hidem : S * S = S) (htrace : realTrace S = 1) :
    dyadicTracePower m S = 1 := by
  rw [dyadicTracePower_eq_trace_of_idempotent hm hS hidem, htrace]

theorem matrix_sqrt_real_smul_one {c : ℝ} (hc : 0 ≤ c) :
    CFC.sqrt (c • (1 : Matrix n n ℂ)) = Real.sqrt c • (1 : Matrix n n ℂ) := by
  apply CFC.sqrt_unique
  · simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul,
      Real.mul_self_sqrt hc]
  · exact smul_nonneg (Real.sqrt_nonneg _) zero_le_one

theorem dyadicRoot_real_smul_one (m : ℕ) {c : ℝ} (hc : 0 ≤ c) :
    dyadicRoot m (c • (1 : Matrix n n ℂ)) = c ^ ((1 / 2 : ℝ) ^ m) • (1 : Matrix n n ℂ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [dyadicRoot_succ, ih, matrix_sqrt_real_smul_one (Real.rpow_nonneg hc _),
      Real.sqrt_eq_rpow, ← Real.rpow_mul hc, pow_succ]

theorem dyadicTracePower_real_smul_one (m : ℕ) {c : ℝ} (hc : 0 ≤ c) :
    dyadicTracePower m (c • (1 : Matrix n n ℂ)) =
      (Fintype.card n : ℝ) * c ^ (1 - (1 / 2 : ℝ) ^ m) := by
  have hp : 1 ≤ 2 ^ m := Nat.one_le_pow m 2 (by norm_num)
  have hprod : (1 / 2 : ℝ) ^ m * ((2 ^ m : ℕ) : ℝ) = 1 := by
    rw [Nat.cast_pow, Nat.cast_ofNat, ← mul_pow]
    norm_num
  have he : (c ^ ((1 / 2 : ℝ) ^ m)) ^ (2 ^ m - 1) = c ^ (1 - (1 / 2 : ℝ) ^ m) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hc, Nat.cast_sub hp, Nat.cast_one]
    congr 1
    nlinarith
  rw [dyadicTracePower, dyadicRoot_real_smul_one m hc, smul_pow, one_pow, realTrace_smul, he]
  simp only [realTrace, Matrix.trace_one]
  rw [mul_comm]
  congr 1

/-- The maximum density bound is attained at the normalized identity. -/
theorem dyadicTracePower_normalized_identity (m : ℕ) [Nonempty n] :
    dyadicTracePower m ((1 / (Fintype.card n : ℝ)) • (1 : Matrix n n ℂ)) =
      (Fintype.card n : ℝ) ^ (1 / ((2 ^ m : ℕ) : ℝ)) := by
  have hd : (0 : ℝ) < Fintype.card n := Nat.cast_pos.mpr Fintype.card_pos
  rw [dyadicTracePower_real_smul_one m (by positivity), one_div, Real.inv_rpow hd.le,
    ← Real.rpow_neg hd.le]
  conv_lhs => lhs; rw [← Real.rpow_one (Fintype.card n : ℝ)]
  rw [← Real.rpow_add hd]
  congr 1
  rw [show 1 + -(1 - (1 / 2 : ℝ) ^ m) = (1 / 2 : ℝ) ^ m by ring,
    _root_.one_div_pow, Nat.cast_pow, Nat.cast_ofNat]

theorem normalized_identity_posSemidef :
    ((1 / (Fintype.card n : ℝ)) • (1 : Matrix n n ℂ)).PosSemidef :=
  (smul_nonneg (by positivity) (zero_le_one : (0 : Matrix n n ℂ) ≤ 1)).posSemidef

theorem realTrace_normalized_identity [Nonempty n] :
    realTrace ((1 / (Fintype.card n : ℝ)) • (1 : Matrix n n ℂ)) = 1 := by
  simp [realTrace]

end MatrixSpencer
