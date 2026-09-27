import MatrixSpencer.RectangularRidgeSquareJetIdentities

/-! Actual derivatives of integer powers of a matrix curve through order four.
The bounds grow polynomially in the integer exponent, even for noncommuting
matrix jets. -/

open Matrix Filter Topology
open scoped Matrix.Norms.L2Operator ContDiff
noncomputable section
namespace MatrixSpencer.RectangularRidgePowerJetBounds
open RectangularRidgeSquareJetIdentities
variable {n : Type*} [Fintype n] [DecidableEq n]
local instance ridgePowerJetCStar : CStarAlgebra (Matrix n n ℂ) := {}
variable {f g : ℝ → Matrix n n ℂ} {t : ℝ}

theorem product_first (hf : ContDiffAt ℝ 4 f t) (hg : ContDiffAt ℝ 4 g t) :
    iteratedDeriv 1 (fun u => f u * g u) t =
      iteratedDeriv 1 f t * g t + f t * iteratedDeriv 1 g t := by
  have h := hasDerivAt_jet hf 0 (by norm_num)
  have k := hasDerivAt_jet hg 0 (by norm_num)
  simpa only [Nat.reduceAdd, iteratedDeriv_one, iteratedDeriv_zero] using (h.fun_mul k).deriv

theorem product_second (hf : ContDiffAt ℝ 4 f t) (hg : ContDiffAt ℝ 4 g t) :
    iteratedDeriv 2 (fun u => f u * g u) t =
      iteratedDeriv 2 f t * g t + (2 : ℝ) • (iteratedDeriv 1 f t * iteratedDeriv 1 g t) +
        f t * iteratedDeriv 2 g t := by
  have he : iteratedDeriv 1 (fun u => f u * g u) =ᶠ[𝓝 t]
      (fun u => iteratedDeriv 1 f u * g u + f u * iteratedDeriv 1 g u) := by
    filter_upwards [hf.eventually (by norm_num), hg.eventually (by norm_num)] with u hu hv
    exact product_first hu hv
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, he.deriv_eq]
  have h0 := hasDerivAt_jet hf 0 (by norm_num)
  have h1 := hasDerivAt_jet hf 1 (by norm_num)
  have k0 := hasDerivAt_jet hg 0 (by norm_num)
  have k1 := hasDerivAt_jet hg 1 (by norm_num)
  simp only [iteratedDeriv_zero] at h0 k0
  rw [((h1.fun_mul k0).fun_add (h0.fun_mul k1)).deriv]
  module

theorem product_third (hf : ContDiffAt ℝ 4 f t) (hg : ContDiffAt ℝ 4 g t) :
    iteratedDeriv 3 (fun u => f u * g u) t =
      iteratedDeriv 3 f t * g t + (3 : ℝ) • (iteratedDeriv 2 f t * iteratedDeriv 1 g t) +
        (3 : ℝ) • (iteratedDeriv 1 f t * iteratedDeriv 2 g t) +
        f t * iteratedDeriv 3 g t := by
  have he : iteratedDeriv 2 (fun u => f u * g u) =ᶠ[𝓝 t]
      (fun u => iteratedDeriv 2 f u * g u +
        (2 : ℝ) • (iteratedDeriv 1 f u * iteratedDeriv 1 g u) +
        f u * iteratedDeriv 2 g u) := by
    filter_upwards [hf.eventually (by norm_num), hg.eventually (by norm_num)] with u hu hv
    exact product_second hu hv
  rw [show (3 : ℕ) = 2 + 1 from rfl, iteratedDeriv_succ, he.deriv_eq]
  have h0 := hasDerivAt_jet hf 0 (by norm_num)
  have h1 := hasDerivAt_jet hf 1 (by norm_num)
  have h2 := hasDerivAt_jet hf 2 (by norm_num)
  have k0 := hasDerivAt_jet hg 0 (by norm_num)
  have k1 := hasDerivAt_jet hg 1 (by norm_num)
  have k2 := hasDerivAt_jet hg 2 (by norm_num)
  simp only [iteratedDeriv_zero] at h0 k0
  rw [(((h2.fun_mul k0).fun_add ((h1.fun_mul k1).fun_const_smul (2 : ℝ))).fun_add
    (h0.fun_mul k2)).deriv]
  module

theorem product_fourth (hf : ContDiffAt ℝ 4 f t) (hg : ContDiffAt ℝ 4 g t) :
    iteratedDeriv 4 (fun u => f u * g u) t =
      iteratedDeriv 4 f t * g t + (4 : ℝ) • (iteratedDeriv 3 f t * iteratedDeriv 1 g t) +
        (6 : ℝ) • (iteratedDeriv 2 f t * iteratedDeriv 2 g t) +
        (4 : ℝ) • (iteratedDeriv 1 f t * iteratedDeriv 3 g t) +
        f t * iteratedDeriv 4 g t := by
  have he : iteratedDeriv 3 (fun u => f u * g u) =ᶠ[𝓝 t]
      (fun u => iteratedDeriv 3 f u * g u +
        (3 : ℝ) • (iteratedDeriv 2 f u * iteratedDeriv 1 g u) +
        (3 : ℝ) • (iteratedDeriv 1 f u * iteratedDeriv 2 g u) +
        f u * iteratedDeriv 3 g u) := by
    filter_upwards [hf.eventually (by norm_num), hg.eventually (by norm_num)] with u hu hv
    exact product_third hu hv
  conv_lhs => rw [show (4 : ℕ) = 3 + 1 from rfl, iteratedDeriv_succ]
  rw [he.deriv_eq]
  have h0 := hasDerivAt_jet hf 0 (by norm_num)
  have h1 := hasDerivAt_jet hf 1 (by norm_num)
  have h2 := hasDerivAt_jet hf 2 (by norm_num)
  have h3 := hasDerivAt_jet hf 3 (by norm_num)
  have k0 := hasDerivAt_jet hg 0 (by norm_num)
  have k1 := hasDerivAt_jet hg 1 (by norm_num)
  have k2 := hasDerivAt_jet hg 2 (by norm_num)
  have k3 := hasDerivAt_jet hg 3 (by norm_num)
  simp only [iteratedDeriv_zero] at h0 k0
  rw [((((h3.fun_mul k0).fun_add ((h2.fun_mul k1).fun_const_smul (3 : ℝ))).fun_add
    ((h1.fun_mul k2).fun_const_smul (3 : ℝ))).fun_add (h0.fun_mul k3)).deriv]
  module

lemma mul_norm_le {A B : Matrix n n ℂ} {a b : ℝ} (hA : ‖A‖ ≤ a) (hB : ‖B‖ ≤ b) :
    ‖A*B‖ ≤ a*b :=
  (norm_mul_le A B).trans (mul_le_mul hA hB (norm_nonneg _) ((norm_nonneg _).trans hA))

lemma add_norm_le {A B : Matrix n n ℂ} {a b : ℝ} (hA : ‖A‖ ≤ a) (hB : ‖B‖ ≤ b) :
    ‖A+B‖ ≤ a+b := (norm_add_le A B).trans (add_le_add hA hB)

lemma smul_norm_le {A : Matrix n n ℂ} {a c : ℝ} (hc : 0 ≤ c) (hA : ‖A‖ ≤ a) :
    ‖c • A‖ ≤ c*a := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
  exact mul_le_mul_of_nonneg_left hA hc

/-- Derivative bounds are preserved by multiplication, with addition of the
first-order scale. This is the noncommutative Leibniz estimate through order four. -/
theorem product_bounds (hf : ContDiffAt ℝ 4 f t) (hg : ContDiffAt ℝ 4 g t)
    {a b : ℝ} (hf0 : ‖f t‖ ≤ 1) (hg0 : ‖g t‖ ≤ 1)
    (hf1 : ‖iteratedDeriv 1 f t‖ ≤ a) (hg1 : ‖iteratedDeriv 1 g t‖ ≤ b)
    (hf2 : ‖iteratedDeriv 2 f t‖ ≤ a^2) (hg2 : ‖iteratedDeriv 2 g t‖ ≤ b^2)
    (hf3 : ‖iteratedDeriv 3 f t‖ ≤ a^3) (hg3 : ‖iteratedDeriv 3 g t‖ ≤ b^3)
    (hf4 : ‖iteratedDeriv 4 f t‖ ≤ a^4) (hg4 : ‖iteratedDeriv 4 g t‖ ≤ b^4) :
    ‖iteratedDeriv 1 (fun u => f u*g u) t‖ ≤ a+b ∧
    ‖iteratedDeriv 2 (fun u => f u*g u) t‖ ≤ (a+b)^2 ∧
    ‖iteratedDeriv 3 (fun u => f u*g u) t‖ ≤ (a+b)^3 ∧
    ‖iteratedDeriv 4 (fun u => f u*g u) t‖ ≤ (a+b)^4 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [product_first hf hg]
    have hh := add_norm_le (mul_norm_le hf1 hg0) (mul_norm_le hf0 hg1)
    simpa only [mul_one, one_mul] using hh
  · rw [product_second hf hg]
    have hh := add_norm_le
      (add_norm_le (mul_norm_le hf2 hg0) (smul_norm_le (by norm_num : (0:ℝ)≤2) (mul_norm_le hf1 hg1)))
      (mul_norm_le hf0 hg2)
    convert hh using 1; ring
  · rw [product_third hf hg]
    have hh := add_norm_le
      (add_norm_le
        (add_norm_le (mul_norm_le hf3 hg0) (smul_norm_le (by norm_num : (0:ℝ)≤3) (mul_norm_le hf2 hg1)))
        (smul_norm_le (by norm_num : (0:ℝ)≤3) (mul_norm_le hf1 hg2)))
      (mul_norm_le hf0 hg3)
    convert hh using 1; ring
  · rw [product_fourth hf hg]
    have hh := add_norm_le
      (add_norm_le
        (add_norm_le
          (add_norm_le (mul_norm_le hf4 hg0) (smul_norm_le (by norm_num : (0:ℝ)≤4) (mul_norm_le hf3 hg1)))
          (smul_norm_le (by norm_num : (0:ℝ)≤6) (mul_norm_le hf2 hg2)))
        (smul_norm_le (by norm_num : (0:ℝ)≤4) (mul_norm_le hf1 hg3)))
      (mul_norm_le hf0 hg4)
    convert hh using 1; ring

variable [Nonempty n]

/-- The actual power jets have polynomial dependence on the power k. -/
theorem power_bounds (hf : ContDiffAt ℝ 4 f t) {a : ℝ} (hf0 : ‖f t‖ ≤ 1)
    (hf1 : ‖iteratedDeriv 1 f t‖ ≤ a) (hf2 : ‖iteratedDeriv 2 f t‖ ≤ a^2)
    (hf3 : ‖iteratedDeriv 3 f t‖ ≤ a^3) (hf4 : ‖iteratedDeriv 4 f t‖ ≤ a^4) (k : ℕ) :
    ‖iteratedDeriv 1 (fun u => f u^k) t‖ ≤ (k:ℝ)*a ∧
    ‖iteratedDeriv 2 (fun u => f u^k) t‖ ≤ ((k:ℝ)*a)^2 ∧
    ‖iteratedDeriv 3 (fun u => f u^k) t‖ ≤ ((k:ℝ)*a)^3 ∧
    ‖iteratedDeriv 4 (fun u => f u^k) t‖ ≤ ((k:ℝ)*a)^4 := by
  induction k with
  | zero => simp [iteratedDeriv_succ, iteratedDeriv_zero]
  | succ k ih =>
    have h0 : ‖f t^k‖ ≤ 1 := (norm_pow_le _ _).trans (pow_le_one₀ (norm_nonneg _) hf0)
    have hh := product_bounds (hf.pow k) hf h0 hf0 ih.1 hf1 ih.2.1 hf2
      ih.2.2.1 hf3 ih.2.2.2 hf4
    simpa only [← pow_succ, Nat.cast_add, Nat.cast_one, add_mul, one_mul] using hh

/-- One common bound for derivative orders one through four. -/
theorem power_jet_norm_le (hf : ContDiffAt ℝ 4 f t) {a : ℝ} (ha : 1 ≤ a)
    (hf0 : ‖f t‖ ≤ 1)
    (hf1 : ‖iteratedDeriv 1 f t‖ ≤ a) (hf2 : ‖iteratedDeriv 2 f t‖ ≤ a^2)
    (hf3 : ‖iteratedDeriv 3 f t‖ ≤ a^3) (hf4 : ‖iteratedDeriv 4 f t‖ ≤ a^4)
    (k r : ℕ) (hr1 : 1 ≤ r) (hr4 : r ≤ 4) :
    ‖iteratedDeriv r (fun u => f u^k) t‖ ≤ ((k+1:ℕ):ℝ)^4*a^4 := by
  have ha0 : 0 ≤ a := by linarith
  have hpow := power_bounds hf hf0 hf1 hf2 hf3 hf4 k
  have hk0 : 0 ≤ (k:ℝ)*a := mul_nonneg (Nat.cast_nonneg _) ha0
  have hk1 : 1 ≤ ((k+1:ℕ):ℝ)*a := by
    apply one_le_mul_of_one_le_of_one_le
    · exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
    · exact ha
  have hkk : (k:ℝ)*a ≤ ((k+1:ℕ):ℝ)*a := by gcongr; omega
  have he : (((k+1:ℕ):ℝ)*a)^4 = ((k+1:ℕ):ℝ)^4*a^4 := mul_pow _ _ _
  have h12 : (k:ℝ)*a ≤ (((k+1:ℕ):ℝ)*a)^4 :=
    hkk.trans (by simpa only [pow_one] using pow_le_pow_right₀ hk1 (show 1≤4 by omega))
  have h24 : ((k:ℝ)*a)^2 ≤ (((k+1:ℕ):ℝ)*a)^4 :=
    (pow_le_pow_left₀ hk0 hkk 2).trans (pow_le_pow_right₀ hk1 (by omega))
  have h34 : ((k:ℝ)*a)^3 ≤ (((k+1:ℕ):ℝ)*a)^4 :=
    (pow_le_pow_left₀ hk0 hkk 3).trans (pow_le_pow_right₀ hk1 (by omega))
  have h44 : ((k:ℝ)*a)^4 ≤ (((k+1:ℕ):ℝ)*a)^4 := pow_le_pow_left₀ hk0 hkk 4
  interval_cases r
  · exact hpow.1.trans (h12.trans_eq he)
  · exact hpow.2.1.trans (h24.trans_eq he)
  · exact hpow.2.2.1.trans (h34.trans_eq he)
  · exact hpow.2.2.2.trans (h44.trans_eq he)

end MatrixSpencer.RectangularRidgePowerJetBounds
