import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! Exact scalar inverse-curvature kernels for reciprocal integer powers.
Writing a=x^p and b=y^p converts the inverse divided difference of s↦s^(-1/p)
to a finite polynomial. These identities do not assume any matrix calculus. -/

open scoped BigOperators
noncomputable section
namespace MatrixSpencer
namespace ReciprocalPowerKernel

def kernel (p : ℕ) (x y : ℝ) : ℝ :=
  x * y * ∑ j ∈ Finset.range p, x ^ j * y ^ (p - 1 - j)

lemma kernel_eq_sum (p : ℕ) (x y : ℝ) :
    kernel p x y = ∑ j ∈ Finset.range p, x ^ (j + 1) * y ^ (p - j) := by
  unfold kernel
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjp : j < p := Finset.mem_range.mp hj
  have he : p - j = (p - 1 - j) + 1 := by omega
  rw [he, pow_succ, pow_succ]
  ring

lemma kernel_symm (p : ℕ) (x y : ℝ) : kernel p x y = kernel p y x := by
  unfold kernel
  rw [geom_sum₂_comm x y p]
  ring

/-- Multiplying by the root difference gives the original power difference. -/
lemma difference_mul_kernel (p : ℕ) (x y : ℝ) :
    (x - y) * kernel p x y = x * y * (x ^ p - y ^ p) := by
  unfold kernel
  calc
    _ = x * y * ((∑ j ∈ Finset.range p, x ^ j * y ^ (p - 1 - j)) * (x - y)) := by ring
    _ = _ := by rw [geom_sum₂_mul]

lemma kernel_diagonal {p : ℕ} (hp : 0 < p) (x : ℝ) :
    kernel p x x = (p : ℝ) * x ^ (p + 1) := by
  unfold kernel
  rw [geom_sum₂_self]
  have he : p + 1 = (p - 1) + 1 + 1 := by omega
  rw [he, pow_succ, pow_succ]
  ring

lemma kernel_nonneg (p : ℕ) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ kernel p x y := by
  unfold kernel
  exact mul_nonneg (mul_nonneg hx hy)
    (Finset.sum_nonneg (fun j _ => mul_nonneg (pow_nonneg hx _) (pow_nonneg hy _)))

lemma kernel_pos {p : ℕ} (hp : 0 < p) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    0 < kernel p x y := by
  unfold kernel
  apply mul_pos (mul_pos hx hy)
  exact Finset.sum_pos (fun j _ => mul_pos (pow_pos hx _) (pow_pos hy _))
    (Finset.nonempty_range_iff.mpr hp.ne')

/-- Pairing complementary powers bounds them by the two endpoint powers. -/
lemma complementary_powers_le {m j : ℕ} (hj : j ≤ m) {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x ^ j * y ^ (m - j) + x ^ (m - j) * y ^ j ≤ x ^ m + y ^ m := by
  have he : j + (m - j) = m := by omega
  have hex : x ^ j * x ^ (m - j) = x ^ m := by rw [← pow_add, he]
  have hey : y ^ j * y ^ (m - j) = y ^ m := by rw [← pow_add, he]
  rcases le_total x y with hxy | hyx
  · have h1 := pow_le_pow_left₀ hx hxy j
    have h2 := pow_le_pow_left₀ hx hxy (m - j)
    have hprod := mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2)
    nlinarith
  · have h1 := pow_le_pow_left₀ hy hyx j
    have h2 := pow_le_pow_left₀ hy hyx (m - j)
    have hprod := mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2)
    nlinarith

lemma twice_geometric_sum_le (p : ℕ) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    2 * (∑ j ∈ Finset.range p, x ^ j * y ^ (p - 1 - j)) ≤
      (p : ℝ) * (x ^ (p - 1) + y ^ (p - 1)) := by
  have hsum := Finset.sum_le_sum (s := Finset.range p) (fun j hj =>
    complementary_powers_le (show j ≤ p - 1 from by have := Finset.mem_range.mp hj; omega) hx hy)
  have hrev : (∑ j ∈ Finset.range p, x ^ (p - 1 - j) * y ^ j) =
      ∑ j ∈ Finset.range p, x ^ j * y ^ (p - 1 - j) := by
    calc
      _ = ∑ j ∈ Finset.range p, y ^ j * x ^ (p - 1 - j) := by
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := geom_sum₂_comm y x p
  simp only [Finset.sum_add_distrib, hrev, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul] at hsum
  linarith

/-- The exact reciprocal-power inverse kernel is bounded by its two endpoint products. -/
theorem kernel_le_endpoint_products {p : ℕ} (hp : 0 < p) {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    kernel p x y ≤ (p : ℝ) / 2 * (x ^ p * y + x * y ^ p) := by
  have hsum := mul_le_mul_of_nonneg_left (twice_geometric_sum_le p hx hy) (mul_nonneg hx hy)
  have he : p = (p - 1) + 1 := by omega
  have hex : x * x ^ (p - 1) = x ^ p := by
    calc
      _ = x ^ ((p - 1) + 1) := by rw [pow_succ]; ring
      _ = _ := by rw [← he]
  have hey : y * y ^ (p - 1) = y ^ p := by
    calc
      _ = y ^ ((p - 1) + 1) := by rw [pow_succ]; ring
      _ = _ := by rw [← he]
  have hrhs : x * y * ((p : ℝ) * (x ^ (p - 1) + y ^ (p - 1))) =
      (p : ℝ) * (x ^ p * y + x * y ^ p) := by
    calc
      _ = (p : ℝ) * ((x * x ^ (p - 1)) * y + x * (y * y ^ (p - 1))) := by ring
      _ = _ := by rw [hex, hey]
  rw [hrhs] at hsum
  unfold kernel
  nlinarith

/-- The polynomial equals the inverse divided difference away from equal roots. -/
theorem kernel_eq_inverse_difference {p : ℕ} {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hxy : x ≠ y) :
    kernel p x y = (x ^ p - y ^ p) / (y⁻¹ - x⁻¹) := by
  have hd : y⁻¹ - x⁻¹ ≠ 0 := sub_ne_zero.mpr (by
    intro he
    exact hxy (inv_injective he).symm)
  apply (eq_div_iff hd).mpr
  have h := difference_mul_kernel p x y
  field_simp
  nlinarith

/-- The inverse scalar multiplier in the original positive eigenvalue variables. -/
def inverseKernel (p : ℕ) (a b : ℝ) : ℝ :=
  kernel p (a ^ (p : ℝ)⁻¹) (b ^ (p : ℝ)⁻¹)

lemma root_nat_power (p j : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    (a ^ (p : ℝ)⁻¹) ^ j = a ^ ((j : ℝ) / p) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul ha]
  congr 1
  simp only [div_eq_mul_inv, mul_comm]

/-- Exactly p positive-product terms, including both endpoint powers. -/
lemma inverseKernel_eq_sum (p : ℕ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    inverseKernel p a b = ∑ j ∈ Finset.range p,
      a ^ (((j + 1 : ℕ) : ℝ) / p) * b ^ (((p - j : ℕ) : ℝ) / p) := by
  unfold inverseKernel
  rw [kernel_eq_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [root_nat_power p (j + 1) ha, root_nat_power p (p - j) hb]

lemma inverseKernel_pos {p : ℕ} (hp : 0 < p) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 < inverseKernel p a b :=
  kernel_pos hp (Real.rpow_pos_of_pos ha _) (Real.rpow_pos_of_pos hb _)

lemma inverseKernel_symm (p : ℕ) (a b : ℝ) : inverseKernel p a b = inverseKernel p b a :=
  kernel_symm p _ _

/-- The diagonal value is the reciprocal of q*a^(-1-q), for q=1/p. -/
lemma inverseKernel_diagonal {p : ℕ} (hp : 0 < p) {a : ℝ} (ha : 0 ≤ a) :
    inverseKernel p a a = (p : ℝ) * a ^ (1 + (p : ℝ)⁻¹) := by
  unfold inverseKernel
  rw [kernel_diagonal hp, root_nat_power p (p + 1) ha]
  congr 2
  have hpR : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
  push_cast
  field_simp

/-- Off the diagonal this is exactly the inverse divided difference of s^(-1/p). -/
theorem inverseKernel_eq_divided_difference {p : ℕ} (hp : 0 < p)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    inverseKernel p a b = (a - b) / (b ^ (-(p : ℝ)⁻¹) - a ^ (-(p : ℝ)⁻¹)) := by
  have hroot : a ^ (p : ℝ)⁻¹ ≠ b ^ (p : ℝ)⁻¹ := by
    intro he
    apply hab
    have h := congrArg (fun z : ℝ => z ^ p) he
    simpa only [Real.rpow_inv_natCast_pow ha.le hp.ne', Real.rpow_inv_natCast_pow hb.le hp.ne'] using h
  unfold inverseKernel
  rw [kernel_eq_inverse_difference (Real.rpow_pos_of_pos ha _) (Real.rpow_pos_of_pos hb _) hroot,
    Real.rpow_inv_natCast_pow ha.le hp.ne', Real.rpow_inv_natCast_pow hb.le hp.ne',
    Real.rpow_neg ha.le, Real.rpow_neg hb.le]

/-- The scalar bound needed for the positive-superoperator inverse-curvature comparison. -/
theorem inverseKernel_le_endpoint_products {p : ℕ} (hp : 0 < p)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    inverseKernel p a b ≤ (p : ℝ) / 2 *
      (a * b ^ (p : ℝ)⁻¹ + a ^ (p : ℝ)⁻¹ * b) := by
  have h := kernel_le_endpoint_products hp
    (Real.rpow_nonneg ha (p : ℝ)⁻¹) (Real.rpow_nonneg hb (p : ℝ)⁻¹)
  simpa only [inverseKernel, Real.rpow_inv_natCast_pow ha hp.ne',
    Real.rpow_inv_natCast_pow hb hp.ne'] using h

end ReciprocalPowerKernel
end MatrixSpencer
