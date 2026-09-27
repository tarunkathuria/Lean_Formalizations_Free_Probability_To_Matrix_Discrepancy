import AugmentedHigherRankKS.EpochZeroAtoms
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! One-sided first-order optimality for actual reserve preparation. -/
open Matrix MatrixSpencer Set Filter
open scoped BigOperators Topology MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace AugmentedHigherRankKS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def prepareOne (a : ℝ) (z : EpochState ι) (i : ι) (t : ℝ) : EpochState ι :=
  preparation a z (fun j => if j = i then t else 0)

@[simp] theorem prepareOne_zero (a : ℝ) (z : EpochState ι) (i : ι) :
    prepareOne a z i 0 = z := by
  rcases z with ⟨x, s, c⟩
  simp [prepareOne, preparation, position, spent, reserve]

theorem prepareOne_mem {a R : ℝ} (ha : 0 < a) {z : EpochState ι}
    (hz : z ∈ epochDomain a R) (i : ι) {t : ℝ} (ht : 0 ≤ t)
    (htc : t ≤ reserve z i) : prepareOne a z i t ∈ epochDomain a R := by
  apply preparation_mem ha hz
  intro j
  by_cases hji : j = i
  · subst j; simp only [if_pos rfl]; exact ⟨ht, htc⟩
  · simp only [if_neg hji]
    exact ⟨le_rfl, (hz j).2.2.2.2.1⟩

theorem derivative_nonneg_of_right_minimum {f : ℝ → ℝ} {d η : ℝ}
    (hη : 0 < η) (hd : HasDerivAt f d 0)
    (hmin : ∀ t, 0 ≤ t → t ≤ η → f 0 ≤ f t) : 0 ≤ d := by
  have hl := hd.tendsto_slope_zero_right
  apply ge_of_tendsto hl
  have hsmall : ∀ᶠ t : ℝ in 𝓝[>] 0, t < η :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (isOpen_Iio.mem_nhds hη)
  filter_upwards [self_mem_nhdsWithin, hsmall] with t ht hlt
  simp only [zero_add, smul_eq_mul]
  exact mul_nonneg (inv_nonneg.mpr (le_of_lt ht)) (sub_nonneg.mpr (hmin t ht.le hlt.le))

/-- At a compact minimum the derivative of a positive-reserve preparation
curve is nonnegative. The derivative value itself is computed analytically. -/
theorem preparation_derivative_nonneg {a R : ℝ} (ha : 0 < a)
    (F : EpochState ι → ℝ) {z : EpochState ι} (hz : z ∈ epochDomain a R)
    (hmin : IsMinOn F (epochDomain a R) z) (i : ι)
    (hci : 0 < reserve z i) {d : ℝ}
    (hd : HasDerivAt (fun t => F (prepareOne a z i t)) d 0) : 0 ≤ d := by
  apply derivative_nonneg_of_right_minimum hci hd
  intro t ht htc
  simpa only [prepareOne_zero] using hmin (prepareOne_mem ha hz i ht htc)

/-- The first-order reserve inequality gives the concrete response cap. -/
theorem preparation_response_cap {a R c p τ m : ℝ}
    (ha : 0 < a) (hc : 0 ≤ c) (hcR : c ≤ a * R)
    (hp : 0 < p) (hτ : 0 ≤ τ) (hmp : m ≤ p)
    (hderiv : 0 ≤ m / a - τ) : c * (τ / p) ^ 2 ≤ R / a := by
  have hτp : τ ≤ p / a := by
    have hm : m / a ≤ p / a := (div_le_div_iff_of_pos_right ha).mpr hmp
    linarith
  have hq : τ / p ≤ 1 / a := by
    apply (div_le_iff₀ hp).mpr
    simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one] using hτp
  have hq0 : 0 ≤ τ / p := div_nonneg hτ hp.le
  have hq2 : (τ / p)^2 ≤ (1 / a)^2 :=
    pow_le_pow_left₀ hq0 hq 2
  calc
    c * (τ / p)^2 ≤ c * (1 / a)^2 := mul_le_mul_of_nonneg_left hq2 hc
    _ ≤ (a * R) * (1 / a)^2 := mul_le_mul_of_nonneg_right hcR (sq_nonneg _)
    _ = R / a := by field_simp

end AugmentedHigherRankKS
