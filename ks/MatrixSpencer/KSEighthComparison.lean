import MatrixSpencer.KSEighthInertia
import MatrixSpencer.KSFisher

/-!
# The finite mixed-term comparison for the eighth-cube proof

The arguments retain the physical Fisher weights. In particular, the diagonal
weight is not commuted with the Gram. The constants below use the exact
no-retirement bounds at a=1/8 and u=64.
-/

open Matrix
open scoped BigOperators MatrixOrder

noncomputable section
namespace MatrixSpencer.KSEighthComparison

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Weighted Young inequality in the precise normalization of the remaining
mixed source term. -/
theorem mixed_scalar_bound {r m e t y α η : ℝ} (hr : 0 < r)
    (hm : 0 ≤ m) (hη : 0 < η) (he : e ^ 2 ≤ α) :
    -2 * m * e * t * y ≤ (α / η) * (m / r) * t ^ 2 + η * r * m * y ^ 2 := by
  have hcore : -2 * e * t * y ≤ (α / η) / r * t ^ 2 + η * r * y ^ 2 := by
    apply (mul_le_mul_iff_of_pos_right (mul_pos hη hr)).mp
    have heq : ((α / η) / r * t ^ 2 + η * r * y ^ 2) * (η * r) =
        α * t ^ 2 + η ^ 2 * r ^ 2 * y ^ 2 := by
      field_simp [hη.ne', hr.ne']
      <;> ring
    rw [heq]
    have hnon := mul_nonneg (sub_nonneg.mpr he) (sq_nonneg t)
    nlinarith [sq_nonneg (e * t + η * r * y)]
  have hh := mul_le_mul_of_nonneg_left hcore hm
  convert hh using 1 <;> ring

/-- A diagonal Fisher inequality also bounds the diagonal energy of Tξ.
This is the noncommutative TGT≤τΓ implication, stated on vectors. -/
theorem weighted_fisher_transfer (r m t : ι → ℝ) {τ q : ℝ}
    (hr : ∀ i, 0 < r i) (hm : ∀ i, 0 ≤ m i) (hτ : 0 ≤ τ)
    (hrτ : ∀ i, r i ^ 2 ≤ τ)
    (hfisher : (∑ i, (m i / r i) * t i ^ 2) ≤ q) :
    (∑ i, r i * m i * t i ^ 2) ≤ τ * q := by
  calc
    _ ≤ ∑ i, τ * ((m i / r i) * t i ^ 2) := by
      apply Finset.sum_le_sum
      intro i _
      have hh := mul_le_mul_of_nonneg_right (hrτ i)
        (mul_nonneg (div_nonneg (hm i) (hr i).le) (sq_nonneg (t i)))
      convert hh using 1 <;> field_simp [(hr i).ne'] <;> ring
    _ = τ * ∑ i, (m i / r i) * t i ^ 2 := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hfisher hτ

/-- The mixed source term is bounded using the actual Fisher inequality. -/
theorem mixed_sum_bound (r m e t y : ι → ℝ) {α η q : ℝ}
    (hr : ∀ i, 0 < r i) (hm : ∀ i, 0 ≤ m i) (hα : 0 ≤ α)
    (hη : 0 < η) (he : ∀ i, e i ^ 2 ≤ α)
    (hfisher : (∑ i, (m i / r i) * t i ^ 2) ≤ q) :
    (∑ i, -2 * m i * e i * t i * y i) ≤
      (α / η) * q + η * ∑ i, r i * m i * y i ^ 2 := by
  calc
    _ ≤ ∑ i, ((α / η) * ((m i / r i) * t i ^ 2) +
        η * (r i * m i * y i ^ 2)) := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [mul_assoc] using mixed_scalar_bound (hr i) (hm i) hη (he i)
    _ = (α / η) * ∑ i, (m i / r i) * t i ^ 2 +
        η * ∑ i, r i * m i * y i ^ 2 := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ _ := add_le_add_right
      (mul_le_mul_of_nonneg_left hfisher (div_nonneg hα hη.le)) _

/-- The defect estimate uses scalar squares coordinate by coordinate, so it
requires no commutation between the Gram and the diagonal weight. -/
theorem weighted_defect_lower (g ξ t : ι → ℝ) (hg : ∀ i, 0 ≤ g i) :
    (1 / 2 : ℝ) * ∑ i, g i * ξ i ^ 2 - ∑ i, g i * t i ^ 2 ≤
      ∑ i, g i * (ξ i - t i) ^ 2 := by
  calc
    _ = ∑ i, g i * ((1 / 2 : ℝ) * ξ i ^ 2 - t i ^ 2) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (hg i)
      nlinarith [sq_nonneg (ξ i - 2 * t i)]

/-- The diagonal force bound transfers the defect lower bound to a legal
coefficient direction y. No inverse of I−T is used. -/
theorem legal_weight_lower (g ξ t y b : ι → ℝ) {B : ℝ}
    (hg : ∀ i, 0 ≤ g i) (hb : ∀ i, b i ^ 2 ≤ B ^ 2)
    (hlegal : ∀ i, b i * y i = ξ i - t i) :
    (1 / 2 : ℝ) * ∑ i, g i * ξ i ^ 2 - ∑ i, g i * t i ^ 2 ≤
      B ^ 2 * ∑ i, g i * y i ^ 2 := by
  apply (weighted_defect_lower g ξ t hg).trans
  calc
    _ = ∑ i, b i ^ 2 * (g i * y i ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← hlegal]
      ring
    _ ≤ ∑ i, B ^ 2 * (g i * y i ^ 2) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right (hb i) (mul_nonneg (hg i) (sq_nonneg _))
    _ = _ := (Finset.mul_sum _ _ _).symm

def comparisonA : ℝ := 1 / 64 + 1 / 2016 + (3969 / 4489) / 2016

def comparisonB : ℝ := (3969 / 4489) / 4

theorem comparisonA_pos : 0 < comparisonA := by norm_num [comparisonA]
theorem comparisonB_pos : 0 < comparisonB := by norm_num [comparisonB]
theorem comparison_ratio : comparisonA / comparisonB < 3 / 32 := by
  norm_num [comparisonA, comparisonB]

/-- Exact one-sign bound for half of the explicit moving-transport majorant
acceleration, with all eighth-cube constants already discharged. -/
theorem completion_bound (r m e ξ t y b : ι → ℝ) {q : ℝ}
    (hr : ∀ i, 0 < r i) (hm : ∀ i, 0 ≤ m i)
    (he : ∀ i, e i ^ 2 ≤ (1 / 4032 : ℝ))
    (hrτ : ∀ i, r i ^ 2 ≤ (1 / 1008 : ℝ))
    (hfisher : (∑ i, (m i / r i) * t i ^ 2) ≤ q)
    (hb : ∀ i, b i ^ 2 ≤ (67 / 63 : ℝ) ^ 2)
    (hlegal : ∀ i, b i * y i = ξ i - t i) :
    q / 64 + (∑ i, -2 * m i * e i * t i * y i) -
        (∑ i, r i * m i * y i ^ 2) ≤
      comparisonA * q - comparisonB * ∑ i, r i * m i * ξ i ^ 2 := by
  have hmix := mixed_sum_bound r m e t y hr hm (by norm_num : (0:ℝ) ≤ 1/4032)
    (by norm_num : (0:ℝ) < 1/2) he hfisher
  have hf := weighted_fisher_transfer r m t hr hm (by norm_num : (0:ℝ) ≤ 1/1008) hrτ hfisher
  have hl := legal_weight_lower (fun i => r i * m i) ξ t y b
    (fun i => mul_nonneg (hr i).le (hm i)) hb hlegal
  dsimp only [comparisonA, comparisonB]
  norm_num at hmix hl ⊢
  nlinarith

/-- The eighth cube keeps every natural owner uniformly positive. -/
theorem eighth_square_bound {x : ℝ} (hx : |x| ≤ (1 / 8 : ℝ)) :
    x ^ 2 ≤ (1 / 64 : ℝ) := by
  rcases abs_le.mp hx with ⟨hl, hu⟩
  nlinarith [mul_nonneg (sub_nonneg.mpr hu) (sub_nonneg.mpr hl)]

theorem eighth_owner_lower {x : ℝ} (hx : |x| ≤ (1 / 8 : ℝ)) :
    63 ≤ 64 * (1 - x ^ 2) := by
  nlinarith [eighth_square_bound hx]

/-- The no-safe inequality bounds the actual transport probe and balanced
atom trace; this retains the owner in the squared-trace estimate. -/
theorem no_safe_probe_bounds {x q σ : ℝ}
    (hx : |x| ≤ (1 / 8 : ℝ)) (hq : 0 ≤ q) (hσ : σ = -1 ∨ σ = 1)
    (hns : 64 * (1 - x ^ 2) * q < 1 / 8 - σ * x) :
    q < (1 / 252 : ℝ) ∧ 64 * (1 - x ^ 2) * q ^ 2 ≤ (1 / 1008 : ℝ) := by
  have hx' := abs_le.mp hx
  have hcx : 63 ≤ 64 * (1 - x ^ 2) := eighth_owner_lower hx
  have hupper : 1 / 8 - σ * x ≤ (1 / 4 : ℝ) := by
    rcases hσ with rfl | rfl <;> linarith [hx'.1, hx'.2]
  have hcq : 64 * (1 - x ^ 2) * q < (1 / 4 : ℝ) := hns.trans_le hupper
  have hqq := mul_le_mul_of_nonneg_right hcx hq
  have hqb : q < (1 / 252 : ℝ) := by nlinarith
  refine ⟨hqb, ?_⟩
  have hh := mul_le_mul_of_nonneg_right hcq.le hq
  nlinarith

/-- Both sign forces stay uniformly away from zero on a no-safe state. -/
theorem no_safe_force_bounds {x q σ : ℝ}
    (hx : |x| ≤ (1 / 8 : ℝ)) (hq : 0 ≤ q) (hσ : σ = -1 ∨ σ = 1)
    (hns : 64 * (1 - x ^ 2) * q < 1 / 8 - σ * x) :
    (σ - 128 * x * q) ≠ 0 ∧
      (σ - 128 * x * q) ^ 2 ≤ (67 / 63 : ℝ) ^ 2 := by
  have hqbound := (no_safe_probe_bounds hx hq hσ hns).1
  have hprod : |128 * x * q| ≤ (4 / 63 : ℝ) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 128), abs_of_nonneg hq]
    have hh := mul_le_mul_of_nonneg_right hx hq
    nlinarith
  have hσabs : |σ| = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hbabs : |σ - 128 * x * q| ≤ (67 / 63 : ℝ) := by
    calc
      _ ≤ |σ| + |128 * x * q| := by simpa using (abs_sub_le σ 0 (128 * x * q))
      _ ≤ _ := by rw [hσabs]; linarith
  constructor
  · intro hz
    have he : σ = 128 * x * q := sub_eq_zero.mp hz
    rw [← he, hσabs] at hprod
    norm_num at hprod
  · rcases abs_le.mp hbabs with ⟨hl, hu⟩
    nlinarith [mul_nonneg (sub_nonneg.mpr hu) (sub_nonneg.mpr hl)]

/-- The normalized mixed coefficient has the exact alpha=1/4032 bound. -/
theorem eighth_mixed_coefficient_bound {x : ℝ} (hx : |x| ≤ (1 / 8 : ℝ)) :
    (x / (8 * Real.sqrt (1 - x ^ 2))) ^ 2 ≤ (1 / 4032 : ℝ) := by
  have hx2 := eighth_square_bound hx
  have hd : 0 < 1 - x ^ 2 := by nlinarith
  have hs := Real.sq_sqrt hd.le
  have hsn : Real.sqrt (1 - x ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hd).ne'
  apply (mul_le_mul_iff_of_pos_right (show 0 < 64 * (1 - x ^ 2) from by positivity)).mp
  have he : (x / (8 * Real.sqrt (1 - x ^ 2))) ^ 2 *
      (64 * (1 - x ^ 2)) = x ^ 2 := by
    calc
      _ = x ^ 2 / (64 * Real.sqrt (1 - x ^ 2) ^ 2) * (64 * (1 - x ^ 2)) := by ring
      _ = _ := by rw [hs]; field_simp [hd.ne']
  rw [he]
  nlinarith

end MatrixSpencer.KSEighthComparison
