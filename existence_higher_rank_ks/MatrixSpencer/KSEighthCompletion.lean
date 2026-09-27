import MatrixSpencer.KSEighthComparison

/-!
# Simultaneous strict transport completions for the eighth-cube route

The inputs are the physical Fisher matrices of one sign block. The proof
constructs the legal map without inverting I−T and intersects the images of
large negative subspaces. The result supplies separate transport completions
for the same nonzero coefficient direction.
-/

open Matrix Module
open scoped BigOperators MatrixOrder
noncomputable section
namespace MatrixSpencer.KSEighthCompletion
open KSEighthComparison KSEighthInertia

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Concrete finite data extracted from one actual balanced sign block. -/
structure Data (ι : Type*) [Fintype ι] [DecidableEq ι] where
  Γ : Matrix ι ι ℝ
  T : Matrix ι ι ℝ
  r : ι → ℝ
  m : ι → ℝ
  e : ι → ℝ
  b : ι → ℝ
  Γ_posSemidef : Γ.PosSemidef
  T_isHermitian : T.IsHermitian
  r_pos : ∀ i, 0 < r i
  m_pos : ∀ i, 0 < m i
  diagonal_eq : ∀ i, Γ i i = r i * m i
  fisher : T * Matrix.diagonal (fun i => m i / r i) * T ≤ Γ
  mixed_bound : ∀ i, e i ^ 2 ≤ (1 / 4032 : ℝ)
  trace_bound : ∀ i, r i ^ 2 ≤ (1 / 1008 : ℝ)
  force_bound : ∀ i, b i ^ 2 ≤ (67 / 63 : ℝ) ^ 2
  force_ne_zero : ∀ i, b i ≠ 0

namespace Data

def weight (d : Data ι) (i : ι) : ℝ := d.r i * d.m i

def completion (d : Data ι) : Matrix ι ι ℝ :=
  Matrix.diagonal (fun i => (d.b i)⁻¹) * (1 - d.T)

def comparison (d : Data ι) : Matrix ι ι ℝ :=
  comparisonA • d.Γ - comparisonB • Matrix.diagonal d.weight

/-- Half of the physical center acceleration after the legal completion. -/
def energy (d : Data ι) (ξ : ι → ℝ) : ℝ :=
  (ξ ⬝ᵥ (d.Γ *ᵥ ξ)) / 64 +
    (∑ i, -2 * d.m i * d.e i * (d.T *ᵥ ξ) i * (d.completion *ᵥ ξ) i) -
    ∑ i, d.r i * d.m i * (d.completion *ᵥ ξ) i ^ 2

theorem completion_legal (d : Data ι) (ξ : ι → ℝ) (i : ι) :
    d.b i * (d.completion *ᵥ ξ) i = ξ i - (d.T *ᵥ ξ) i := by
  simp only [completion, ← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal,
    Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply]
  rw [← mul_assoc, mul_inv_cancel₀ (d.force_ne_zero i), one_mul]

theorem fisher_quadratic (d : Data ι) (ξ : ι → ℝ) :
    (∑ i, (d.m i / d.r i) * (d.T *ᵥ ξ) i ^ 2) ≤ ξ ⬝ᵥ (d.Γ *ᵥ ξ) := by
  have ht : d.Tᵀ = d.T := by simpa only [Matrix.conjTranspose] using d.T_isHermitian.eq
  have hf := (Matrix.le_iff.mp d.fisher).2 ξ
  simp only [star_trivial, Matrix.sub_mulVec, dotProduct_sub, sub_nonneg] at hf
  have he := KSFisher.diagonal_sandwich_quadratic d.T (fun i => d.m i / d.r i) ξ
  rw [ht] at he
  rwa [he] at hf

theorem comparison_quadratic (d : Data ι) (ξ : ι → ℝ) :
    ξ ⬝ᵥ (d.comparison *ᵥ ξ) = comparisonA * (ξ ⬝ᵥ (d.Γ *ᵥ ξ)) -
      comparisonB * ∑ i, d.r i * d.m i * ξ i ^ 2 := by
  simp only [comparison, Matrix.sub_mulVec, Matrix.smul_mulVec,
    dotProduct_sub, dotProduct_smul, smul_eq_mul, Matrix.mulVec_diagonal]
  congr 1
  congr 1
  simp only [dotProduct, weight]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Matrix.mulVec_diagonal, weight]
  ring

/-- The actual Fisher and no-safe estimates imply the finite comparison. -/
theorem energy_le_comparison (d : Data ι) (ξ : ι → ℝ) :
    d.energy ξ ≤ ξ ⬝ᵥ (d.comparison *ᵥ ξ) := by
  rw [comparison_quadratic]
  exact completion_bound d.r d.m d.e ξ (d.T *ᵥ ξ) (d.completion *ᵥ ξ) d.b
    d.r_pos (fun i => (d.m_pos i).le) d.mixed_bound d.trace_bound
    (d.fisher_quadratic ξ) d.force_bound (d.completion_legal ξ)

/-- A zero coefficient direction has nonnegative transport-only energy. -/
theorem energy_nonneg_of_completion_zero (d : Data ι) (ξ : ι → ℝ)
    (hzero : d.completion *ᵥ ξ = 0) : 0 ≤ d.energy ξ := by
  have hq := d.Γ_posSemidef.2 ξ
  simp only [star_trivial] at hq
  simp only [energy, hzero, Pi.zero_apply, mul_zero, zero_pow (by decide : 2 ≠ 0),
    Finset.sum_const_zero, add_zero, sub_zero]
  exact div_nonneg hq (by norm_num)

/-- The completion is injective on every negative comparison subspace,
even though its ambient kernel can be nontrivial. -/
theorem completion_injective (d : Data ι) (U : Submodule ℝ (ι → ℝ))
    (hU : StrictlyNegativeOn d.comparison U) :
    Function.Injective (d.completion.mulVecLin.domRestrict U) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  by_contra hne
  have hne' : (x : ι → ℝ) ≠ 0 := fun h => hne (Subtype.ext h)
  change d.completion *ᵥ (x : ι → ℝ) = 0 at hx
  have hn := hU x x.property hne'
  have hc := d.energy_le_comparison x
  have hp := d.energy_nonneg_of_completion_zero x hx
  linarith

theorem completion_image_dimension (d : Data ι) (U : Submodule ℝ (ι → ℝ))
    (hU : StrictlyNegativeOn d.comparison U) :
    finrank ℝ (U.map d.completion.mulVecLin) = finrank ℝ U := by
  have h := LinearMap.finrank_range_of_inj (d.completion_injective U hU)
  rwa [LinearMap.range_domRestrict] at h

end Data

/-- The two actual sign blocks admit strict completions of a common nonzero
coefficient direction. This is the direct majorant counterpart of the
13k/16 common-Hessian inertia argument. -/
theorem exists_common_negative_completions [Nonempty ι] (d₁ d₂ : Data ι) :
    ∃ (y ξ₁ ξ₂ : ι → ℝ), y ≠ 0 ∧
      d₁.completion *ᵥ ξ₁ = y ∧ d₂.completion *ᵥ ξ₂ = y ∧
      d₁.energy ξ₁ < 0 ∧ d₂.energy ξ₂ < 0 := by
  obtain ⟨U₁, hdim₁, hneg₁⟩ := exists_large_negative_comparison d₁.Γ_posSemidef
    d₁.weight (fun i => mul_pos (d₁.r_pos i) (d₁.m_pos i)) d₁.diagonal_eq
    comparisonA_pos comparisonB_pos
  obtain ⟨U₂, hdim₂, hneg₂⟩ := exists_large_negative_comparison d₂.Γ_posSemidef
    d₂.weight (fun i => mul_pos (d₂.r_pos i) (d₂.m_pos i)) d₂.diagonal_eq
    comparisonA_pos comparisonB_pos
  change StrictlyNegativeOn d₁.comparison U₁ at hneg₁
  change StrictlyNegativeOn d₂.comparison U₂ at hneg₂
  let V₁ := U₁.map d₁.completion.mulVecLin
  let V₂ := U₂.map d₂.completion.mulVecLin
  have hi₁ : finrank ℝ V₁ = finrank ℝ U₁ := d₁.completion_image_dimension U₁ hneg₁
  have hi₂ : finrank ℝ V₂ = finrank ℝ U₂ := d₂.completion_image_dimension U₂ hneg₂
  have hdim : (finrank ℝ U₁ : ℝ) + finrank ℝ U₂ ≤
      (finrank ℝ ↥(V₁ ⊓ V₂) : ℝ) + Fintype.card ι := by
    have he := Submodule.finrank_sup_add_finrank_inf_eq V₁ V₂
    have hs := (V₁ ⊔ V₂).finrank_le
    simp only [Module.finrank_pi] at hs
    rw [← hi₁, ← hi₂]
    exact_mod_cast (by omega : finrank ℝ V₁ + finrank ℝ V₂ ≤
      finrank ℝ ↥(V₁ ⊓ V₂) + Fintype.card ι)
  have hk : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hratio := mul_lt_mul_of_pos_right comparison_ratio hk
  have hdpos : 0 < finrank ℝ ↥(V₁ ⊓ V₂) := by
    have hh : (0 : ℝ) < finrank ℝ ↥(V₁ ⊓ V₂) := by nlinarith
    exact_mod_cast hh
  have hne : V₁ ⊓ V₂ ≠ ⊥ := by
    intro he
    have hz := Submodule.finrank_eq_zero.mpr he
    omega
  obtain ⟨y, hy, hyne⟩ := (Submodule.ne_bot_iff (V₁ ⊓ V₂)).mp hne
  rcases hy.1 with ⟨ξ₁, hξ₁, he₁⟩
  rcases hy.2 with ⟨ξ₂, hξ₂, he₂⟩
  have hx₁ : ξ₁ ≠ 0 := by intro h; apply hyne; rw [← he₁, h]; simp
  have hx₂ : ξ₂ ≠ 0 := by intro h; apply hyne; rw [← he₂, h]; simp
  refine ⟨y, ξ₁, ξ₂, hyne, he₁, he₂, ?_, ?_⟩
  · exact (d₁.energy_le_comparison ξ₁).trans_lt (hneg₁ ξ₁ hξ₁ hx₁)
  · exact (d₂.energy_le_comparison ξ₂).trans_lt (hneg₂ ξ₂ hξ₂ hx₂)

end MatrixSpencer.KSEighthCompletion
