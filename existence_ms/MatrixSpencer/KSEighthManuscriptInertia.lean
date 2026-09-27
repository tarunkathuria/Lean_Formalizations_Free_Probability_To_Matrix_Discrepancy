import MatrixSpencer.KSEighthManuscriptContact



open Matrix Module Filter Topology
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
noncomputable section
namespace MatrixSpencer.KSEighthManuscriptInertia
open KSEighthComparison KSEighthInertia KSEighthCompletion

variable {ι n : Type*} [Fintype ι] [DecidableEq ι]

/-- The completion images intersect in more than thirteen sixteenths of all
coefficient directions, and every nonzero vector admits both negative lifts. -/
theorem exists_large_common_negative_completions [Nonempty ι] (d₁ d₂ : Data ι) :
    ∃ W : Submodule ℝ (ι → ℝ),
      (13 / 16 : ℝ) * Fintype.card ι < (finrank ℝ W : ℝ) ∧
      ∀ y ∈ W, y ≠ 0 → ∃ ξ₁ ξ₂ : ι → ℝ,
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
  refine ⟨V₁ ⊓ V₂, by nlinarith, ?_⟩
  intro y hy hyne
  rcases hy.1 with ⟨ξ₁, hξ₁, he₁⟩
  rcases hy.2 with ⟨ξ₂, hξ₂, he₂⟩
  have hx₁ : ξ₁ ≠ 0 := by intro h; apply hyne; rw [← he₁, h]; simp
  have hx₂ : ξ₂ ≠ 0 := by intro h; apply hyne; rw [← he₂, h]; simp
  exact ⟨ξ₁, ξ₂, he₁, he₂,
    (d₁.energy_le_comparison ξ₁).trans_lt (hneg₁ ξ₁ hξ₁ hx₁),
    (d₂.energy_le_comparison ξ₂).trans_lt (hneg₂ ξ₂ hξ₂ hx₂)⟩

open KSEighthBalanced
variable [Nonempty ι] [Fintype n] [DecidableEq n]

theorem exists_large_physical_descent
    (v : ι → n → ℂ) (hv : ∀ i, v i ≠ 0) (x : ι → ℝ)
    (hx : ∀ i, |x i| ≤ (1 / 8 : ℝ))
    (S₁ S₂ Z₁ Z₂ : Matrix n n ℂ) (hS₁ : S₁.PosDef) (hS₂ : S₂.PosDef)
    (hZ₁ : Z₁.PosDef) (hZ₂ : Z₂.PosDef)
    (ht₁ : Z₁ * KSBalancedSpin.source (fun i => KSRankOne.atom (v i)) (owner x) S₁ * Z₁ = S₁)
    (ht₂ : Z₂ * KSBalancedSpin.source (fun i => KSRankOne.atom (v i)) (owner x) S₂ * Z₂ = S₂)
    (hn₁ : ∀ i, owner x i * probe v Z₁ i < 1 / 8 - x i)
    (hn₂ : ∀ i, owner x i * probe v Z₂ i < 1 / 8 + x i) :
    ∃ W : Submodule ℝ (ι → ℝ),
      (13 / 16 : ℝ) * Fintype.card ι < (finrank ℝ W : ℝ) ∧
      ∀ y ∈ W, y ≠ 0 → ∃ (U₁ U₂ : Matrix n n ℂ), U₁.IsHermitian ∧ U₂.IsHermitian ∧
      KSBalancedSpin.physicalForce (fun i => KSRankOne.atom (v i)) (1 : Matrix n n ℂ) 64 x (direction x y) (probe v Z₁) -
        Z₁⁻¹ * U₁ * Z₁⁻¹ + KSBalancedSpin.source (fun i => KSRankOne.atom (v i)) (owner x) U₁ = 0 ∧
      KSBalancedSpin.physicalForce (fun i => KSRankOne.atom (v i)) (-1 : Matrix n n ℂ) 64 x (direction x y) (probe v Z₂) -
        Z₂⁻¹ * U₂ * Z₂⁻¹ + KSBalancedSpin.source (fun i => KSRankOne.atom (v i)) (owner x) U₂ = 0 ∧
      realTrace (S₁ * KSBalancedSpin.physicalAcceleration (fun i => KSRankOne.atom (v i)) Z₁ U₁ 64 x (direction x y) (probe v Z₁)) +
        realTrace (S₂ * KSBalancedSpin.physicalAcceleration (fun i => KSRankOne.atom (v i)) Z₂ U₂ 64 x (direction x y) (probe v Z₂)) < 0 := by
  have hn₁' : ∀ i, owner x i * probe v Z₁ i < 1 / 8 - (1 : ℝ) * x i := by simpa only [one_mul]
  have hn₂' : ∀ i, owner x i * probe v Z₂ i < 1 / 8 - (-1 : ℝ) * x i := by simpa only [neg_one_mul, sub_neg_eq_add]
  let d₁ := data v hv x hx 1 (Or.inr rfl) S₁ Z₁ hS₁ hZ₁ ht₁ hn₁'
  let d₂ := data v hv x hx (-1) (Or.inl rfl) S₂ Z₂ hS₂ hZ₂ ht₂ hn₂'
  obtain ⟨W, hdim, hW⟩ := exists_large_common_negative_completions d₁ d₂
  refine ⟨W, hdim, ?_⟩
  intro y hy hyne
  obtain ⟨ξ₁, ξ₂, he₁, he₂, hneg₁, hneg₂⟩ := hW y hy hyne
  refine ⟨transportCompletion v x Z₁ ξ₁, transportCompletion v x Z₂ ξ₂,
    transportCompletion_isHermitian v x Z₁ ξ₁, transportCompletion_isHermitian v x Z₂ ξ₂, ?_, ?_, ?_⟩
  · have hl := physical_velocity_zero v x hx hZ₁ 1 y ξ₁ (fun i => by
      have he := d₁.completion_legal ξ₁ i
      rw [he₁] at he
      exact he)
    simpa only [one_smul] using hl
  · have hl := physical_velocity_zero v x hx hZ₂ (-1) y ξ₂ (fun i => by
      have he := d₂.completion_legal ξ₂ i
      rw [he₂] at he
      exact he)
    simpa only [neg_one_smul] using hl
  · have ha₁ := physical_acceleration_eq v hv x hx 1 (Or.inr rfl) S₁ Z₁ hS₁ hZ₁ ht₁ hn₁' ξ₁
    have ha₂ := physical_acceleration_eq v hv x hx (-1) (Or.inl rfl) S₂ Z₂ hS₂ hZ₂ ht₂ hn₂' ξ₂
    change realTrace (S₁ * KSBalancedSpin.physicalAcceleration _ Z₁ _ 64 x
      (direction x (d₁.completion *ᵥ ξ₁)) (probe v Z₁)) = 2 * d₁.energy ξ₁ at ha₁
    change realTrace (S₂ * KSBalancedSpin.physicalAcceleration _ Z₂ _ 64 x
      (direction x (d₂.completion *ᵥ ξ₂)) (probe v Z₂)) = 2 * d₂.energy ξ₂ at ha₂
    rw [he₁] at ha₁
    rw [he₂] at ha₂
    rw [ha₁, ha₂]
    linarith


open KSEighthBlocks KSEighthActualState KSEighthFullSupport KSEighthLocalState

/-- More than 13k/16 normalized coefficient directions have strictly negative
actual second derivative. The two sign transports are internally supplied by
the actual density optimizer; no inertia or curvature premise remains. -/
theorem exists_large_negative_curve_subspace [Nonempty n]
    (Q : Matrix n n ℂ) (hQ : Q.IsHermitian) (v : ι → n → ℂ) (hv : ∀ i, v i ≠ 0)
    (x : ι → ℝ) (hx : ∀ i, |x i| ≤ (1 / 8 : ℝ)) {θ : ℝ} (hθ : 0 < θ)
    (hn₁ : ∀ i, owner x i * probe (KSEighthSupport.compressedVector v)
      (transport Q v x θ true) i < 1 / 8 - x i)
    (hn₂ : ∀ i, owner x i * probe (KSEighthSupport.compressedVector v)
      (transport Q v x θ false) i < 1 / 8 + x i) :
    ∃ W : Submodule ℝ (ι → ℝ),
      (13 / 16 : ℝ) * Fintype.card ι < (finrank ℝ W : ℝ) ∧
      ∀ y ∈ W, y ≠ 0 →
        deriv (curvePotential Q v θ x (direction x y)) 0 = 0 ∧
        iteratedDeriv 2 (curvePotential Q v θ x (direction x y)) 0 < 0 := by
  obtain ⟨W, hdim, hW⟩ := exists_large_physical_descent
    (KSEighthSupport.compressedVector v)
    (KSEighthSupport.compressedVector_ne_zero v hv) x hx
    (supportDensity Q v x θ true) (supportDensity Q v x θ false)
    (transport Q v x θ true) (transport Q v x θ false)
    (supportDensity_posDef Q v x hθ true) (supportDensity_posDef Q v x hθ false)
    (transport_posDef Q v hv x hx hθ true) (transport_posDef Q v hv x hx hθ false)
    (transport_solve Q v hv x hx hθ true) (transport_solve Q v hv x hx hθ false) hn₁ hn₂
  refine ⟨W, hdim, ?_⟩
  intro y hy hyne
  obtain ⟨U₁, U₂, hU₁, hU₂, hz₁, hz₂, hneg⟩ := hW y hy hyne
  exact KSEighthManuscriptContact.negative_second_of_completions
    Q hQ v hv x hx hθ (direction x y) U₁ U₂ hU₁ hU₂ hz₁ hz₂ hneg

end MatrixSpencer.KSEighthManuscriptInertia
