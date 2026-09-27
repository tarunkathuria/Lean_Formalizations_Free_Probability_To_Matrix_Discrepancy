import MatrixSpencer.KSEighthFullSupport

/-! Compatible, concrete negative transport directions for the old two sign blocks. -/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSEighthPhysicalDescent
open KSEighthBalanced

variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] [Fintype n] [DecidableEq n]

theorem exists_common_physical_descent
    (v : ι → n → ℂ) (hv : ∀ i, v i ≠ 0) (x : ι → ℝ)
    (hx : ∀ i, |x i| ≤ (1 / 8 : ℝ))
    (S₁ S₂ Z₁ Z₂ : Matrix n n ℂ) (hS₁ : S₁.PosDef) (hS₂ : S₂.PosDef)
    (hZ₁ : Z₁.PosDef) (hZ₂ : Z₂.PosDef)
    (ht₁ : Z₁ * KSBalancedSpin.source (fun i => KSRankOne.atom (v i)) (owner x) S₁ * Z₁ = S₁)
    (ht₂ : Z₂ * KSBalancedSpin.source (fun i => KSRankOne.atom (v i)) (owner x) S₂ * Z₂ = S₂)
    (hn₁ : ∀ i, owner x i * probe v Z₁ i < 1 / 8 - x i)
    (hn₂ : ∀ i, owner x i * probe v Z₂ i < 1 / 8 + x i) :
    ∃ (h : ι → ℝ) (U₁ U₂ : Matrix n n ℂ), h ≠ 0 ∧ U₁.IsHermitian ∧ U₂.IsHermitian ∧
      KSBalancedSpin.physicalForce (fun i => KSRankOne.atom (v i)) (1 : Matrix n n ℂ) 64 x h (probe v Z₁) -
        Z₁⁻¹ * U₁ * Z₁⁻¹ + KSBalancedSpin.source (fun i => KSRankOne.atom (v i)) (owner x) U₁ = 0 ∧
      KSBalancedSpin.physicalForce (fun i => KSRankOne.atom (v i)) (-1 : Matrix n n ℂ) 64 x h (probe v Z₂) -
        Z₂⁻¹ * U₂ * Z₂⁻¹ + KSBalancedSpin.source (fun i => KSRankOne.atom (v i)) (owner x) U₂ = 0 ∧
      realTrace (S₁ * KSBalancedSpin.physicalAcceleration (fun i => KSRankOne.atom (v i)) Z₁ U₁ 64 x h (probe v Z₁)) +
        realTrace (S₂ * KSBalancedSpin.physicalAcceleration (fun i => KSRankOne.atom (v i)) Z₂ U₂ 64 x h (probe v Z₂)) < 0 := by
  have hn₁' : ∀ i, owner x i * probe v Z₁ i < 1 / 8 - (1 : ℝ) * x i := by simpa only [one_mul]
  have hn₂' : ∀ i, owner x i * probe v Z₂ i < 1 / 8 - (-1 : ℝ) * x i := by simpa only [neg_one_mul, sub_neg_eq_add]
  let d₁ := data v hv x hx 1 (Or.inr rfl) S₁ Z₁ hS₁ hZ₁ ht₁ hn₁'
  let d₂ := data v hv x hx (-1) (Or.inl rfl) S₂ Z₂ hS₂ hZ₂ ht₂ hn₂'
  obtain ⟨y, ξ₁, ξ₂, hy, he₁, he₂, hneg₁, hneg₂⟩ :=
    KSEighthCompletion.exists_common_negative_completions d₁ d₂
  have hh : direction x y ≠ 0 := by
    intro hz
    apply hy
    funext i
    have hh := congrFun hz i
    rw [direction_eq x y hx i] at hh
    have hs : 0 < Real.sqrt (1 - x i ^ 2) := Real.sqrt_pos.mpr
      (by have hi := KSEighthComparison.eighth_square_bound (hx i); linarith)
    exact (mul_eq_zero.mp hh).resolve_left hs.ne'
  refine ⟨direction x y, transportCompletion v x Z₁ ξ₁, transportCompletion v x Z₂ ξ₂, hh,
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

end MatrixSpencer.KSEighthPhysicalDescent
