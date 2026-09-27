import MatrixSpencer.DyadicTsallisHessian
import MatrixSpencer.DyadicTraceBounds
import MatrixSpencer.HermitianConeConcavity

/-! Continuity and the exact density budget of the actual dyadic regularizer. -/
open Matrix Set
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace MatrixSpencer
noncomputable section
variable {n : Type*} [Fintype n] [DecidableEq n]
local instance dyadicBoundsCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance dyadicBoundsSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance

theorem dyadic_order_two_le {m : ℕ} (hm : 1 ≤ m) : 2 ≤ 2 ^ m :=
  (show 2 ^ 1 ≤ 2 ^ m from Nat.pow_le_pow_right (by norm_num) hm)

theorem dyadic_normalization_pos {m : ℕ} (hm : 1 ≤ m) {θ : ℝ} (hθ : 0 < θ) :
    0 < θ * (2 ^ m : ℝ) / ((2 ^ m : ℝ) - 1) := by
  have hp : (2 : ℝ) ≤ 2 ^ m := by exact_mod_cast dyadic_order_two_le hm
  exact div_pos (mul_pos hθ (by positivity)) (by linarith)

theorem dyadic_normalization_nonneg {m : ℕ} (hm : 1 ≤ m) {θ : ℝ} (hθ : 0 ≤ θ) :
    0 ≤ θ * (2 ^ m : ℝ) / ((2 ^ m : ℝ) - 1) := by
  have hp : (2 : ℝ) ≤ 2 ^ m := by exact_mod_cast dyadic_order_two_le hm
  exact div_nonneg (mul_nonneg hθ (by positivity)) (by linarith)

theorem dyadicTsallisRegularizer_eq_scaled_trace (m : ℕ) (θ : ℝ) (S : Matrix n n ℂ) :
    dyadicTsallisRegularizer m θ S =
      (θ * (2 ^ m : ℝ) / ((2 ^ m : ℝ) - 1)) * dyadicTracePower m S := rfl

theorem continuousOn_dyadicTsallisRegularizer (m : ℕ) (θ : ℝ) :
    ContinuousOn (dyadicTsallisRegularizer (n := n) m θ) {S | S.PosSemidef} :=
  continuousOn_const.mul (continuousOn_dyadicTracePower m)

theorem continuousOn_density_dyadicTsallisRegularizer (m : ℕ) (θ : ℝ) :
    ContinuousOn (dyadicTsallisRegularizer (n := n) m θ) densitySet :=
  (continuousOn_dyadicTsallisRegularizer m θ).mono (fun _ hS => hS.1)

theorem continuousOn_dyadicTsallisPotential (m : ℕ) (θ : ℝ) :
    ContinuousOn (dyadicTsallisPotential (n := n) m θ) hermitianSemidefiniteCone :=
  (continuousOn_dyadicTsallisRegularizer m θ).comp
    (hermitianInclusion (n := n)).continuous.continuousOn (fun _ hS => hS)

theorem dyadicTsallisRegularizer_nonneg {m : ℕ} (hm : 1 ≤ m) {θ : ℝ} (hθ : 0 ≤ θ)
    {S : Matrix n n ℂ} (hS : S.PosSemidef) : 0 ≤ dyadicTsallisRegularizer m θ S :=
  mul_nonneg (dyadic_normalization_nonneg hm hθ) (dyadicTracePower_nonneg m hS)

theorem dyadicTsallisRegularizer_density_bound {m : ℕ} (hm : 1 ≤ m) {θ : ℝ} (hθ : 0 ≤ θ)
    {S : Matrix n n ℂ} (hS : S ∈ densitySet) :
    dyadicTsallisRegularizer m θ S ≤
      (θ * (2 ^ m : ℝ) / ((2 ^ m : ℝ) - 1)) *
        (Fintype.card n : ℝ) ^ (1 / (2 ^ m : ℝ)) := by
  rw [dyadicTsallisRegularizer_eq_scaled_trace]
  have h := mul_le_mul_of_nonneg_left (dyadicTracePower_le_dimension_rpow hm hS.1 hS.2)
    (dyadic_normalization_nonneg hm hθ)
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using h

theorem dyadicTsallisRegularizer_density_bound_reciprocal {m : ℕ} (hm : 1 ≤ m)
    {θ : ℝ} (hθ : 0 ≤ θ) {S : Matrix n n ℂ} (hS : S ∈ densitySet) :
    dyadicTsallisRegularizer m θ S ≤
      θ * (Fintype.card n : ℝ) ^ (1 / (2 ^ m : ℝ)) / (1 - 1 / (2 ^ m : ℝ)) := by
  have h := dyadicTsallisRegularizer_density_bound hm hθ hS
  have hp : (2 : ℝ) ≤ 2 ^ m := by exact_mod_cast dyadic_order_two_le hm
  have hp0 : (2 ^ m : ℝ) ≠ 0 := by positivity
  have hp1 : (2 ^ m : ℝ) - 1 ≠ 0 := by linarith
  convert h using 1
  field_simp

theorem dyadicTsallisRegularizer_normalized_identity (m : ℕ) (θ : ℝ) [Nonempty n] :
    dyadicTsallisRegularizer m θ ((1 / (Fintype.card n : ℝ)) • (1 : Matrix n n ℂ)) =
      (θ * (2 ^ m : ℝ) / ((2 ^ m : ℝ) - 1)) *
        (Fintype.card n : ℝ) ^ (1 / (2 ^ m : ℝ)) := by
  rw [dyadicTsallisRegularizer_eq_scaled_trace, dyadicTracePower_normalized_identity]
  simp only [Nat.cast_pow, Nat.cast_ofNat]

theorem dyadicTsallisRegularizer_density_projection {m : ℕ} (hm : 1 ≤ m) (θ : ℝ)
    {S : Matrix n n ℂ} (hS : S.PosSemidef) (hidem : S * S = S) (htrace : realTrace S = 1) :
    dyadicTsallisRegularizer m θ S = θ * (2 ^ m : ℝ) / ((2 ^ m : ℝ) - 1) := by
  rw [dyadicTsallisRegularizer_eq_scaled_trace,
    dyadicTracePower_eq_one_of_density_projection hm hS hidem htrace, mul_one]

end
end MatrixSpencer
