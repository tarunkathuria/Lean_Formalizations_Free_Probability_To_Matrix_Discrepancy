import HigherRankKS.SupportedFrameDirection
import HigherRankKS.NormalizedOwner

/-! Scalar identities relating the actual two frames to the owner payment. -/

open Matrix MatrixSpencer
open scoped BigOperators MatrixOrder ComplexOrder

noncomputable section
namespace HigherRankKS.SupportedFrames

open SupportedSpin BalancedFrames SourceProfile
variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]

theorem q_pos (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (hne : ∀ i, A i ≠ 0) (k : ℕ) (hk : 1 ≤ k)
    (x : ι → ℝ) (hx : ∀ i, x i ∈ Set.Ioo (-1 : ℝ) 1)
    {S : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hS : S.PosDef) (i : ι) :
    0 < q A ((1 : ℝ) / 2 ^ k) x S i := by
  have hc : ∀ i, 0 < weights ((1 : ℝ) / 2 ^ k) x i :=
    fun i => owner_pos (by positivity) (hx i)
  have hp := carrierMass_pos (probe A) (probe_posSemidef A hA)
    (fun i => probe_ne_zero A hA i (hne i)) (density_posDef A hS)
  have hτ := transportMass_pos (term A ((1 : ℝ) / 2 ^ k) S)
    (term_posSemidef A _ hS.posSemidef)
    (fun i => term_ne_zero A hA hS k hk i (hne i))
    (transport_posDef A hA hc hS k hk)
  exact div_pos (hτ i) (hp i)

theorem P_posDef (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (k : ℕ) (hk : 1 ≤ k) (x : ι → ℝ)
    (hx : ∀ i, x i ∈ Set.Ioo (-1 : ℝ) 1)
    {S : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hS : S.PosDef) :
    (P A ((1 : ℝ) / 2 ^ k) x S).PosDef :=
  balancedDensity_posDef (density_posDef A hS)
    (transport_posDef A hA (fun i => owner_pos (by positivity) (hx i)) hS k hk)

theorem r_eq_sqrt_mul_q (A : ι → Matrix n n ℂ) (β : ℝ) (x : ι → ℝ)
    (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) (i : ι) :
    r A β x S i = Real.sqrt (owner β (x i)) * q A β x S i := by
  unfold r probeScale q weights
  ring

theorem R_eq_mass_div_q (A : ι → Matrix n n ℂ) {β : ℝ} (hβ : 0 < β)
    (x : ι → ℝ) (hx : ∀ i, x i ∈ Set.Ioo (-1 : ℝ) 1)
    (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) (i : ι) :
    R A β x S i = carrierMass (probe A) (density A S) i / q A β x S i := by
  unfold R μ coefficientMass
  rw [r_eq_sqrt_mul_q]
  change (Real.sqrt (owner β (x i)) * _) / (Real.sqrt (owner β (x i)) * _) = _
  exact mul_div_mul_left _ _ (Real.sqrt_pos.mpr (owner_pos hβ (hx i))).ne'

theorem weighted_r_square (A : ι → Matrix n n ℂ) {β : ℝ} (hβ : 0 < β)
    (x : ι → ℝ) (hx : ∀ i, x i ∈ Set.Ioo (-1 : ℝ) 1)
    (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) (i : ι) :
    R A β x S i * r A β x S i ^ 2 =
      owner β (x i) * (carrierMass (probe A) (density A S) i * q A β x S i) := by
  rw [R_eq_mass_div_q A hβ x hx S, r_eq_sqrt_mul_q, mul_pow,
    Real.sq_sqrt (owner_pos hβ (hx i)).le]
  by_cases hq : q A β x S i = 0
  · simp [hq]
  · field_simp
    <;> ring

theorem summed_owner_payment (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (hne : ∀ i, A i ≠ 0) (k : ℕ) (hk : 1 ≤ k)
    (x : ι → ℝ) (hx : ∀ i, x i ∈ Set.Ioo (-1 : ℝ) 1)
    {S : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hS : S.PosDef) (y : ι → ℝ) :
    let β := (1 : ℝ) / 2 ^ k
    let u := ownerScale β
    (∑ i, (1 / 2 : ℝ) * NormalizedOwner.direction (owner β (x i)) u (y i) ^ 2 *
      (carrierMass (probe A) (density A S) i * q A β x S i) *
      (deriv (deriv (owner β)) (x i) + (2 * (1 - β) / β) *
        (deriv (owner β) (x i)) ^ 2 / owner β (x i))) ≤
      -(∑ i, R A β x S i * r A β x S i ^ 2 * y i ^ 2) -
        (2 / u) * (∑ i, R A β x S i * z A β x S i ^ 2 * y i ^ 2) := by
  dsimp only
  have hβ : 0 < (1 : ℝ) / 2 ^ k := by positivity
  have hp := carrierMass_pos (probe A) (probe_posSemidef A hA)
    (fun i => probe_ne_zero A hA i (hne i)) (density_posDef A hS)
  have hb := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    NormalizedOwner.owner_payment hβ (hx i) (hp i).le
      (q_pos A hA hne k hk x hx hS i) (y i))
  convert hb using 1
  simp only [weighted_r_square A hβ x hx S]
  simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.mul_sum,
    R_eq_mass_div_q A hβ x hx S, z]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

end HigherRankKS.SupportedFrames
