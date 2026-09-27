import HigherRankKS.SupportedFrameParameters
import HigherRankKS.SupportedResponseGeometry
import HigherRankKS.NormalizedForce
import HigherRankKS.SourceDerivative

/-! The normalized coefficient direction in the actual balanced frame. -/

open Matrix MatrixSpencer MatrixSpencer.KSFisher
open scoped BigOperators MatrixOrder ComplexOrder

noncomputable section
namespace HigherRankKS.SupportedFrames
open SupportedSpin BalancedFrames SourceProfile

variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]

def coefficientDirection (β : ℝ) (x y : ι → ℝ) : ι → ℝ :=
  fun i => NormalizedOwner.direction (owner β (x i)) (ownerScale β) (y i)

theorem coefficientDirection_eq {β : ℝ} (hβ : 0 < β) (x y : ι → ℝ)
    (hx : ∀ i, x i ∈ Set.Ioo (-1 : ℝ) 1) (i : ι) :
    coefficientDirection β x y i =
      (1 / Real.sqrt (ownerScale β)) * Real.sqrt (owner β (x i)) * y i :=
  NormalizedOwner.direction_eq_inv_sqrt (owner_pos hβ (hx i)).le _ _

theorem coefficientDirection_ne_zero {β : ℝ} (hβ : 0 < β) (x y : ι → ℝ)
    (hx : ∀ i, x i ∈ Set.Ioo (-1 : ℝ) 1) (hy : y ≠ 0) :
    coefficientDirection β x y ≠ 0 :=
  NormalizedOwner.direction_ne_zero (fun i => owner_pos hβ (hx i)) (ownerScale_pos hβ) hy

theorem normalized_force (A : ι → Matrix n n ℂ) {β : ℝ} (hβ : 0 < β)
    (x y : ι → ℝ) (hx : ∀ i, x i ∈ Set.Ioo (-1 : ℝ) 1)
    (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) :
    let Z := transport A β (weights β x) S
    (∑ i, coefficientDirection β x y i •
      (involution A * balancedKraus (probe A) Z i +
        (deriv (owner β) (x i) * q A β x S i) • balancedKraus (probe A) Z i)) =
      (1 / Real.sqrt (ownerScale β)) •
        (involution A * synthesis (E A β x S) y -
          synthesis (E A β x S) (Matrix.diagonal (z A β x S) *ᵥ y)) := by
  dsimp only
  simp only [coefficientDirection_eq hβ x y hx]
  exact NormalizedForce.force_identity _ _ _ _ _ _ _

theorem normalized_source (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (hne : ∀ i, A i ≠ 0) (k : ℕ) (hk : 1 ≤ k) (x y : ι → ℝ)
    (hx : ∀ i, x i ∈ Set.Ioo (-1 : ℝ) 1)
    {S : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hS : S.PosDef) :
    let β := (1 : ℝ) / 2 ^ k
    let Z := transport A β (weights β x) S
    (∑ i, (deriv (owner β) (x i) * coefficientDirection β x y i) •
      balancedKraus (term A β S) Z i) =
      (-(1 / Real.sqrt (ownerScale β))) •
        synthesis (F A β x S) (fun i => R A β x S i * z A β x S i * y i) := by
  dsimp only
  have hβ : 0 < (1 : ℝ) / 2 ^ k := by positivity
  have hp := carrierMass_pos (probe A) (probe_posSemidef A hA)
    (fun i => probe_ne_zero A hA i (hne i)) (density_posDef A hS)
  simp only [coefficientDirection_eq hβ x y hx, R_eq_mass_div_q A hβ x hx S]
  exact NormalizedForce.source_identity _ _ _ _ _ _ (fun i => (hp i).ne')
    (fun i => (q_pos A hA hne k hk x hx hS i).ne') _

theorem normalized_force_pairing (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (k : ℕ) (hk : 1 ≤ k) (x y : ι → ℝ)
    (hx : ∀ i, x i ∈ Set.Ioo (-1 : ℝ) 1)
    {S : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hS : S.PosDef)
    (hfixed : KSSignSymmetry.conjugate KSSignSymmetry.signMatrix S = S)
    (X : Matrix (n ⊕ n) (n ⊕ n) ℂ) :
    let β := (1 : ℝ) / 2 ^ k
    let h := coefficientDirection β x y
    let Z := transport A β (weights β x) S
    realTrace ((∑ i, h i • signedLift (A i)) * X) +
      (∑ i, h i * deriv (owner β) (x i) * q A β x S i * realTrace (spinAtom (A i) * X)) =
      (1 / Real.sqrt (ownerScale β)) *
        realTrace ((involution A * synthesis (E A β x S) y -
          synthesis (E A β x S) (Matrix.diagonal (z A β x S) *ᵥ y)) *
            balancedDensity (density A X) Z) := by
  dsimp only
  have hβ : 0 < (1 : ℝ) / 2 ^ k := by positivity
  have hc : ∀ i, 0 < weights ((1 : ℝ) / 2 ^ k) x i :=
    fun i => owner_pos hβ (hx i)
  rw [balanced_scalar_force_pairing A hA X (transport_posDef A hA hc hS k hk)
    (involution_commute_transport A hA hc hS hfixed k hk),
    normalized_force A hβ x y hx S, Matrix.smul_mul, realTrace_smul]

theorem mass_mul_q (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (hne : ∀ i, A i ≠ 0) (β : ℝ) (x : ι → ℝ)
    {S : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hS : S.PosDef) (i : ι) :
    carrierMass (probe A) (density A S) i * q A β x S i =
      transportMass (term A β S) (transport A β (weights β x) S) i := by
  have hp := carrierMass_pos (probe A) (probe_posSemidef A hA)
    (fun i => probe_ne_zero A hA i (hne i)) (density_posDef A hS)
  unfold q
  field_simp [(hp i).ne']

theorem probe_value_eq_mass_q (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (hne : ∀ i, A i ≠ 0) (β : ℝ) (x : ι → ℝ)
    (S : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ))
    (hS : (S : Matrix (n ⊕ n) (n ⊕ n) ℂ).PosDef) (i : ι) :
    let Z := transport A β (weights β x) S
    SourceDerivative.probe β (A i) (sourceEmbedding A * Z * (sourceEmbedding A)ᴴ) S =
      carrierMass (probe A) (density A S) i * q A β x S i := by
  rw [mass_mul_q A hA hne β x hS i, transportMass, term_pairing]
  rfl

theorem normalized_owner_budget (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (hne : ∀ i, A i ≠ 0) (k : ℕ) (hk : 1 ≤ k) (x y : ι → ℝ)
    (hx : ∀ i, x i ∈ Set.Ioo (-1 : ℝ) 1)
    (S : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ))
    (hS : (S : Matrix (n ⊕ n) (n ⊕ n) ℂ).PosDef) :
    let β := (1 : ℝ) / 2 ^ k
    let h := coefficientDirection β x y
    let Z := transport A β (weights β x) S
    let τ := fun i => SourceDerivative.probe β (A i) (sourceEmbedding A * Z * (sourceEmbedding A)ᴴ) S
    (∑ i, h i ^ 2 * deriv (deriv (owner β)) (x i) * τ i) / 2 +
      (1 - β) / β * (∑ i, (h i * deriv (owner β) (x i)) ^ 2 * τ i / owner β (x i)) ≤
      -(∑ i, R A β x S i * r A β x S i ^ 2 * y i ^ 2) -
        (2 / ownerScale β) * (∑ i, R A β x S i * z A β x S i ^ 2 * y i ^ 2) := by
  dsimp only
  have hb := summed_owner_payment A hA hne k hk x hx hS y
  dsimp only at hb
  convert hb using 1
  simp only [probe_value_eq_mass_q A hA hne _ x S hS]
  rw [Finset.sum_div, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  dsimp only [coefficientDirection]
  ring

end HigherRankKS.SupportedFrames
