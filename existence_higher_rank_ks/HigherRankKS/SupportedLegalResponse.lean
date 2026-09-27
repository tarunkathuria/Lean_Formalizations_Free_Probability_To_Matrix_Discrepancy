import HigherRankKS.SupportedFrameNormalization
import HigherRankKS.ResponseReduction

/-! The legal response bound at the concrete supported source. -/

open Matrix MatrixSpencer MatrixSpencer.KSFisher MatrixSpencer.KSSpinDrift
open scoped BigOperators MatrixOrder ComplexOrder

noncomputable section
namespace HigherRankKS.SupportedFrames
open SupportedSpin BalancedFrames SourceProfile

variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]

theorem legal_upper_bound (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (hne : ∀ i, A i ≠ 0) (k : ℕ) (hk : 1 ≤ k) (x : ι → ℝ)
    (hx : ∀ i, x i ∈ Set.Ioo (-1 : ℝ) 1)
    {S : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hS : S.PosDef)
    (hfixed : KSSignSymmetry.conjugate KSSignSymmetry.signMatrix S = S)
    (ω y : ι → ℝ)
    (hlegal : (1 - (TwoFrames.channel (E A ((1 : ℝ) / 2 ^ k) x S)
        (F A ((1 : ℝ) / 2 ^ k) x S))ᵀ) *ᵥ ω =
      ((TwoFrames.spinChannel (involution A) (E A ((1 : ℝ) / 2 ^ k) x S)
        (F A ((1 : ℝ) / 2 ^ k) x S))ᵀ -
        (TwoFrames.channel (E A ((1 : ℝ) / 2 ^ k) x S)
          (F A ((1 : ℝ) / 2 ^ k) x S))ᵀ * Matrix.diagonal (z A ((1 : ℝ) / 2 ^ k) x S)) *ᵥ y)
    (X : Matrix (n ⊕ n) (n ⊕ n) ℂ) (hX : X.IsHermitian) :
    let β := (1 : ℝ) / 2 ^ k
    let u := ownerScale β
    let a := 1 / Real.sqrt u
    let Es := E A β x S
    let Fs := F A β x S
    let Y := balancedDensity (density A X) (transport A β (weights β x) S)
    let N := (-a) • synthesis Fs (fun i => R A β x S i * z A β x S i * y i);
    -(∑ i, R A β x S i * r A β x S i ^ 2 * y i ^ 2) -
      (2 / u) * (∑ i, R A β x S i * z A β x S i ^ 2 * y i ^ 2) +
      a * realTrace ((involution A * synthesis Es y -
        synthesis Es (Matrix.diagonal (z A β x S) *ᵥ y)) * Y) -
      β / 2 * SylvesterMetric.energy (P A β x S) (P_posDef A hA k hk x hx hS)
        (Y - TwoFrames.frameChannel Es Fs Y - N) ≤
      legalUpper ((1 / β) • P A β x S) (involution A) Es (R A β x S)
        (fun i => r A β x S i ^ 2 + (2 / u) * z A β x S i ^ 2)
        (z A β x S) u ω y := by
  dsimp only
  have hβ : 0 < (1 : ℝ) / 2 ^ k := by positivity
  have hc : ∀ i, 0 < weights ((1 : ℝ) / 2 ^ k) x i :=
    fun i => owner_pos hβ (hx i)
  have hp := carrierMass_pos (probe A) (probe_posSemidef A hA)
    (fun i => probe_ne_zero A hA i (hne i)) (density_posDef A hS)
  have hZ := transport_posDef A hA hc hS k hk
  have hE : ∀ i, (E A ((1 : ℝ) / 2 ^ k) x S i).IsHermitian :=
    fun i => (measurementFrame_posSemidef _ (probe_posSemidef A hA) _ _ i).isHermitian
  have hF : ∀ i, (F A ((1 : ℝ) / 2 ^ k) x S i).IsHermitian :=
    fun i => (preparationFrame_posSemidef _ _
      (term_posSemidef A _ hS.posSemidef) _ _ _ (fun i => (hp i).le) i).isHermitian
  have hcomm : ∀ i, involution A * E A ((1 : ℝ) / 2 ^ k) x S i =
      E A ((1 : ℝ) / 2 ^ k) x S i * involution A :=
    KSBalancedSpin.atom_commute _ _
      (involution_commute_transport A hA hc hS hfixed k hk).eq
      (fun i => (involution_commute_probe A hA i).eq)
  have hY : (balancedDensity (density A X) (transport A ((1 : ℝ) / 2 ^ k)
      (weights ((1 : ℝ) / 2 ^ k) x) S)).IsHermitian := by
    have hX0 := KSSupportSymmetry.compress_isHermitian (sourceEmbedding A) hX
    change (density A X).IsHermitian at hX0
    have hI := (transportInverseSqrt_posDef hZ).isHermitian
    simp only [balancedDensity, Matrix.IsHermitian, Matrix.conjTranspose_mul,
      hI.eq, hX0.eq, Matrix.mul_assoc]
  exact ResponseReduction.normalized_legal_bound _ _ hE hF (involution_isHermitian A)
    (P_posDef A hA k hk x hx hS) hcomm (R A _ x S) (r A _ x S) (z A _ x S) ω y
    hlegal hβ (ownerScale_pos hβ) hY

end HigherRankKS.SupportedFrames
