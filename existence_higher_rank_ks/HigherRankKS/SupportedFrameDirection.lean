import HigherRankKS.SupportedDiagonal
import HigherRankKS.SourceProfile

/-!
# Instantiating the projection at an actual higher-rank source

All frames, probes, and covariance terms in this file are constructed
from the given matrices, a faithful symmetric density, and its exact
supported transport. No Gram or projection bounds are supplied as data.
-/

open Matrix MatrixSpencer MatrixSpencer.KSSignSymmetry MatrixSpencer.KSSpinDrift
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

noncomputable section
namespace HigherRankKS.SupportedFrames

open SupportedSpin BalancedFrames SourceProfile

variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]

def weights (β : ℝ) (x : ι → ℝ) : ι → ℝ := fun i => owner β (x i)
def q (A : ι → Matrix n n ℂ) (β : ℝ) (x : ι → ℝ)
    (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) (i : ι) : ℝ :=
  transportMass (term A β S) (transport A β (weights β x) S) i /
    carrierMass (probe A) (density A S) i
def E (A : ι → Matrix n n ℂ) (β : ℝ) (x : ι → ℝ)
    (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) :=
  measurementFrame (probe A) (weights β x) (transport A β (weights β x) S)
def F (A : ι → Matrix n n ℂ) (β : ℝ) (x : ι → ℝ)
    (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) :=
  preparationFrame (probe A) (term A β S) (weights β x)
    (density A S) (transport A β (weights β x) S)
def μ (A : ι → Matrix n n ℂ) (β : ℝ) (x : ι → ℝ)
    (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) :=
  coefficientMass (probe A) (weights β x) (density A S)
def r (A : ι → Matrix n n ℂ) (β : ℝ) (x : ι → ℝ)
    (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) :=
  probeScale (probe A) (term A β S) (weights β x)
    (density A S) (transport A β (weights β x) S)
def z (A : ι → Matrix n n ℂ) (β : ℝ) (x : ι → ℝ)
    (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) : ι → ℝ :=
  fun i => -(deriv (owner β) (x i)) * q A β x S i
def P (A : ι → Matrix n n ℂ) (β : ℝ) (x : ι → ℝ)
    (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) :=
  balancedDensity (density A S) (transport A β (weights β x) S)
def R (A : ι → Matrix n n ℂ) (β : ℝ) (x : ι → ℝ)
    (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) : ι → ℝ :=
  fun i => μ A β x S i / r A β x S i

theorem exists_negative_actual_frame [Nonempty ι]
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef) (hne : ∀ i, A i ≠ 0)
    (k : ℕ) (hk : 1 ≤ k) (x : ι → ℝ) (hx : ∀ i, x i ∈ Set.Ioo (-1 : ℝ) 1)
    {S : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hS : S.PosDef)
    (hfixed : conjugate signMatrix S = S)
    (hfail : ∀ i, ((1 : ℝ) / 2 ^ k) * owner ((1 : ℝ) / 2 ^ k) (x i) *
      q A ((1 : ℝ) / 2 ^ k) x S i < endpointDistance (x i)) :
    let β := (1 : ℝ) / 2 ^ k
    let Es := E A β x S
    let Fs := F A β x S
    let zs := z A β x S
    ∃ ω y : ι → ℝ, y ≠ 0 ∧
      (1 - (TwoFrames.channel Es Fs)ᵀ) *ᵥ ω =
        ((TwoFrames.spinChannel (involution A) Es Fs)ᵀ -
          (TwoFrames.channel Es Fs)ᵀ * Matrix.diagonal zs) *ᵥ y ∧
      legalUpper ((1 / β) • P A β x S) (involution A) Es (R A β x S)
        (fun i => r A β x S i ^ 2 + (2 / (100 / β)) * (zs i) ^ 2)
        zs (100 / β) ω y < 0 := by
  let β : ℝ := 1 / 2 ^ k
  have hβ : 0 < β := by dsimp [β]; positivity
  have hβhalf : β ≤ 1 / 2 := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
    have hj : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    dsimp [β]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ (1 + j))).mpr
    rw [pow_add]
    norm_num
    linarith
  have hc : ∀ i, 0 < weights β x i := fun i => owner_pos hβ (hx i)
  have hp := carrierMass_pos (probe A) (probe_posSemidef A hA)
    (fun i => probe_ne_zero A hA i (hne i)) (density_posDef A hS)
  have hZ := transport_posDef A hA hc hS k hk
  have hτ := transportMass_pos (term A β S) (term_posSemidef A β hS.posSemidef)
    (fun i => term_ne_zero A hA hS k hk i (hne i)) hZ
  have hq : ∀ i, 0 < q A β x S i := fun i => div_pos (hτ i) (hp i)
  have hμ : ∀ i, 0 < μ A β x S i := coefficientMass_pos _ _ _ hc hp
  have hr : ∀ i, 0 < r A β x S i := probeScale_pos _ _ _ _ _ hc hp hτ
  have hrq : ∀ i, r A β x S i = Real.sqrt (owner β (x i)) * q A β x S i := by
    intro i
    unfold r probeScale q weights
    ring
  have hcaps := fun i => failed_endpoint_caps hβ (hq i).le (hx i) (hfail i)
  have hP : P A β x S = TwoFrames.frameSum (F A β x S) (μ A β x S) := by
    apply balancedDensity_eq_frameSum _ _ _ (fun i => (hc i).le) hZ (fun i => (hp i).ne')
    rw [← compressedSource_eq_sum]
    exact transport_equation A hA hc hS k hk
  have hpair : ∀ i, realTrace (E A β x S i *
      TwoFrames.frameSum (F A β x S) (μ A β x S)) = μ A β x S i := by
    intro i
    rw [← hP]
    exact measurement_pairing _ _ _ hZ i
  have hcomm : ∀ i, involution A * E A β x S i = E A β x S i * involution A :=
    KSBalancedSpin.atom_commute _ _
      (involution_commute_transport A hA hc hS hfixed k hk).eq
      (fun i => (involution_commute_probe A hA i).eq)
  have hd : ∀ i, realTrace (TwoFrames.frameSum (F A β x S) (μ A β x S) *
      E A β x S i * E A β x S i) / (μ A β x S i / r A β x S i) ≤ r A β x S i ^ 2 := by
    intro i
    rw [← hP]
    exact actual_balanced_diagonal A hA hne hc hS (sign_fixed_blockDiagonal hfixed) k hk i
  have ht := TwoFrames.exists_negative_frame_direction (E A β x S) (F A β x S)
    (measurementFrame_posSemidef _ (probe_posSemidef A hA) _ _)
    (preparationFrame_posSemidef _ _ (term_posSemidef A β hS.posSemidef) _ _ _
      (fun i => (hp i).le)) hμ hr (trace_preparationFrame _ _ _ _ hZ) hpair
    (involution_isHermitian A) (involution_sq A hA) hcomm hβ hβhalf
    (by exact div_nonneg (kappa_pos hβ).le (sq_nonneg β)) (hcaps (Classical.arbitrary ι)).2.2.2
    (z A β x S) (fun i => (hcaps i).1.trans (hcaps i).2.1.le)
    (fun i => by rw [hrq]; exact (hcaps i).2.2.1) hd
  rw [← hP] at ht
  exact ht

end HigherRankKS.SupportedFrames
