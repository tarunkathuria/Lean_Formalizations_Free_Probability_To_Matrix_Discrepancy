import AugmentedHigherRankKS.FourBlockForceSupport
import HigherRankKS.BalancedFrames
import HigherRankKS.TwoFrameFisher

/-! Normalized frames constructed from the actual four-block source and transport. -/
noncomputable section
open Matrix MatrixSpencer HigherRankKS MatrixSpencer.KSFisher MatrixSpencer.KSSpinDrift
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace AugmentedHigherRankKS
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]

/-- Weighted diagonal estimate for a general Hermitian force family. -/
theorem weighted_force_diagonal_le (B O G : ι → Matrix n n ℂ) (c : ι → ℝ)
    (hc : ∀ i, 0 < c i) (S : Matrix n n ℂ) {Z : Matrix n n ℂ} (hZ : Z.PosDef)
    (hp : ∀ i, 0 < BalancedFrames.carrierMass B S i)
    (hτ : ∀ i, 0 < BalancedFrames.transportMass O Z i) (κ : ℝ)
    (hbound : ∀ i, realTrace (S * G i * Z * G i) ≤ κ * BalancedFrames.transportMass O Z i)
    (i : ι) :
    realTrace (balancedDensity S Z * BalancedFrames.measurementFrame G c Z i *
      BalancedFrames.measurementFrame G c Z i) /
      (BalancedFrames.coefficientMass B c S i / BalancedFrames.probeScale B O c S Z i) ≤
      κ * BalancedFrames.probeScale B O c S Z i ^ 2 := by
  rw [BalancedFrames.physical_diagonal G c (fun i => (hc i).le) S hZ]
  have hR : 0 < BalancedFrames.coefficientMass B c S i / BalancedFrames.probeScale B O c S Z i :=
    div_pos (BalancedFrames.coefficientMass_pos B c S hc hp i)
      (BalancedFrames.probeScale_pos B O c S Z hc hp hτ i)
  calc
    _ ≤ c i * (κ * BalancedFrames.transportMass O Z i) /
        (BalancedFrames.coefficientMass B c S i / BalancedFrames.probeScale B O c S Z i) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hbound i) (hc i).le) hR.le
    _ = _ := by
      unfold BalancedFrames.coefficientMass BalancedFrames.probeScale
      field_simp [(hp i).ne', (hτ i).ne', (Real.sqrt_pos.mpr (hc i)).ne']
      rw [Real.sq_sqrt (hc i).le]
      ring

namespace Frames
open AugmentedHigherRankKS.SupportedSpin HigherRankKS.BalancedFrames

def E (A : ι → Matrix n n ℂ) (β : ℝ) (c : ι → ℝ)
    (S : Matrix (FourSpin n) (FourSpin n) ℂ) := measurementFrame (probe A) c (transport A β c S)
def F (A : ι → Matrix n n ℂ) (β : ℝ) (c : ι → ℝ)
    (S : Matrix (FourSpin n) (FourSpin n) ℂ) :=
  preparationFrame (probe A) (term A β S) c (density A S) (transport A β c S)
def N (A : ι → Matrix n n ℂ) (β : ℝ) (c x : ι → ℝ)
    (S : Matrix (FourSpin n) (FourSpin n) ℂ) := measurementFrame (force A x) c (transport A β c S)
def μ (A : ι → Matrix n n ℂ) (c : ι → ℝ)
    (S : Matrix (FourSpin n) (FourSpin n) ℂ) := coefficientMass (probe A) c (density A S)
def r (A : ι → Matrix n n ℂ) (β : ℝ) (c : ι → ℝ)
    (S : Matrix (FourSpin n) (FourSpin n) ℂ) :=
  probeScale (probe A) (term A β S) c (density A S) (transport A β c S)
def R (A : ι → Matrix n n ℂ) (β : ℝ) (c : ι → ℝ)
    (S : Matrix (FourSpin n) (FourSpin n) ℂ) (i : ι) := μ A c S i / r A β c S i
def P (A : ι → Matrix n n ℂ) (β : ℝ) (c : ι → ℝ)
    (S : Matrix (FourSpin n) (FourSpin n) ℂ) := balancedDensity (density A S) (transport A β c S)

theorem masses_pos (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (hne : ∀ i, A i ≠ 0) (k : ℕ) (hk : 1 ≤ k) (c : ι → ℝ) (hc : ∀ i, 0 < c i)
    {S : Matrix (FourSpin n) (FourSpin n) ℂ} (hS : S.PosDef) :
    (∀ i, 0 < μ A c S i) ∧ (∀ i, 0 < r A ((1 : ℝ) / 2 ^ k) c S i) := by
  have hp := carrierMass_pos (probe A) (probe_posSemidef A hA)
    (fun i => probe_ne_zero A hA i (hne i)) (density_posDef A hS)
  have hZ := transport_posDef A hA hc hS k hk
  have hτ := transportMass_pos (term A ((1 : ℝ) / 2 ^ k) S)
    (term_posSemidef A _ hS.posSemidef)
    (fun i => term_ne_zero A hA hS k hk i (hne i)) hZ
  exact ⟨coefficientMass_pos _ _ _ hc hp, probeScale_pos _ _ _ _ _ hc hp hτ⟩

theorem frame_properties (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (hne : ∀ i, A i ≠ 0) (k : ℕ) (hk : 1 ≤ k) (c : ι → ℝ) (hc : ∀ i, 0 < c i)
    (x : ι → ℝ) {S : Matrix (FourSpin n) (FourSpin n) ℂ} (hS : S.PosDef) :
    let β := (1 : ℝ) / 2 ^ k
    (∀ i, (E A β c S i).PosSemidef) ∧
    (∀ i, (F A β c S i).PosSemidef) ∧
    (∀ i, (N A β c x S i).IsHermitian) ∧
    (∀ i, realTrace (F A β c S i) = r A β c S i) ∧
    P A β c S = TwoFrames.frameSum (F A β c S) (μ A c S) ∧
    (∀ i, realTrace (E A β c S i * P A β c S) = μ A c S i) := by
  dsimp only
  have hp := carrierMass_pos (probe A) (probe_posSemidef A hA)
    (fun i => probe_ne_zero A hA i (hne i)) (density_posDef A hS)
  have hZ := transport_posDef A hA hc hS k hk
  refine ⟨measurementFrame_posSemidef _ (probe_posSemidef A hA) _ _,
    preparationFrame_posSemidef _ _ (term_posSemidef A _ hS.posSemidef) _ _ _
      (fun i => (hp i).le), ?_, trace_preparationFrame _ _ _ _ hZ, ?_,
    measurement_pairing _ _ _ hZ⟩
  · intro i
    exact IsSelfAdjoint.smul (show IsSelfAdjoint (Real.sqrt (c i)) from rfl)
      (balancedKraus_isHermitian (force A x) (force_isHermitian A hA x) _ i)
  · apply balancedDensity_eq_frameSum _ _ _ (fun i => (hc i).le) hZ (fun i => (hp i).ne')
    rw [← compressedSource_eq_sum]
    exact transport_equation A hA hc hS k hk

/-- Both response frames have their actual source-probe diagonal budgets. -/
theorem frame_diagonals (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (hne : ∀ i, A i ≠ 0) (k : ℕ) (hk : 1 ≤ k) (c : ι → ℝ) (hc : ∀ i, 0 < c i)
    (x : ι → ℝ) (hx : ∀ i, |x i| ≤ 1)
    {S : Matrix (FourSpin n) (FourSpin n) ℂ} (hS : S.PosDef) :
    let β := (1 : ℝ) / 2 ^ k
    (∀ i, realTrace (P A β c S * E A β c S i * E A β c S i) / R A β c S i ≤
      4 * r A β c S i ^ 2) ∧
    (∀ i, realTrace (P A β c S * N A β c x S i * N A β c x S i) / R A β c S i ≤
      16 * r A β c S i ^ 2) := by
  dsimp only
  have hp := carrierMass_pos (probe A) (probe_posSemidef A hA)
    (fun i => probe_ne_zero A hA i (hne i)) (density_posDef A hS)
  have hZ := transport_posDef A hA hc hS k hk
  have hτ := transportMass_pos (term A ((1 : ℝ) / 2 ^ k) S)
    (term_posSemidef A _ hS.posSemidef)
    (fun i => term_ne_zero A hA hS k hk i (hne i)) hZ
  have hβ : 0 ≤ (1 : ℝ) / 2 ^ k := by positivity
  have hβ1 : (1 : ℝ) / 2 ^ k ≤ 1 :=
    (div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num))
  constructor
  · exact weighted_force_diagonal_le _ _ _ c hc _ hZ hp hτ 4
      (actual_supported_probe_bound A hA hS.posSemidef hZ.posSemidef hβ hβ1)
  · exact weighted_force_diagonal_le _ _ _ c hc _ hZ hp hτ 16
      (actual_supported_force_bound A hA x hx hS.posSemidef hZ.posSemidef hβ hβ1)

end Frames
end AugmentedHigherRankKS
