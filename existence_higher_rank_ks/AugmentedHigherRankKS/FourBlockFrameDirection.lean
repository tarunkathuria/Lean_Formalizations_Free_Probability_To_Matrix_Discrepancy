import AugmentedHigherRankKS.IndependentFrameDirection
import AugmentedHigherRankKS.FourBlockFrames

/-! The legal direction is derived from the actual four-block source. -/
noncomputable section
open Matrix MatrixSpencer HigherRankKS MatrixSpencer.KSFisher
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace AugmentedHigherRankKS.Frames
variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [Fintype n] [DecidableEq n]
open TwoFrames

def direction (c y : ι → ℝ) (i : ι) : ℝ := Real.sqrt (c i) * y i

theorem direction_ne_zero (c : ι → ℝ) (hc : ∀ i, 0 < c i) {y : ι → ℝ}
    (hy : y ≠ 0) : direction c y ≠ 0 := by
  intro he
  apply hy
  funext i
  exact (mul_eq_zero.mp (congrFun he i)).resolve_left (Real.sqrt_pos.mpr (hc i)).ne'

theorem debit_eq (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (hne : ∀ i, A i ≠ 0) (c : ι → ℝ) (hc : ∀ i, 0 < c i) (β : ℝ)
    {S : Matrix (FourSpin n) (FourSpin n) ℂ} (hS : S.PosDef) (y : ι → ℝ) :
    (∑ i, μ A c S i * r A β c S i * y i ^ 2) =
      ∑ i, BalancedFrames.transportMass (SupportedSpin.term A β S)
        (SupportedSpin.transport A β c S) i * direction c y i ^ 2 := by
  apply Finset.sum_congr rfl
  intro i _
  have hp := BalancedFrames.carrierMass_pos (SupportedSpin.probe A)
    (SupportedSpin.probe_posSemidef A hA)
    (fun j => SupportedSpin.probe_ne_zero A hA j (hne j)) (SupportedSpin.density_posDef A hS) i
  dsimp only [μ, r, BalancedFrames.coefficientMass, BalancedFrames.probeScale, direction]
  field_simp [hp.ne']

/-- An actual legal response direction, with a half-reserve margin retained for runtime. -/
theorem exists_direction (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (hne : ∀ i, A i ≠ 0) (k : ℕ) (hk : 1 ≤ k) (c : ι → ℝ) (hc : ∀ i, 0 < c i)
    (x z : ι → ℝ) (hx : ∀ i, |x i| ≤ 1)
    {S : Matrix (FourSpin n) (FourSpin n) ℂ} (hS : S.PosDef)
    (hcap : ∀ i, r A ((1 : ℝ) / 2 ^ k) c S i ^ 2 ≤ 1 / 48)
    {a : ℝ} (ha : 120 / ((1 : ℝ) / 2 ^ k) ≤ a) :
    let β := (1 : ℝ) / 2 ^ k
    let σ := 2 * β / (1 + β)
    ∃ ω y : ι → ℝ, direction c y ≠ 0 ∧
      (1 - (channel (E A β c S) (F A β c S))ᵀ) *ᵥ ω =
        (channel (N A β c x S) (F A β c S))ᵀ *ᵥ y ∧
      (∑ i, z i * direction c y i) = 0 ∧
      realTrace (P A β c S * (IndependentLegalResponse.trial (E A β c S) (N A β c x S) ω y *
        IndependentLegalResponse.trial (E A β c S) (N A β c x S) ω y)) / σ <
        (a / 2) * ∑ i, BalancedFrames.transportMass (SupportedSpin.term A β S)
          (SupportedSpin.transport A β c S) i * direction c y i ^ 2 := by
  dsimp only
  let β := (1 : ℝ) / 2 ^ k
  have hb : 0 < β := by positivity
  have hb2 : β ≤ 1 / 2 := by
    dsimp only [β]
    apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
    exact le_self_pow₀ (by norm_num) (by omega)
  have hσ : 4 * β / 3 ≤ 2 * β / (1 + β) := by
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith
  have ha2 : 60 / β ≤ a / 2 := by
    change 120 / β ≤ a at ha
    rw [show 60 / β = (120 / β) / 2 by ring]
    linarith
  obtain ⟨hE, hF, hN, htrace, hP, hpair⟩ := frame_properties A hA hne k hk c hc x hS
  obtain ⟨hμ, hr⟩ := masses_pos A hA hne k hk c hc hS
  obtain ⟨hEd, hNd⟩ := frame_diagonals A hA hne k hk c hc x hx hS
  rw [hP] at hpair hEd hNd
  obtain ⟨ω, y, hy, hlegal, hz, hneg⟩ := IndependentFrameDirection.exists_direction
    (E A β c S) (F A β c S) (N A β c x S) hE hF hN hμ hr htrace hpair
    hEd hNd hcap hb hσ ha2 (fun i => z i * Real.sqrt (c i))
  refine ⟨ω, y, direction_ne_zero c hc hy, hlegal, ?_, ?_⟩
  · simpa only [direction, mul_assoc] using hz
  · rw [← hP, debit_eq A hA hne c hc β hS y] at hneg
    linarith

end AugmentedHigherRankKS.Frames
