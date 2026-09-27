import HigherRankKS.LegalResponse

/-! Adjoint transport trials for arbitrary Hermitian coefficient forces. -/
noncomputable section
open Matrix MatrixSpencer HigherRankKS MatrixSpencer.KSFisher
open scoped BigOperators MatrixOrder ComplexOrder
namespace AugmentedHigherRankKS.IndependentLegalResponse
variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
open HigherRankKS.TwoFrames

def trial (E N : ι → Matrix n n ℂ) (ω y : ι → ℝ) : Matrix n n ℂ :=
  synthesis N y + synthesis E ω

theorem measurement_trial (E F N : ι → Matrix n n ℂ) (ω y : ι → ℝ)
    (hlegal : (1 - (channel E F)ᵀ) *ᵥ ω = (channel N F)ᵀ *ᵥ y) :
    measurement F (trial E N ω y) = ω := by
  funext i
  have h := congrFun hlegal i
  simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply,
    channel_transpose_mulVec] at h
  simp only [measurement, trial, Matrix.mul_add, realTrace_add]
  linarith

theorem trial_equation (E F N : ι → Matrix n n ℂ) (ω y : ι → ℝ)
    (hlegal : (1 - (channel E F)ᵀ) *ᵥ ω = (channel N F)ᵀ *ᵥ y) :
    trial E N ω y - frameChannel F E (trial E N ω y) = synthesis N y := by
  rw [frameChannel, measurement_trial E F N ω y hlegal, trial, add_sub_cancel_right]

/-- The legal equation pays the full force pairing by the inverse-Sylvester quadratic. -/
theorem response_le (E F N : ι → Matrix n n ℂ)
    (hE : ∀ i, (E i).IsHermitian) (hF : ∀ i, (F i).IsHermitian)
    (hN : ∀ i, (N i).IsHermitian) (P : Matrix n n ℂ) (hP : P.PosDef)
    (ω y : ι → ℝ)
    (hlegal : (1 - (channel E F)ᵀ) *ᵥ ω = (channel N F)ᵀ *ᵥ y)
    {σ : ℝ} (hσ : 0 < σ) {Y : Matrix n n ℂ} (hY : Y.IsHermitian) :
    realTrace (synthesis N y * Y) -
      σ / 2 * SylvesterMetric.energy P hP (Y - frameChannel E F Y) ≤
      realTrace (P * (trial E N ω y * trial E N ω y)) / σ := by
  have hU := (synthesis_isHermitian N hN y).add (synthesis_isHermitian E hE ω)
  have hW := hY.sub (synthesis_isHermitian F hF (measurement E Y))
  have hb := SylvesterMetric.shifted_response_le P hP hU hW
    (Matrix.isHermitian_zero : (0 : Matrix n n ℂ).IsHermitian) hσ
  simp only [sub_zero, Matrix.mul_zero, realTrace_zero, add_zero] at hb
  change realTrace (trial E N ω y * (Y - frameChannel E F Y)) -
    σ / 2 * SylvesterMetric.energy P hP (Y - frameChannel E F Y) ≤
    realTrace (P * (trial E N ω y * trial E N ω y)) / σ at hb
  rw [← adjoint_force_pairing, trial_equation E F N ω y hlegal] at hb
  exact hb

end AugmentedHigherRankKS.IndependentLegalResponse
