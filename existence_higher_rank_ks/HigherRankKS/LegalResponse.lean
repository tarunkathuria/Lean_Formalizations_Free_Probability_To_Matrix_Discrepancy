import HigherRankKS.TwoFrameFisher
import HigherRankKS.SourceMetricAbsorption

/-!
# The adjoint transport trial

The coefficient equation uses the transpose of the two-frame channel.
It constructs a trial for the actual Sylvester quadratic without an
inverse or a spectral-gap assumption on the channel.
-/

open Matrix MatrixSpencer MatrixSpencer.KSFisher
open scoped BigOperators MatrixOrder ComplexOrder

noncomputable section
namespace HigherRankKS.TwoFrames

variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]

def measurement (E : ι → Matrix n n ℂ) (Y : Matrix n n ℂ) : ι → ℝ :=
  fun i => realTrace (E i * Y)

def frameChannel (E F : ι → Matrix n n ℂ) (Y : Matrix n n ℂ) : Matrix n n ℂ :=
  synthesis F (measurement E Y)

omit [DecidableEq ι] [DecidableEq n] in
theorem trace_synthesis (E : ι → Matrix n n ℂ) (a : ι → ℝ) (Y : Matrix n n ℂ) :
    realTrace (synthesis E a * Y) = a ⬝ᵥ measurement E Y := by
  simp only [synthesis, Matrix.sum_mul, Matrix.smul_mul, realTrace_sum, realTrace_smul,
    dotProduct, measurement]

omit [DecidableEq ι] [DecidableEq n] in
theorem frameChannel_trace_adjoint (E F : ι → Matrix n n ℂ) (U Y : Matrix n n ℂ) :
    realTrace (frameChannel F E U * Y) = realTrace (U * frameChannel E F Y) := by
  rw [frameChannel, trace_synthesis, realTrace_mul_comm U, frameChannel, trace_synthesis,
    dotProduct_comm]

def transportTrial (J : Matrix n n ℂ) (E : ι → Matrix n n ℂ)
    (z ω y : ι → ℝ) : Matrix n n ℂ :=
  J * synthesis E y - synthesis E (Matrix.diagonal z *ᵥ y) + synthesis E ω

theorem measurement_transportTrial (E F : ι → Matrix n n ℂ)
    (J : Matrix n n ℂ) (z ω y : ι → ℝ)
    (hlegal : (1 - (channel E F)ᵀ) *ᵥ ω =
      ((spinChannel J E F)ᵀ - (channel E F)ᵀ * Matrix.diagonal z) *ᵥ y) :
    measurement F (transportTrial J E z ω y) = ω := by
  have he (i : ι) := congrFun hlegal i
  funext i
  simp only [Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec,
    Pi.sub_apply, channel_transpose_mulVec, spinChannel_transpose_mulVec] at he
  simp only [measurement, transportTrial, Matrix.mul_add, Matrix.mul_sub,
    realTrace_add, realTrace_sub]
  linarith [he i]

theorem transportTrial_adjoint_equation (E F : ι → Matrix n n ℂ)
    (J : Matrix n n ℂ) (z ω y : ι → ℝ)
    (hlegal : (1 - (channel E F)ᵀ) *ᵥ ω =
      ((spinChannel J E F)ᵀ - (channel E F)ᵀ * Matrix.diagonal z) *ᵥ y) :
    transportTrial J E z ω y - frameChannel F E (transportTrial J E z ω y) =
      J * synthesis E y - synthesis E (Matrix.diagonal z *ᵥ y) := by
  rw [frameChannel, measurement_transportTrial E F J z ω y hlegal, transportTrial,
    add_sub_cancel_right]

omit [DecidableEq ι] [DecidableEq n] in
theorem adjoint_force_pairing (E F : ι → Matrix n n ℂ) (U Y : Matrix n n ℂ) :
    realTrace ((U - frameChannel F E U) * Y) =
      realTrace (U * (Y - frameChannel E F Y)) := by
  rw [Matrix.sub_mul, Matrix.mul_sub, realTrace_sub, realTrace_sub,
    frameChannel_trace_adjoint]

end HigherRankKS.TwoFrames

namespace HigherRankKS.SylvesterMetric

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Completing the inverse-Sylvester quadratic after an adjoint trial.
The mixed source term has no factor of the reciprocal of beta. -/
theorem shifted_response_le (P : Matrix n n ℂ) (hP : P.PosDef)
    {U W N : Matrix n n ℂ} (hU : U.IsHermitian)
    (hW : W.IsHermitian) (hN : N.IsHermitian) {β : ℝ} (hβ : 0 < β) :
    realTrace (U * W) - β / 2 * energy P hP (W - N) ≤
      realTrace (P * (U * U)) / β + realTrace (U * N) := by
  have htest : ((1 / β) • U).IsHermitian := by
    simp only [Matrix.IsHermitian, Matrix.conjTranspose_smul, star_trivial, hU.eq]
  have hv := variational_le_energy P hP (hW.sub hN) htest
  have hquad : realTrace (U * sylvester P U) = 2 * realTrace (P * (U * U)) := by
    simp only [sylvester_apply, Matrix.mul_add, realTrace_add]
    have hc := realTrace_mul_comm U (P * U)
    have ht := realTrace_mul_comm (U * U) P
    simp only [Matrix.mul_assoc] at hc ht
    rw [hc, ht]
    ring
  have hsyl : sylvester P ((1 / β) • U) = (1 / β) • sylvester P U :=
    ((sylvester P).restrictScalars ℝ).map_smul _ _
  unfold variational at hv
  rw [hsyl, Matrix.smul_mul, Matrix.mul_smul, realTrace_smul, realTrace_smul,
    Matrix.mul_smul, realTrace_smul, hquad, Matrix.sub_mul, realTrace_sub,
    realTrace_mul_comm W U, realTrace_mul_comm N U] at hv
  have hb := mul_le_mul_of_nonneg_left hv (show 0 ≤ β / 2 by positivity)
  have hid₁ : (β / 2) * (2 * ((1 / β) * (realTrace (U * W) - realTrace (U * N)))) =
      realTrace (U * W) - realTrace (U * N) := by field_simp
  have hid₂ : (β / 2) * ((1 / β) * ((1 / β) *
      (2 * realTrace (P * (U * U))))) = realTrace (P * (U * U)) / β := by field_simp
  rw [mul_sub, hid₁, hid₂] at hb
  linarith

end HigherRankKS.SylvesterMetric

namespace HigherRankKS.TwoFrames

variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]

theorem legal_response_le (E F : ι → Matrix n n ℂ)
    (hE : ∀ i, (E i).IsHermitian) (hF : ∀ i, (F i).IsHermitian)
    {J P : Matrix n n ℂ} (hJ : J.IsHermitian) (hP : P.PosDef)
    (hc : ∀ i, J * E i = E i * J) (R z ω y : ι → ℝ)
    (hlegal : (1 - (channel E F)ᵀ) *ᵥ ω =
      ((spinChannel J E F)ᵀ - (channel E F)ᵀ * Matrix.diagonal z) *ᵥ y)
    {β : ℝ} (hβ : 0 < β) (a : ℝ) {Y : Matrix n n ℂ} (hY : Y.IsHermitian) :
    let W := transportTrial J E z ω y
    let N := (-a) • synthesis F (fun i => R i * z i * y i)
    a * realTrace ((J * synthesis E y - synthesis E (Matrix.diagonal z *ᵥ y)) * Y) -
      β / 2 * SylvesterMetric.energy P hP (Y - frameChannel E F Y - N) ≤
      a ^ 2 / β * realTrace (P * (W * W)) -
        a ^ 2 * (∑ i, ω i * R i * z i * y i) := by
  let W := transportTrial J E z ω y
  let N := (-a) • synthesis F (fun i => R i * z i * y i)
  have hsmul (b : ℝ) {X : Matrix n n ℂ} (hX : X.IsHermitian) :
      (b • X).IsHermitian := by
    simp only [Matrix.IsHermitian, Matrix.conjTranspose_smul, star_trivial, hX.eq]
  have hW : W.IsHermitian :=
    ((spin_synthesis_isHermitian hJ E hE hc y).sub
      (synthesis_isHermitian E hE _)).add (synthesis_isHermitian E hE ω)
  have hN : N.IsHermitian := hsmul _ (synthesis_isHermitian F hF _)
  have hch : (frameChannel E F Y).IsHermitian := synthesis_isHermitian F hF _
  have hb := SylvesterMetric.shifted_response_le P hP (hsmul a hW) (hY.sub hch) hN hβ
  have hforce : realTrace ((a • W) * (Y - frameChannel E F Y)) =
      a * realTrace ((J * synthesis E y - synthesis E (Matrix.diagonal z *ᵥ y)) * Y) := by
    rw [Matrix.smul_mul, realTrace_smul, ← adjoint_force_pairing]
    rw [transportTrial_adjoint_equation E F J z ω y hlegal]
  have hsource : realTrace ((a • W) * N) =
      -(a ^ 2 * ∑ i, ω i * R i * z i * y i) := by
    rw [show N = (-a) • synthesis F (fun i => R i * z i * y i) from rfl]
    simp only [Matrix.smul_mul, Matrix.mul_smul, realTrace_smul]
    rw [realTrace_mul_comm W, trace_synthesis,
      measurement_transportTrial E F J z ω y hlegal]
    have hd : (fun i => R i * z i * y i) ⬝ᵥ ω = ∑ i, ω i * R i * z i * y i := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hd]
    ring
  rw [hforce, hsource] at hb
  simp only [Matrix.smul_mul, Matrix.mul_smul, realTrace_smul] at hb
  convert hb using 1
  ring

end HigherRankKS.TwoFrames
