import HigherRankKS.NormalizedForce
import HigherRankKS.NormalizedOwner

/-! Combining the two source payments with the legal transport trial. -/

open Matrix MatrixSpencer MatrixSpencer.KSFisher MatrixSpencer.KSSpinDrift
open scoped BigOperators MatrixOrder ComplexOrder

noncomputable section
namespace HigherRankKS.ResponseReduction

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- One half of the source curvature pays the scalar residual and the other
half pays the matrix residual. This is the pointwise response estimate,
before maximizing over the density tangent. -/
theorem source_payments (P : Matrix n n ℂ) (hP : P.PosDef)
    {W D : Matrix n n ℂ} (hW : W.IsHermitian) (hD : D.IsHermitian)
    {β C B residual direct force root : ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    (hmetric : SylvesterMetric.energy P hP D ≤ (1 - β) / (2 * β) * C)
    (hscalar : 2 * residual ≤ C / 2 + (2 * (1 - β) / β) * B)
    (hroot : 0 ≤ root) :
    (direct + 2 * force + 2 * residual - C - root -
        SylvesterMetric.energy P hP (W - D)) / 2 ≤
      direct / 2 + (1 - β) / β * B + force -
        β / 2 * SylvesterMetric.energy P hP W := by
  have hb := SylvesterMetric.source_metric_absorption P hP hW hD hβ hβ1 hmetric
  have he : (2 * (1 - β) / β) * B = 2 * ((1 - β) / β * B) := by ring
  rw [he] at hscalar
  linarith

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The normalized pointwise response is bounded by the same concrete
quadratic used in the finite projection average. -/
theorem normalized_legal_bound (E F : ι → Matrix n n ℂ)
    (hE : ∀ i, (E i).IsHermitian) (hF : ∀ i, (F i).IsHermitian)
    {J P : Matrix n n ℂ} (hJ : J.IsHermitian) (hP : P.PosDef)
    (hc : ∀ i, J * E i = E i * J) (R r z ω y : ι → ℝ)
    (hlegal : (1 - (TwoFrames.channel E F)ᵀ) *ᵥ ω =
      ((TwoFrames.spinChannel J E F)ᵀ -
        (TwoFrames.channel E F)ᵀ * Matrix.diagonal z) *ᵥ y)
    {β u : ℝ} (hβ : 0 < β) (hu : 0 < u)
    {Y : Matrix n n ℂ} (hY : Y.IsHermitian) :
    let a := 1 / Real.sqrt u;
    let N := (-a) • synthesis F (fun i => R i * z i * y i);
    -(∑ i, R i * r i ^ 2 * y i ^ 2) -
        (2 / u) * (∑ i, R i * z i ^ 2 * y i ^ 2) +
        a * realTrace ((J * synthesis E y - synthesis E (Matrix.diagonal z *ᵥ y)) * Y) -
        β / 2 * SylvesterMetric.energy P hP (Y - TwoFrames.frameChannel E F Y - N) ≤
      legalUpper ((1 / β) • P) J E R
        (fun i => r i ^ 2 + (2 / u) * z i ^ 2) z u ω y := by
  dsimp only
  have hb := TwoFrames.legal_response_le E F hE hF hJ hP hc R z ω y hlegal hβ
    (1 / Real.sqrt u) hY
  dsimp only at hb
  have ha : (1 / Real.sqrt u) ^ 2 = 1 / u := by
    rw [div_pow, one_pow, Real.sq_sqrt hu.le]
  rw [ha] at hb
  unfold legalUpper
  rw [Matrix.smul_mul, realTrace_smul]
  have hsum : (∑ i, R i * (r i ^ 2 + 2 / u * z i ^ 2) * y i ^ 2) =
      (∑ i, R i * r i ^ 2 * y i ^ 2) +
        (2 / u) * (∑ i, R i * z i ^ 2 * y i ^ 2) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsum]
  change _ ≤ _ at hb
  dsimp only [TwoFrames.transportTrial] at hb
  have he (t : ℝ) : (1 / u) / β * t = (1 / β * t) / u := by ring
  rw [he] at hb
  have hm (t : ℝ) : (1 / u) * t = t / u := by ring
  rw [hm] at hb
  linarith

end HigherRankKS.ResponseReduction
