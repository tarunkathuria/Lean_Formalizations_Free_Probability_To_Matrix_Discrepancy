import MatrixSpencer.KSFullManuscriptParameters


noncomputable section
namespace MatrixSpencer.KSFullManuscriptWalkBudget
open KSFullManuscriptParameters

theorem cutoff_le {N : ℕ} (hN : 0 < N) {δ M : ℝ} (hδ : 0 < δ) (hM : 0 < M) :
    (cutoff N δ M : ℝ) ≤ 256*N/δ^2 + 100*(N : ℝ)^2*M/δ + 1 := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hκ := curvatureTolerance_pos hN hδ
  have ht := movementStep_pos hN hδ hM
  have hc := (Nat.ceil_lt_add_one (by positivity : 0 ≤ 16*(N : ℝ)/movementStep N δ M^2)).le
  change (cutoff N δ M : ℝ) ≤ 16*(N : ℝ)/movementStep N δ M^2+1 at hc
  apply hc.trans
  apply add_le_add_right
  by_cases hs : δ/4 ≤ Real.sqrt (24*curvatureTolerance N δ/M)
  · rw [movementStep,min_eq_left hs]
    have he : 16*(N : ℝ)/(δ/4)^2 = 256*N/δ^2 := by field_simp; ring
    rw [he]
    exact le_add_of_nonneg_right (by positivity)
  · rw [movementStep,min_eq_right (le_of_not_ge hs),Real.sq_sqrt (by positivity)]
    have he : 16*(N : ℝ)/(24*curvatureTolerance N δ/M) = (200/3 : ℝ)*(N : ℝ)^2*M/δ := by
      unfold curvatureTolerance
      field_simp
      <;> ring
    rw [he]
    have hq : 0 ≤ (N : ℝ)^2*M/δ := by positivity
    have hd : 0 ≤ 256*(N : ℝ)/δ^2 := by positivity
    ring_nf at hq hd ⊢
    nlinarith

end MatrixSpencer.KSFullManuscriptWalkBudget
