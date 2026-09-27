import MatrixSpencer.MSManuscriptNumericalEpochRun

/-! A bound on the actual fixed-mesh loop budget. This accounts for the cube,
Taylor and time caps in the defined mesh. It is a parameter bound, not a
whole-program operation count or a claim that the derivative budget has
already been bounded polynomially in the original input size. -/
noncomputable section
namespace MatrixSpencer.MSManuscriptNumericalWalkBudget
open MSManuscriptNumericalEpochRun MSManuscriptNumericalEpochLedger
variable {N d : ℕ}
set_option maxHeartbeats 800000

def fourthBudget (c : Config N d) : ℝ :=
  MSManuscriptMovementDrift.uniformBudget N d
    (MSManuscriptEpochInput.centerCap c.offset (N := N)) c.regularizer c.floor

theorem fourthBudget_pos (c : Config N d) : 0 < fourthBudget c := by
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp c.dimension_pos
  exact MSManuscriptMovementDrift.uniformBudget_pos
    (MSManuscriptEpochInput.centerCap_pos c.offset (N := N)).le c.regularizer_pos

private theorem inv_square_min (x y : ℝ) :
    1 / (min x y)^2 ≤ 1/x^2 + 1/y^2 := by
  rcases le_total x y with h | h
  · rw [min_eq_left h]
    exact le_add_of_nonneg_right (by positivity)
  · rw [min_eq_right h]
    exact le_add_of_nonneg_left (by positivity)

theorem mesh_inverse_square_le (c : Config N d) :
    1/(mesh c)^2 ≤ ((N : ℝ)+1)/c.margin^2 + 4 +
      4/(MSManuscriptMatchedInterval.radius c.floor)^2 +
      fourthBudget c/(24*c.driftError) + 2/timeLimit := by
  let a := c.margin/Real.sqrt ((N : ℝ)+1)
  let b := MSManuscriptMatchedInterval.radius c.floor/2
  let q := Real.sqrt (24*c.driftError/fourthBudget c)
  have hq := inv_square_min b q
  have hhalf := inv_square_min (1/2) (min b q)
  have hcube := inv_square_min a (min (1/2) (min b q))
  have htime := inv_square_min (min a (min (1/2) (min b q))) (Real.sqrt (timeLimit/2))
  have ha : 1/a^2 = ((N : ℝ)+1)/c.margin^2 := by
    dsimp [a]
    rw [div_pow, Real.sq_sqrt (by positivity)]
    field_simp
  have hb : 1/b^2 = 4/(MSManuscriptMatchedInterval.radius c.floor)^2 := by
    dsimp [b]
    field_simp
    <;> ring
  have hqeq : 1/q^2 = fourthBudget c/(24*c.driftError) := by
    dsimp [q]
    rw [Real.sq_sqrt (div_nonneg (mul_nonneg (by norm_num) c.driftError_pos.le) (fourthBudget_pos c).le)]
    field_simp
  have hteq : 1/(Real.sqrt (timeLimit/2))^2 = 2/timeLimit := by
    norm_num [timeLimit]
  have hm : mesh c = min a (min (1/2) (min b q)) ⊓ Real.sqrt (timeLimit/2) := rfl
  rw [hm]
  change 1/(min (min a (min (1/2) (min b q))) (Real.sqrt (timeLimit/2)))^2 ≤ _
  rw [ha] at hcube
  rw [hb, hqeq] at hq
  rw [hteq] at htime
  rw [show (1 : ℝ)/(1/2)^2 = 4 by norm_num] at hhalf
  linarith

theorem count_le (c : Config N d) :
    (count c : ℝ) ≤ timeLimit *
      (((N : ℝ)+1)/c.margin^2 + 4 +
        4/(MSManuscriptMatchedInterval.radius c.floor)^2 +
        fourthBudget c/(24*c.driftError)) + 3 := by
  have hf := Nat.floor_le (show 0 ≤ timeLimit/(mesh c)^2 by
    exact div_nonneg (by norm_num [timeLimit]) (sq_nonneg _))
  have hm := mul_le_mul_of_nonneg_left (mesh_inverse_square_le c)
    (show 0 ≤ timeLimit by norm_num [timeLimit])
  change (count c : ℝ) ≤ _
  dsimp only [count]
  push_cast
  have ht : timeLimit*(2/timeLimit) = 2 := by norm_num [timeLimit]
  rw [mul_add, ht] at hm
  rw [mul_one_div] at hm
  linarith

end MatrixSpencer.MSManuscriptNumericalWalkBudget
