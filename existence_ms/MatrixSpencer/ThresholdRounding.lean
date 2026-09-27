import MatrixSpencer.Statement
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-!
# Finite threshold rounding of cube coordinates

Boundary-layer coordinates are rounded to a real sign. The statements use
explicit coordinate absolute values and the Euclidean norm; no default Pi
norm is used for the squared-norm ledger. Total rounding cost is charged to
the actual coordinates changed, each of which can be charged at most once.
-/

open scoped BigOperators

noncomputable section
namespace MatrixSpencer
namespace ThresholdRounding

def boundarySign (x : ℝ) : ℝ := if 0 ≤ x then 1 else -1

def roundScalar (ε x : ℝ) : ℝ := if 1 - ε ≤ |x| then boundarySign x else x

lemma boundarySign_isSign (x : ℝ) : IsSign (boundarySign x) := by
  unfold boundarySign IsSign
  split_ifs <;> simp

lemma abs_boundarySign (x : ℝ) : |boundarySign x| = 1 := by
  rcases boundarySign_isSign x with h | h <;> simp [h]

lemma boundarySign_sq (x : ℝ) : boundarySign x ^ 2 = 1 := by
  rcases boundarySign_isSign x with h | h <;> simp [h]

lemma abs_boundarySign_sub {x : ℝ} (hx : |x| ≤ 1) :
    |boundarySign x - x| = 1 - |x| := by
  rcases abs_le.mp hx with ⟨hlo, hhi⟩
  by_cases hzero : 0 ≤ x
  · simp only [boundarySign, if_pos hzero, abs_of_nonneg hzero,
      abs_of_nonneg (sub_nonneg.mpr hhi)]
  · have hxneg : x ≤ 0 := le_of_lt (lt_of_not_ge hzero)
    have hdiff : -1 - x ≤ 0 := by linarith
    simp only [boundarySign, if_neg hzero, abs_of_nonpos hxneg, abs_of_nonpos hdiff]
    ring

lemma roundScalar_eq_of_interior {ε x : ℝ} (hx : |x| < 1 - ε) : roundScalar ε x = x := by
  simp [roundScalar, not_le.mpr hx]

lemma roundScalar_isSign_of_boundary {ε x : ℝ} (hx : 1 - ε ≤ |x|) :
    IsSign (roundScalar ε x) := by
  simpa only [roundScalar, if_pos hx] using boundarySign_isSign x

lemma roundScalar_isSign_of_changed {ε x : ℝ} (hx : roundScalar ε x ≠ x) :
    IsSign (roundScalar ε x) := by
  by_cases hb : 1 - ε ≤ |x|
  · exact roundScalar_isSign_of_boundary hb
  · exact False.elim (hx (by simp [roundScalar, hb]))

/-- After cleanup a coordinate is frozen at a sign or is strictly inside the live region. -/
lemma roundScalar_sign_or_interior (ε x : ℝ) :
    IsSign (roundScalar ε x) ∨ |roundScalar ε x| < 1 - ε := by
  by_cases hb : 1 - ε ≤ |x|
  · exact Or.inl (roundScalar_isSign_of_boundary hb)
  · right
    simpa only [roundScalar, if_neg hb] using lt_of_not_ge hb

lemma roundScalar_of_isSign (ε : ℝ) {x : ℝ} (hx : IsSign x) : roundScalar ε x = x := by
  rcases hx with rfl | rfl <;> simp [roundScalar, boundarySign]

lemma roundScalar_abs_le {ε x : ℝ} (hx : |x| ≤ 1) : |roundScalar ε x| ≤ 1 := by
  unfold roundScalar
  split_ifs
  · exact (abs_boundarySign x).le
  · exact hx

lemma roundScalar_cost_le {ε x : ℝ} (hε : 0 ≤ ε) (hx : |x| ≤ 1) :
    |roundScalar ε x - x| ≤ ε := by
  unfold roundScalar
  split_ifs with hb
  · rw [abs_boundarySign_sub hx]
    linarith
  · simpa only [sub_self, abs_zero] using hε

lemma roundScalar_sq_ge {ε x : ℝ} (hx : |x| ≤ 1) : x ^ 2 ≤ roundScalar ε x ^ 2 := by
  unfold roundScalar
  split_ifs
  · rw [boundarySign_sq]
    nlinarith [sq_abs x, abs_nonneg x]
  · exact le_rfl

lemma roundScalar_idempotent (ε x : ℝ) : roundScalar ε (roundScalar ε x) = roundScalar ε x := by
  by_cases hc : roundScalar ε x = x
  · rw [hc, hc]
  · exact roundScalar_of_isSign ε (roundScalar_isSign_of_changed hc)

variable {ι : Type*} [Fintype ι]

/-- Round every coordinate currently in the boundary layer. -/
def roundVector (ε : ℝ) (x : ι → ℝ) : ι → ℝ := fun i => roundScalar ε (x i)

omit [Fintype ι] in
lemma roundVector_cube {ε : ℝ} {x : ι → ℝ} (hx : ∀ i, |x i| ≤ 1) :
    ∀ i, |roundVector ε x i| ≤ 1 := fun i => roundScalar_abs_le (hx i)

omit [Fintype ι] in
lemma roundVector_frozen {ε : ℝ} {x : ι → ℝ} {i : ι} (hx : IsSign (x i)) :
    roundVector ε x i = x i := roundScalar_of_isSign ε hx

lemma roundVector_cost_le {ε : ℝ} (hε : 0 ≤ ε) {x : ι → ℝ} (hx : ∀ i, |x i| ≤ 1) :
    ∑ i, |roundVector ε x i - x i| ≤ Fintype.card ι * ε := by
  calc
    _ ≤ ∑ _i : ι, ε := Finset.sum_le_sum (fun i _ => roundScalar_cost_le hε (hx i))
    _ = _ := by simp

/-- Squared coordinate norm never decreases under threshold rounding. -/
lemma roundVector_sum_sq_ge {ε : ℝ} {x : ι → ℝ} (hx : ∀ i, |x i| ≤ 1) :
    ∑ i, x i ^ 2 ≤ ∑ i, roundVector ε x i ^ 2 :=
  Finset.sum_le_sum (fun i _ => roundScalar_sq_ge (hx i))

/-- The norm ledger uses the Euclidean norm, with its exact sum-of-squares formula. -/
lemma roundVector_euclidean_norm_sq_ge {ε : ℝ} {x : EuclideanSpace ℝ ι}
    (hx : ∀ i, |x i| ≤ 1) :
    ‖x‖ ^ 2 ≤ ‖WithLp.toLp 2 (roundVector ε (WithLp.ofLp x))‖ ^ 2 := by
  simpa only [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs] using
    roundVector_sum_sq_ge hx

omit [Fintype ι] in
/-- A bounded move in each live coordinate preserves the full cube. -/
lemma move_cube {x v : ι → ℝ} {ε s : ℝ} {frozen : Set ι}
    (hfrozen : ∀ i ∈ frozen, |x i| ≤ 1 ∧ v i = 0)
    (hlive : ∀ i ∉ frozen, |x i| ≤ 1 - ε)
    (hstep : ∀ i ∉ frozen, |s| * |v i| ≤ ε) :
    ∀ i, |x i + s * v i| ≤ 1 := by
  intro i
  by_cases hi : i ∈ frozen
  · simpa only [(hfrozen i hi).2, mul_zero, add_zero] using (hfrozen i hi).1
  · calc
      _ ≤ |x i| + |s * v i| := abs_add_le _ _
      _ = |x i| + |s| * |v i| := by rw [abs_mul]
      _ ≤ 1 := by linarith [hlive i hi, hstep i hi]

omit [Fintype ι] in
/-- The entire scalar interpolation obeys the same movement bound. -/
lemma interpolation_cube {x v : ι → ℝ} {ε h s : ℝ} {frozen : Set ι}
    (hfrozen : ∀ i ∈ frozen, |x i| ≤ 1 ∧ v i = 0)
    (hlive : ∀ i ∉ frozen, |x i| ≤ 1 - ε)
    (hstep : ∀ i ∉ frozen, h * |v i| ≤ ε) (hs : |s| ≤ h) :
    ∀ i, |x i + s * v i| ≤ 1 :=
  move_cube hfrozen hlive (fun i hi =>
    (mul_le_mul_of_nonneg_right hs (abs_nonneg _)).trans (hstep i hi))

/-- Changed coordinates are the only coordinates that incur rounding cost. -/
lemma roundScalar_cost_le_indicator {ε x : ℝ} (hε : 0 ≤ ε) (hx : |x| ≤ 1) :
    |roundScalar ε x - x| ≤ ε * (if roundScalar ε x ≠ x then (1 : ℝ) else 0) := by
  by_cases hc : roundScalar ε x = x
  · simp [hc]
  · simpa [hc] using roundScalar_cost_le hε hx

omit [Fintype ι] in
/-- At most one charged rounding of a fixed coordinate costs at most one epsilon. -/
lemma coordinate_total_cost_le (x : ℕ → ι → ℝ) {ε : ℝ} (hε : 0 ≤ ε) (N : ℕ) (i : ι)
    (hx : ∀ j < N, |x j i| ≤ 1)
    (honce : ∀ j < N, ∀ k < N,
      roundScalar ε (x j i) ≠ x j i → roundScalar ε (x k i) ≠ x k i → j = k) :
    ∑ j ∈ Finset.range N, |roundScalar ε (x j i) - x j i| ≤ ε := by
  let S := (Finset.range N).filter (fun j => roundScalar ε (x j i) ≠ x j i)
  have hc : S.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro j hj k hk
    exact honce j (Finset.mem_range.mp (Finset.mem_filter.mp hj).1)
      k (Finset.mem_range.mp (Finset.mem_filter.mp hk).1)
      (Finset.mem_filter.mp hj).2 (Finset.mem_filter.mp hk).2
  calc
    _ ≤ ∑ j ∈ Finset.range N, ε * (if roundScalar ε (x j i) ≠ x j i then (1 : ℝ) else 0) :=
      Finset.sum_le_sum (fun j hj => roundScalar_cost_le_indicator hε (hx j (Finset.mem_range.mp hj)))
    _ = ε * S.card := by rw [← Finset.mul_sum, Finset.sum_boole]
    _ ≤ ε * 1 := mul_le_mul_of_nonneg_left (by exact_mod_cast hc) hε
    _ = ε := mul_one _

/-- Global finite rounding charge: each coordinate is charged at most once. -/
lemma total_rounding_cost_le (x : ℕ → ι → ℝ) {ε : ℝ} (hε : 0 ≤ ε) (N : ℕ)
    (hx : ∀ j < N, ∀ i, |x j i| ≤ 1)
    (honce : ∀ i, ∀ j < N, ∀ k < N,
      roundScalar ε (x j i) ≠ x j i → roundScalar ε (x k i) ≠ x k i → j = k) :
    ∑ j ∈ Finset.range N, ∑ i, |roundVector ε (x j) i - x j i| ≤ Fintype.card ι * ε := by
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ _i : ι, ε := Finset.sum_le_sum (fun i _ =>
      coordinate_total_cost_le x hε N i (fun j hj => hx j hj i) (honce i))
    _ = _ := by simp

omit [Fintype ι] in
/-- Permanent freezing after a changed rounding implies the at-most-once charging condition. -/
lemma at_most_once_of_frozen_persistence (x : ℕ → ι → ℝ) (ε : ℝ) (N : ℕ)
    (hpersist : ∀ i, ∀ j < N, ∀ k < N, j < k →
      roundScalar ε (x j i) ≠ x j i → x k i = roundScalar ε (x j i)) :
    ∀ i, ∀ j < N, ∀ k < N,
      roundScalar ε (x j i) ≠ x j i → roundScalar ε (x k i) ≠ x k i → j = k := by
  intro i j hj k hk hcj hck
  rcases lt_trichotomy j k with hjk | hjk | hjk
  · have hp := hpersist i j hj k hk hjk hcj
    exact False.elim (hck (by rw [hp, roundScalar_idempotent]))
  · exact hjk
  · have hp := hpersist i k hk j hj hjk hck
    exact False.elim (hcj (by rw [hp, roundScalar_idempotent]))

/-- The total bound with the charging condition discharged by actual frozen persistence. -/
lemma total_rounding_cost_le_of_frozen_persistence (x : ℕ → ι → ℝ) {ε : ℝ}
    (hε : 0 ≤ ε) (N : ℕ) (hx : ∀ j < N, ∀ i, |x j i| ≤ 1)
    (hpersist : ∀ i, ∀ j < N, ∀ k < N, j < k →
      roundScalar ε (x j i) ≠ x j i → x k i = roundScalar ε (x j i)) :
    ∑ j ∈ Finset.range N, ∑ i, |roundVector ε (x j) i - x j i| ≤ Fintype.card ι * ε :=
  total_rounding_cost_le x hε N hx (at_most_once_of_frozen_persistence x ε N hpersist)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A contraction family converts coefficient l1 distance to discrepancy norm. -/
lemma combination_norm_sub_le_l1 (A : ι → E) (hA : ∀ i, ‖A i‖ ≤ 1) (x y : ι → ℝ) :
    ‖(∑ i, y i • A i) - ∑ i, x i • A i‖ ≤ ∑ i, |y i - x i| := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, ‖y i • A i - x i • A i‖ := norm_sum_le _ _
    _ ≤ ∑ i, |y i - x i| := by
      apply Finset.sum_le_sum
      intro i _
      rw [← sub_smul, norm_smul, Real.norm_eq_abs]
      exact mul_le_of_le_one_right (abs_nonneg _) (hA i)

lemma rounding_combination_norm_le (A : ι → E) (hA : ∀ i, ‖A i‖ ≤ 1)
    {ε : ℝ} (hε : 0 ≤ ε) {x : ι → ℝ} (hx : ∀ i, |x i| ≤ 1) :
    ‖(∑ i, roundVector ε x i • A i) - ∑ i, x i • A i‖ ≤ Fintype.card ι * ε :=
  (combination_norm_sub_le_l1 A hA x (roundVector ε x)).trans (roundVector_cost_le hε hx)

/-- The cumulative discrepancy norm charge has the same global rounding budget. -/
lemma total_rounding_combination_norm_le (A : ι → E) (hA : ∀ i, ‖A i‖ ≤ 1)
    (x : ℕ → ι → ℝ) {ε : ℝ} (hε : 0 ≤ ε) (N : ℕ)
    (hx : ∀ j < N, ∀ i, |x j i| ≤ 1)
    (hpersist : ∀ i, ∀ j < N, ∀ k < N, j < k →
      roundScalar ε (x j i) ≠ x j i → x k i = roundScalar ε (x j i)) :
    ∑ j ∈ Finset.range N,
      ‖(∑ i, roundVector ε (x j) i • A i) - ∑ i, x j i • A i‖ ≤ Fintype.card ι * ε := by
  apply le_trans (Finset.sum_le_sum (fun j _ =>
    combination_norm_sub_le_l1 A hA (x j) (roundVector ε (x j))))
  exact total_rounding_cost_le_of_frozen_persistence x hε N hx hpersist

end ThresholdRounding
end MatrixSpencer
