import MatrixSpencer.RectangularRidgeEpochMoments
import MatrixSpencer.MSManuscriptEpochProbability

/-!
# Actual constant success probability of the constructed ridge epoch

Both moments are proved by the concrete finite numerical walk. Markov's
inequality then controls the original certificate, tangent and cleaning tests.
No favorable event or success probability is an assumption.
-/
open scoped BigOperators
noncomputable section
namespace MatrixSpencer.RectangularRidgeEpochSuccess
open RectangularRidgeEpochInput RectangularRidgeEpochRun RectangularRidgeEpochMoments
variable {N d : ℕ} [Nonempty (Fin d)]
attribute [local instance] Classical.propDecidable
attribute [local irreducible] run

def Good (c : Config N d) (s : MSManuscriptNumericalEpochLedger.State N) : Prop :=
  MSManuscriptEpochProbability.Good (live c : ℝ) (energy c s) s.paid s.dust (tangent c s)

theorem dust_le (c : Config N d) (s : Certified c) : s.val.dust ≤ (live c : ℝ) / 1024 := by
  have hd : ((live c - s.val.owner.dim : ℕ) : ℝ) ≤ live c := Nat.cast_le.mpr (Nat.sub_le _ _)
  have hm := mul_le_mul_of_nonneg_left hd
    (by norm_num [RectangularRidgePreparationData.floor] : (0 : ℝ) ≤ 4 * RectangularRidgePreparationData.floor)
  have hh := s.property.1.dust_le
  norm_num [RectangularRidgePreparationData.floor] at hm hh
  nlinarith [Nat.cast_nonneg (α := ℝ) (live c)]

theorem tangent_moment (solver : RectangularRidgeConvexValue.Solver) (a : Fin d) (c : Config N d) :
    (output solver a c).expectation (fun s => tangent c s.val ^ 2) ≤ live c := by
  have hh := output_tangent_moment solver a c
  have ht := mul_le_mul_of_nonneg_left ((duration_le_third c).trans (by norm_num : (1 / 3 : ℝ) ≤ 1))
    (Nat.cast_nonneg (live c))
  simpa only [mul_one] using hh.trans ht

/-- Literal finite mass of good draws for the actual constructed numerical epoch. -/
theorem good_probability_ge (solver : RectangularRidgeConvexValue.Solver) (a : Fin d) (c : Config N d) :
    (31 / 50 : ℝ) ≤ (output solver a c).expectation (fun s => if Good c s.val then 1 else 0) := by
  exact MSManuscriptEpochProbability.good_probability_ge (output solver a c)
    (fun s => energy c s.val) (fun s => s.val.paid) (fun s => s.val.dust) (fun s => tangent c s.val)
    (live_pos c) (energy_nonneg c) (fun s => s.property.1.paid_nonneg) (dust_le c)
    (joint_moment solver a c) (tangent_moment solver a c)

/-- Excessive cleanup is controlled by the same actual energy/paid account. -/
theorem cleaning_probability_le (solver : RectangularRidgeConvexValue.Solver) (a : Fin d) (c : Config N d) :
    (output solver a c).expectation (fun s => if (live c : ℝ) / 64 < s.val.paid + s.val.dust then 1 else 0) ≤ 1 / 8 :=
  MSManuscriptEpochProbability.cleaning_probability_le (output solver a c)
    (fun s => energy c s.val) (fun s => s.val.paid) (fun s => s.val.dust) (live_pos c)
    (energy_nonneg c) (fun s => s.property.1.paid_nonneg) (dust_le c) (joint_moment solver a c)

end MatrixSpencer.RectangularRidgeEpochSuccess
