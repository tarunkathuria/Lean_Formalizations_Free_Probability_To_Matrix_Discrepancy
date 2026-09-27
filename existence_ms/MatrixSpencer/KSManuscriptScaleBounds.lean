import MatrixSpencer.KSEighthManuscriptPreprocess
import MatrixSpencer.KSInitialBounds

/-!
# Polynomial reciprocal bounds for the actual KS input scales

The original-input endpoints compute epsilon from the maximum atom size.
Parseval therefore bounds all inverse input scales by the original label
count. No lower bound on an individual nonzero vector or on the source's
least positive eigenvalue is assumed. These are runtime-parameter bounds,
not an operation-count theorem for the walk.
-/
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSManuscriptScaleBounds
open KSEighthManuscriptPreprocess
variable {N d : ℕ}

/-- The input's actual maximum controls the physical dimension. -/
theorem dimension_le_count_mul_epsilon (v : Fin N→Fin d→ℂ)
    (hp : (∑i,KSRankOne.atom (v i))=1) : (d:ℝ)≤(N:ℝ)*epsilon v :=
  (dimension_le_count_epsilon v hp).trans
    (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (count_le v)) (epsilon_nonneg v))

theorem one_le_count_mul_epsilon (v : Fin N→Fin d→ℂ) (hd : 0<d)
    (hp : (∑i,KSRankOne.atom (v i))=1) : 1≤(N:ℝ)*epsilon v :=
  (show (1:ℝ)≤d from by exact_mod_cast hd).trans (dimension_le_count_mul_epsilon v hp)

/-- Tiny supplied epsilon is not a runtime obstruction: the algorithm uses
its own arithmetic maximum, whose inverse is at most N. -/
theorem inverse_epsilon_le (v : Fin N→Fin d→ℂ) (hd : 0<d)
    (hp : (∑i,KSRankOne.atom (v i))=1) : (epsilon v)⁻¹≤N := by
  have he := epsilon_pos v hd hp
  simpa only [one_div] using (div_le_iff₀ he).mpr (one_le_count_mul_epsilon v hd hp)

theorem epsilon_le_sqrt (v : Fin N→Fin d→ℂ) (hd : 0<d)
    (hp : (∑i,KSRankOne.atom (v i))=1) : epsilon v≤Real.sqrt (epsilon v) := by
  have hs := Real.sq_sqrt (epsilon_nonneg v)
  have he := epsilon_le_one v hd hp
  have hr := Real.sqrt_nonneg (epsilon v)
  have hr1 : Real.sqrt (epsilon v)≤1 := by simpa using Real.sqrt_le_sqrt he
  nlinarith

theorem inverse_delta_le (v : Fin N→Fin d→ℂ) (hd : 0<d)
    (hp : (∑i,KSRankOne.atom (v i))=1) : (Real.sqrt (epsilon v))⁻¹≤N := by
  simpa only [one_div] using (one_div_le_one_div_of_le (epsilon_pos v hd hp)
    (epsilon_le_sqrt v hd hp)).trans (show 1 / epsilon v ≤ (N:ℝ) by
      simpa only [one_div] using inverse_epsilon_le v hd hp)

/-- The fixed regularizer used by both original-input algorithms has inverse
at most 2N. This uses dimension ≤ N epsilon, so no independent dimension or
minimum-vector-norm lower bound is needed. -/
theorem inverse_regularizer_le (v : Fin N→Fin d→ℂ) (hd : 0<d)
    (hp : (∑i,KSRankOne.atom (v i))=1) :
    (ksRegularizerScale (epsilon v) (Fin d))⁻¹≤2*N := by
  have he := epsilon_pos v hd hp
  have hδ := Real.sqrt_pos.mpr he
  have hN : (1:ℝ)≤N := by
    have hn := (count_pos v hd hp).trans_le (count_le v)
    exact_mod_cast hn
  have hdn := dimension_le_count_mul_epsilon v hp
  have hs := Real.sq_sqrt he.le
  have hd0 : (0:ℝ)≤d := Nat.cast_nonneg _
  have hD := Real.sq_sqrt (show (0:ℝ)≤2*d by positivity)
  have hmul := mul_le_mul_of_nonneg_right hN (mul_nonneg (le_trans zero_le_one hN) he.le)
  have hh : Real.sqrt (2*(d:ℝ))≤2*N*Real.sqrt (epsilon v) := by
    have hl := Real.sqrt_nonneg (2*(d:ℝ))
    have hr : 0≤2*(N:ℝ)*Real.sqrt (epsilon v) := by positivity
    have hsq : (2*(N:ℝ)*Real.sqrt (epsilon v))^2 = 4*(N:ℝ)^2*epsilon v := by
      rw [mul_pow, mul_pow, hs]
      ring
    nlinarith
  unfold ksRegularizerScale
  simp only [Fintype.card_sum,Fintype.card_fin,Nat.cast_add]
  rw [inv_div]
  apply (div_le_iff₀ hδ).mpr
  simpa only [two_mul] using hh

end MatrixSpencer.KSManuscriptScaleBounds
