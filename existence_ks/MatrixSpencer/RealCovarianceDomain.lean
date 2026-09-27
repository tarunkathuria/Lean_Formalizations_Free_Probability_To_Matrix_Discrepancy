import MatrixSpencer.TsallisHessian

/-! Openness of the positive definite real symmetric covariance cone. -/

open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
open Filter Topology

namespace MatrixSpencer

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem eventually_real_nonneg_of_posDef (Q : selfAdjoint (Matrix n n ℝ))
    (hQ : (Q : Matrix n n ℝ).PosDef) :
    ∀ᶠ X : selfAdjoint (Matrix n n ℝ) in 𝓝 Q, 0 ≤ (X : Matrix n n ℝ) := by
  rcases subsingleton_or_nontrivial (Matrix n n ℝ) with h | h
  · letI := h
    exact Filter.Eventually.of_forall fun X => by
      rw [Subsingleton.elim (X : Matrix n n ℝ) 0]
  · letI := h
    have hstrict : IsStrictlyPositive (Q : Matrix n n ℝ) :=
      IsStrictlyPositive.iff_of_unital.mpr ⟨hQ.posSemidef.nonneg, hQ.isUnit⟩
    obtain ⟨r, hr, hrQ⟩ := (CFC.exists_pos_algebraMap_le_iff Q.property).mpr
      ((StarOrderedRing.isStrictlyPositive_iff_spectrum_pos (Q : Matrix n n ℝ)).mp hstrict)
    refine Metric.eventually_nhds_iff.mpr ⟨r, hr, ?_⟩
    intro X hX
    have hdist : ‖(X : Matrix n n ℝ) - (Q : Matrix n n ℝ)‖ < r := by
      simpa only [dist_eq_norm] using hX
    have hs : IsSelfAdjoint ((X : Matrix n n ℝ) - (Q : Matrix n n ℝ)) :=
      IsSelfAdjoint.sub X.property Q.property
    have hlow : -(algebraMap ℝ (Matrix n n ℝ)
        ‖(X : Matrix n n ℝ) - (Q : Matrix n n ℝ)‖) ≤
        (X : Matrix n n ℝ) - (Q : Matrix n n ℝ) := by
      rw [← map_neg]
      apply algebraMap_le_of_le_spectrum (ha := hs)
      intro t ht
      have hb : ‖t‖ ≤ ‖(X : Matrix n n ℝ) - (Q : Matrix n n ℝ)‖ :=
        spectrum.norm_le_norm_of_mem ht
      exact (neg_le_neg hb).trans (by simpa only [Real.norm_eq_abs] using neg_abs_le t)
    have hmap : algebraMap ℝ (Matrix n n ℝ) ‖(X : Matrix n n ℝ) - Q‖ ≤
        algebraMap ℝ (Matrix n n ℝ) r := by
      simp only [Algebra.algebraMap_eq_smul_one]
      exact smul_le_smul_of_nonneg_right hdist.le zero_le_one
    calc
      0 = algebraMap ℝ (Matrix n n ℝ) r - algebraMap ℝ (Matrix n n ℝ) r :=
        (sub_self _).symm
      _ ≤ algebraMap ℝ (Matrix n n ℝ) r -
          algebraMap ℝ (Matrix n n ℝ) ‖(X : Matrix n n ℝ) - Q‖ :=
        sub_le_sub_left hmap _
      _ ≤ (Q : Matrix n n ℝ) + ((X : Matrix n n ℝ) - Q) :=
        add_le_add hrQ hlow
      _ = X := by abel

theorem eventually_real_posDef_of_posDef (S : selfAdjoint (Matrix n n ℝ))
    (hS : (S : Matrix n n ℝ).PosDef) :
    ∀ᶠ X : selfAdjoint (Matrix n n ℝ) in 𝓝 S, (X : Matrix n n ℝ).PosDef := by
  have hu : ∀ᶠ X : selfAdjoint (Matrix n n ℝ) in 𝓝 S,
      IsUnit (X : Matrix n n ℝ) :=
    continuous_subtype_val.continuousAt (Units.isOpen.mem_nhds hS.isUnit)
  filter_upwards [eventually_real_nonneg_of_posDef S hS, hu] with X hX huX
  exact hX.posSemidef.posDef_iff_isUnit.mpr huX

end MatrixSpencer
