import MatrixSpencer.KSFullManuscriptEllipsoidMeasure

/-!
# Finite ellipsoid feasibility from inner and outer balls

This proves the volume-based finite cutoff for the actual central-cut
recursion. The separation procedure remains explicitly supplied and certified;
the affine SDP and its concrete separating-vector computation are not assumed
to have been implemented by this theorem.
-/

open Set MeasureTheory
open scoped ENNReal InnerProductSpace
noncomputable section
namespace MatrixSpencer.KSFullManuscriptEllipsoidCutoff

open KSFullManuscriptEllipsoidAffine KSFullManuscriptEllipsoidRun
open KSFullManuscriptEllipsoidMeasure
variable {ℓ : ℕ}

def contraction (ℓ : ℕ) : ℝ := Real.exp (-1 / (2 * ((ℓ : ℝ) + 1)))

theorem run_surjective (hℓ : 1 < ℓ) {target : Set (Space ℓ)}
    (sep : SeparationProcedure target) (s : State (Space ℓ))
    (hs : Function.Surjective s.factor) (T : ℕ) :
    Function.Surjective (run (ℓ : ℝ) sep.query T s).factor := by
  have hr : (1 : ℝ) < ℓ := by exact_mod_cast hℓ
  induction T with
  | zero => exact hs
  | succ T ih => exact step_surjective hr sep _ ih

theorem feasible_or_volume_bound (hℓ : 1 < ℓ) {target : Set (Space ℓ)}
    (sep : SeparationProcedure target) (s : State (Space ℓ))
    (hs : Function.Surjective s.factor) (T : ℕ) :
    sep.query (run (ℓ : ℝ) sep.query T s).center = none ∨
      volume (body (run (ℓ : ℝ) sep.query T s)) ≤
        ENNReal.ofReal (contraction ℓ) ^ T * volume (body s) := by
  induction T with
  | zero => right; simp only [run, pow_zero, one_mul, le_refl]
  | succ T ih =>
    cases hq : sep.query (run (ℓ : ℝ) sep.query T s).center with
    | none => left; simp only [run, step, hq]
    | some g =>
      right
      have hprev := ih.resolve_left (by simp [hq])
      have hstep := update_volume_le hℓ (run (ℓ : ℝ) sep.query T s)
        (run_surjective hℓ sep s hs T) (sep.separates _ _ hq).1
      change volume (body (step (ℓ : ℝ) sep.query (run (ℓ : ℝ) sep.query T s))) ≤ _
      rw [step, hq]
      calc
        _ ≤ ENNReal.ofReal (contraction ℓ) * volume (body (run (ℓ : ℝ) sep.query T s)) := hstep
        _ ≤ ENNReal.ofReal (contraction ℓ) *
            (ENNReal.ofReal (contraction ℓ) ^ T * volume (body s)) := mul_le_mul_left' hprev _
        _ = _ := by rw [pow_succ]; ac_rfl

theorem scalar_volume_cutoff (hℓ : 1 < ℓ) {R r : ℝ} (hR : 0 < R) (hr : 0 < r)
    (T : ℕ) (hT : 2 * (ℓ : ℝ) * ((ℓ : ℝ) + 1) * Real.log (R / r) < T) :
    contraction ℓ ^ T * R ^ ℓ < r ^ ℓ := by
  have hc : 0 < contraction ℓ := Real.exp_pos _
  apply (Real.log_lt_log_iff (mul_pos (pow_pos hc _) (pow_pos hR _)) (pow_pos hr _)).mp
  rw [Real.log_mul (ne_of_gt (pow_pos hc _)) (ne_of_gt (pow_pos hR _)),
    Real.log_pow, Real.log_pow, Real.log_pow, contraction, Real.log_exp]
  rw [Real.log_div (ne_of_gt hR) (ne_of_gt hr)] at hT
  have hden : 0 < 2 * ((ℓ : ℝ) + 1) := by positivity
  have hd : (T : ℝ) * (-1 / (2 * ((ℓ : ℝ) + 1))) =
      -(T : ℝ) / (2 * ((ℓ : ℝ) + 1)) := by ring
  rw [hd]
  have hh : (ℓ : ℝ) * (Real.log R - Real.log r) <
      (T : ℝ) / (2 * ((ℓ : ℝ) + 1)) := by
    apply (lt_div_iff₀ hden).mpr
    nlinarith
  rw [neg_div]
  nlinarith

def initial (c : Space ℓ) (R : ℝ) : State (Space ℓ) where
  center := c
  factor := R • ContinuousLinearMap.id ℝ (Space ℓ)

theorem initial_surjective (c : Space ℓ) {R : ℝ} (hR : 0 < R) :
    Function.Surjective (initial c R).factor := by
  intro y
  refine ⟨R⁻¹ • y, ?_⟩
  simp [initial, smul_smul, ne_of_gt hR]

theorem initial_body (c : Space ℓ) {R : ℝ} (hR : 0 < R) :
    body (initial c R) = Metric.closedBall c R := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    simp only [Metric.mem_closedBall, dist_eq_norm, initial,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, add_sub_cancel_left,
      norm_smul, Real.norm_eq_abs, abs_of_pos hR]
    nlinarith
  · intro hy
    have hn : ‖y - c‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hy
    refine ⟨R⁻¹ • (y - c), ?_, ?_⟩
    · rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR]
      have hh : ‖y - c‖ / R ≤ 1 := (div_le_iff₀ hR).mpr (by simpa using hn)
      simpa only [one_mul, div_eq_mul_inv, mul_comm] using hh
    · simp only [initial, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
        smul_smul, mul_inv_cancel₀ (ne_of_gt hR), one_smul]
      abel

theorem feasible_by_cutoff (hℓ : 1 < ℓ) {target : Set (Space ℓ)}
    (sep : SeparationProcedure target) (c z : Space ℓ) {R r : ℝ}
    (hR : 0 < R) (hr : 0 < r) (houter : target ⊆ Metric.closedBall c R)
    (hinner : Metric.closedBall z r ⊆ target) (T : ℕ)
    (hT : 2 * (ℓ : ℝ) * ((ℓ : ℝ) + 1) * Real.log (R / r) < T) :
    sep.query (run (ℓ : ℝ) sep.query T (initial c R)).center = none := by
  have hrℓ : (1 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hs := initial_surjective c hR
  have hb : target ⊆ body (initial c R) := by rwa [initial_body c hR]
  have hi := (run_invariant hrℓ sep (initial c R) hs hb T).2
  rcases feasible_or_volume_bound hℓ sep (initial c R) hs T with hdone | hvol
  · exact hdone
  · have hsmall : ENNReal.ofReal (contraction ℓ) ^ T * volume (body (initial c R)) <
        volume (Metric.closedBall z r) := by
      rw [initial_body c hR, Measure.addHaar_closedBall' volume c hR.le,
        Measure.addHaar_closedBall' volume z hr.le]
      simp only [finrank_euclideanSpace_fin]
      have hc : 0 ≤ contraction ℓ := (Real.exp_pos _).le
      rw [← ENNReal.ofReal_pow hc, ← mul_assoc,
        ← ENNReal.ofReal_mul (pow_nonneg hc _)]
      apply (ENNReal.mul_lt_mul_right
        (Metric.measure_closedBall_pos volume (0 : Space ℓ) (by norm_num : (0 : ℝ) < 1)).ne'
        measure_closedBall_lt_top.ne).mpr
      exact (ENNReal.ofReal_lt_ofReal_iff (pow_pos hr _)).mpr
        (scalar_volume_cutoff hℓ hR hr T hT)
    have hlarge : volume (Metric.closedBall z r) ≤
        volume (body (run (ℓ : ℝ) sep.query T (initial c R))) := measure_mono (hinner.trans hi)
    exact False.elim (not_lt_of_ge hlarge (hvol.trans_lt hsmall))


def budget (ℓ : ℕ) (R r : ℝ) : ℕ :=
  ⌈2 * (ℓ : ℝ) * ((ℓ : ℝ) + 1) * Real.log (R / r)⌉₊ + 1

theorem budget_gt (ℓ : ℕ) (R r : ℝ) :
    2 * (ℓ : ℝ) * ((ℓ : ℝ) + 1) * Real.log (R / r) < (budget ℓ R r : ℝ) := by
  have h := Nat.le_ceil (2 * (ℓ : ℝ) * ((ℓ : ℝ) + 1) * Real.log (R / r))
  simp only [budget, Nat.cast_add, Nat.cast_one]
  linarith

/-- The actual finite loop, at the explicit cut budget, returns a feasible
point when the target has the supplied inner ball and outer ball. -/
theorem output_by_budget (hℓ : 1 < ℓ) {target : Set (Space ℓ)}
    (sep : SeparationProcedure target) (c z : Space ℓ) {R r : ℝ}
    (hR : 0 < R) (hr : 0 < r) (houter : target ⊆ Metric.closedBall c R)
    (hinner : Metric.closedBall z r ⊆ target) :
    ∃ y, output (ℓ : ℝ) sep.query (budget ℓ R r) (initial c R) = some y ∧ y ∈ target := by
  have hf := feasible_by_cutoff hℓ sep c z hR hr houter hinner
    (budget ℓ R r) (budget_gt ℓ R r)
  refine ⟨(run (ℓ : ℝ) sep.query (budget ℓ R r) (initial c R)).center, ?_, sep.feasible _ hf⟩
  simp only [output, hf]

end MatrixSpencer.KSFullManuscriptEllipsoidCutoff
