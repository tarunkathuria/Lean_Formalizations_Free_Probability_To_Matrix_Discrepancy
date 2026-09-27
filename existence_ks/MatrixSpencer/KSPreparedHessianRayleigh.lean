import MatrixSpencer.KSNumericalHessian
import MatrixSpencer.KSPreparedNegativeCurvature
import MatrixSpencer.KSDebitFaceSmoothness

/-!
# Negative least Hessian Rayleigh value at prepared states

A proved negative second derivative along a nonzero direction gives a unit
competitor with negative Rayleigh value for the actual Hessian matrix. The
normalization is used in this proof of the variational bound; it is not the
numerical direction returned by the algorithm.
-/

open Set
noncomputable section
namespace MatrixSpencer.KSPreparedHessianRayleigh

variable {d : ℕ}

/-- A concrete negative second derivative yields a negative least Rayleigh
value. The Hessian is the actual second Fréchet derivative in coordinates. -/
theorem leastRayleigh_neg_of_negative_second
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (x w : EuclideanSpace ℝ (Fin d))
    (hf : ContDiffAt ℝ 2 f x) (hw : w ≠ 0)
    (hnegative : iteratedDeriv 2 (fun t : ℝ => f (x + t • w)) 0 < 0) :
    KSRayleighAccuracy.leastRayleigh (KSNumericalHessian.hessian f x) < 0 := by
  have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hi : 0 < ‖w‖⁻¹ := inv_pos.mpr hn
  let u : EuclideanSpace ℝ (Fin d) := ‖w‖⁻¹ • w
  have hu : ‖u‖ = 1 := by
    rw [show u = ‖w‖⁻¹ • w from rfl, norm_smul, Real.norm_eq_abs,
      abs_of_pos hi, inv_mul_cancel₀ (ne_of_gt hn)]
  have hq : fderiv ℝ (fderiv ℝ f) x w w < 0 := by
    rwa [KSFourthDifference.line_second f x w hf] at hnegative
  have hscaled : KSRayleighAccuracy.realRayleigh (KSNumericalHessian.hessian f x) u < 0 := by
    rw [KSNumericalHessian.hessian_rayleigh]
    change fderiv ℝ (fderiv ℝ f) x (‖w‖⁻¹ • w) (‖w‖⁻¹ • w) < 0
    simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    exact mul_neg_of_pos_of_neg hi (mul_neg_of_pos_of_neg hi hq)
  exact (KSRayleighAccuracy.leastRayleigh_le _ u hu).trans_lt hscaled

theorem leastRayleigh_neg_of_negative_second_zero
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (w : EuclideanSpace ℝ (Fin d))
    (hf : ContDiffAt ℝ 2 f 0) (hw : w ≠ 0)
    (hnegative : iteratedDeriv 2 (fun t : ℝ => f (t • w)) 0 < 0) :
    KSRayleighAccuracy.leastRayleigh (KSNumericalHessian.hessian f 0) < 0 :=
  leastRayleigh_neg_of_negative_second f 0 w hf hw (by simpa only [zero_add] using hnegative)

variable {N : ℕ} {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

open KSDebitWalkRun KSDebitPreparation KSWeightedLiveCoordinates

theorem prepared_leastRayleigh_neg_of_contDiff
    (C : Controller N n) (s : State C) (hs : ¬terminal s)
    (hf : ContDiffAt ℝ 2
      (fun z => statePotential C.vectors C.δ C.η C.θ (face s.coeff z)) 0) :
    KSRayleighAccuracy.leastRayleigh (KSNumericalHessian.hessian
      (fun z => statePotential C.vectors C.δ C.η C.θ (face s.coeff z)) 0) < 0 := by
  obtain ⟨w, hw, _, hnegative⟩ := KSPreparedNegativeCurvature.exists_negative_second C s hs
  exact leastRayleigh_neg_of_negative_second_zero _ w hf hw hnegative

/-- Every nonterminal actual prepared state has negative least Hessian
Rayleigh value. Ambient smoothness and the negative direction are both
discharged by the actual debit potential proofs. -/
theorem prepared_leastRayleigh_neg (C : Controller N n) (s : State C) (hs : ¬terminal s) :
    KSRayleighAccuracy.leastRayleigh (KSNumericalHessian.hessian
      (fun z => statePotential C.vectors C.δ C.η C.θ (face s.coeff z)) 0) < 0 := by
  apply prepared_leastRayleigh_neg_of_contDiff C s hs
  exact (KSDebitFaceSmoothness.contDiffAt_statePotential_face C.vectors
    C.δ_pos.le C.η_nonneg C.θ_pos s.cube).of_le
      (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))

theorem prepared_leastRayleigh_nonpos (C : Controller N n) (s : State C) (hs : ¬terminal s) :
    KSRayleighAccuracy.leastRayleigh (KSNumericalHessian.hessian
      (fun z => statePotential C.vectors C.δ C.η C.θ (face s.coeff z)) 0) ≤ 0 :=
  (prepared_leastRayleigh_neg C s hs).le

end MatrixSpencer.KSPreparedHessianRayleigh
