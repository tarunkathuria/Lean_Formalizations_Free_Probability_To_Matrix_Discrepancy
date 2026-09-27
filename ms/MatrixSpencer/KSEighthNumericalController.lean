import MatrixSpencer.KSEighthHessianQueries
import MatrixSpencer.KSEighthPreparationCost

/-!
# The actual finite numerical eighth-cube controller

All value, fourth-derivative, and Hessian approximation guarantees are
proved from the original input. The direction is computed by finite Jacobi
iteration on actual finite-difference reports. Each movement uses a fair sign
of this one weighted unit direction. The original eighth potential and
endpoint-deleting preparation are retained.
-/

open Set
open scoped BigOperators ContDiff Topology
noncomputable section
namespace MatrixSpencer.KSEighthNumericalController
open KSEighthWalkRun KSEighthHessianQueries KSEighthFacePotential
variable {N d : ℕ}

abbrev ReportState (v : Fin N → Fin d → ℂ) (ρ τ θ : ℝ) (hd : 0 < d) :=
  PreparedState N ρ τ (KSEighthNumericalValue.stateReport v θ hd (τ/8))

def liveDirection (v : Fin N → Fin d → ℂ) (θ κ : ℝ) (hd : 0 < d)
    (x : Fin N → ℝ) (hlive : 0 < KSEighthLiveEnumeration.count x) : Space x :=
  KSNumericalHessian.output (faceReport v θ κ hd x) 0 (1/32)
    (KSEighthInputTaylorBound.fourthBudget v θ) κ hlive

def numericalDirection (v : Fin N → Fin d → ℂ) (ρ τ θ κ : ℝ) (hd : 0 < d)
    (s : ReportState v ρ τ θ hd) : EuclideanSpace ℝ (Fin N) := by
  classical
  exact if hs : terminal s then 0 else KSEighthLiveEnumeration.extend s.coeff
    (liveDirection v θ κ hd s.coeff (KSEighthLiveEnumeration.count_pos_of_not_vertex s.cube hs))

theorem liveDirection_norm (v : Fin N → Fin d → ℂ) (θ κ : ℝ) (hd : 0 < d)
    (x : Fin N → ℝ) (hlive : 0 < KSEighthLiveEnumeration.count x) :
    ‖liveDirection v θ κ hd x hlive‖ = 1 := KSJacobiRayleigh.outputVector_norm _ _ _

theorem numericalDirection_norm (v : Fin N → Fin d → ℂ) (ρ τ θ κ : ℝ) (hd : 0 < d)
    (s : ReportState v ρ τ θ hd) (hs : ¬terminal s) : ‖numericalDirection v ρ τ θ κ hd s‖ = 1 := by
  rw [numericalDirection, dif_neg hs, KSEighthLiveEnumeration.extend_norm]
  exact liveDirection_norm v θ κ hd _ _

theorem numericalDirection_frozen (v : Fin N → Fin d → ℂ) (ρ τ θ κ : ℝ) (hd : 0 < d)
    (s : ReportState v ρ τ θ hd) (hs : ¬terminal s) (i : Fin N) (hi : |s.coeff i| = 1/8) :
    numericalDirection v ρ τ θ κ hd s i = 0 := by
  rw [numericalDirection, dif_neg hs]
  exact KSEighthLiveEnumeration.extend_frozen _ _ i hi

def movementStep (v : Fin N → Fin d → ℂ) (ρ θ κ : ℝ) : ℝ :=
  min (ρ/2) (min (1/32) (Real.sqrt (κ/(KSEighthInputTaylorBound.fourthBudget v θ+1))))

theorem movementStep_pos (v : Fin N → Fin d → ℂ) {ρ θ κ : ℝ}
    (hρ : 0 < ρ) (hθ : 0 < θ) (hκ : 0 < κ) (hd : 0 < d) : 0 < movementStep v ρ θ κ := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  have hM := KSEighthInputTaylorBound.fourthBudget_pos v hθ
  unfold movementStep
  positivity

theorem movementStep_le_half (v : Fin N → Fin d → ℂ) (ρ θ κ : ℝ) : movementStep v ρ θ κ ≤ ρ/2 :=
  min_le_left _ _

theorem movementStep_le_radius (v : Fin N → Fin d → ℂ) (ρ θ κ : ℝ) : movementStep v ρ θ κ ≤ 1/32 :=
  (min_le_right _ _).trans (min_le_left _ _)

theorem movementStep_square_bound (v : Fin N → Fin d → ℂ) {ρ θ κ : ℝ}
    (hρ : 0 < ρ) (hθ : 0 < θ) (hκ : 0 < κ) (hd : 0 < d) :
    KSEighthInputTaylorBound.fourthBudget v θ * movementStep v ρ θ κ ^ 2 ≤ κ := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  have hM := KSEighthInputTaylorBound.fourthBudget_pos v hθ
  have ht := movementStep_pos v hρ hθ hκ hd
  have hs : movementStep v ρ θ κ ≤ Real.sqrt (κ/(KSEighthInputTaylorBound.fourthBudget v θ+1)) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have he := Real.sq_sqrt (div_nonneg hκ.le (by linarith : 0 ≤ KSEighthInputTaylorBound.fourthBudget v θ+1))
  have hsq : movementStep v ρ θ κ ^ 2 ≤ κ/(KSEighthInputTaylorBound.fourthBudget v θ+1) := by
    nlinarith [Real.sqrt_nonneg (κ/(KSEighthInputTaylorBound.fourthBudget v θ+1))]
  have hm := (le_div_iff₀ (by linarith : 0 < KSEighthInputTaylorBound.fourthBudget v θ+1)).mp hsq
  nlinarith [sq_nonneg (movementStep v ρ θ κ)]

/-- The complete numerical controller, with no accuracy fields supplied. -/
def controller (v : Fin N → Fin d → ℂ) {ρ τ θ κ : ℝ}
    (hρ : 0 < ρ) (hθ : 0 < θ) (hκ : 0 < κ) (hd : 0 < d) : Controller N where
  ρ := ρ
  ρ_pos := hρ
  τ := τ
  report := KSEighthNumericalValue.stateReport v θ hd (τ/8)
  stepSize := movementStep v ρ θ κ
  step_pos := movementStep_pos v hρ hθ hκ hd
  step_le := (movementStep_le_half v ρ θ κ).trans (by linarith)
  direction := numericalDirection v ρ τ θ κ hd
  direction_norm := numericalDirection_norm v ρ τ θ κ hd
  direction_frozen := numericalDirection_frozen v ρ τ θ κ hd

/-- True curvature of the computed direction, after actual finite preparation. -/
theorem liveDirection_curvature (v : Fin N → Fin d → ℂ) {ρ τ θ κ : ℝ}
    (hτ : 0 < τ) (hθ : 0 < θ) (hκ : 0 < κ) (hd : 0 < d)
    (s : ReportState v ρ τ θ hd) (hs : ¬terminal s) :
    fderiv ℝ (fderiv ℝ (potential v θ s.coeff)) 0
      (liveDirection v θ κ hd s.coeff (KSEighthLiveEnumeration.count_pos_of_not_vertex s.cube hs))
      (liveDirection v θ κ hd s.coeff (KSEighthLiveEnumeration.count_pos_of_not_vertex s.cube hs)) ≤ 3*κ := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  have hlive := KSEighthLiveEnumeration.count_pos_of_not_vertex s.cube hs
  have hf := (contDiffAt_potential v hθ s.coeff).of_le
    (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have h := (KSNumericalHessian.output_accuracy (potential v θ s.coeff) _ 0 hlive
    (by norm_num : (0 : ℝ) < 1/32) (KSEighthInputTaylorBound.fourthBudget_pos v hθ).le hκ
    hf (line_bounds v hθ hd s.cube) (query_accuracy v hθ hκ hd s.cube hlive)).2
  rw [KSNumericalHessian.hessian_rayleigh] at h
  have hn := KSEighthNegativeRayleigh.numerical_prepared_leastRayleigh_neg v hθ hτ hd s hs
  exact h.trans (by linarith)

/-- Symmetric actual movement before preparation has a proved quadratic
potential drift, with all Taylor and value errors discharged. -/
theorem proposal_average_le (v : Fin N → Fin d → ℂ) {ρ τ θ κ : ℝ}
    (hρ : 0 < ρ) (hτ : 0 < τ) (hθ : 0 < θ) (hκ : 0 < κ) (hd : 0 < d)
    (s : ReportState v ρ τ θ hd) (hs : ¬terminal s) :
    let F := KSPotentialModels.eighthPotential (fun i => KSRankOne.atom (v i)) θ
    let t := movementStep v ρ θ κ
    (F (proposal s.coeff (numericalDirection v ρ τ θ κ hd s) t) +
      F (proposal s.coeff (numericalDirection v ρ τ θ κ hd s) (-t)))/2 ≤
      F s.coeff + 2*κ*t^2 := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  let w := liveDirection v θ κ hd s.coeff (KSEighthLiveEnumeration.count_pos_of_not_vertex s.cube hs)
  let t := movementStep v ρ θ κ
  have ht := movementStep_pos v hρ hθ hκ hd
  have htr := movementStep_le_radius v ρ θ κ
  have hw : ‖w‖ = 1 := liveDirection_norm _ _ _ _ _ _
  have hsub : Icc (-t) t ⊆ Icc (-(1/32 : ℝ)) (1/32) := fun z hz => ⟨by linarith [hz.1],by linarith [hz.2]⟩
  have hf := (contDiffAt_potential v hθ s.coeff).of_le
    (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have hline : ContDiffOn ℝ 4 (fun u : ℝ => potential v θ s.coeff (0+u • w)) (Icc (-t) t) := by
    simpa only [zero_add] using (line_contDiffOn v hθ hd s.cube w (by rw [hw]; norm_num)).mono hsub
  have hcap : ∀ u ∈ Icc (-t) t,
      |iteratedDeriv 4 (fun z : ℝ => potential v θ s.coeff (0+z • w)) u| ≤ KSEighthInputTaylorBound.fourthBudget v θ := by
    intro u hu
    simpa only [zero_add] using line_fourth_bound v hθ hd s.cube w (by rw [hw]; norm_num) (abs_le.mpr (hsub hu))
  have ha := KSFourthDifference.directional_average_le (potential v θ s.coeff) 0 w ht hf hline hcap
  have hcurv := liveDirection_curvature v hτ hθ hκ hd s hs
  have hsq := movementStep_square_bound v hρ hθ hκ hd
  have he (u : ℝ) (hu : |u| ≤ t) : potential v θ s.coeff (u • w) =
      KSPotentialModels.eighthPotential (fun i => KSRankOne.atom (v i)) θ
        (proposal s.coeff (numericalDirection v ρ τ θ κ hd s) u) := by
    rw [potential_eq_state v hθ s.cube _ (fun i hi => (s.margin i hi).le) (by
      rw [norm_smul, Real.norm_eq_abs, hw, mul_one]
      exact hu.trans_lt (lt_of_le_of_lt (movementStep_le_half v ρ θ κ) (by linarith)))]
    rw [numericalDirection, dif_neg hs, ← KSEighthLiveCoordinates.face_smul_eq_proposal]
  simp only [zero_add, zero_sub, ← neg_smul] at ha
  rw [he t (abs_of_pos ht).le, he (-t) (by rw [abs_neg, abs_of_pos ht]), potential_zero v hθ s.cube] at ha
  dsimp only
  have hc := mul_le_mul_of_nonneg_right hcurv (sq_nonneg t)
  have hm := mul_le_mul_of_nonneg_right hsq (sq_nonneg t)
  change _ ≤ _ + 2*κ*t^2
  dsimp only [w, t] at *
  nlinarith [sq_nonneg (movementStep v ρ θ κ)]

end MatrixSpencer.KSEighthNumericalController
