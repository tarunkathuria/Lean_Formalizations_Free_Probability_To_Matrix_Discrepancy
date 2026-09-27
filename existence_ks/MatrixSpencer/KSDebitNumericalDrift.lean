import MatrixSpencer.KSDebitNumericalController
import MatrixSpencer.KSPreparedHessianRayleigh

/-!
# Drift of the actual finite numerical debit-walk controller

The remaining certificate concerns only actual fourth derivatives and
smoothness on the sampled lines. Accurate numerical value reports, a
negative true Hessian direction, and a finite approximate Jacobi direction
are proved elsewhere and instantiated here. The certificate is not a
local-drift assumption.
-/

open Set
open scoped Topology
noncomputable section
namespace MatrixSpencer.KSDebitNumericalDrift

open KSDebitWalkRun KSDebitHessianQueries KSControllerParameters
variable {N d : ℕ} [Nonempty (Fin d)]

abbrev Prepared (v : Fin N → Fin d → ℂ) (δ η θ : ℝ) (hd : 0 < d) :=
  PreparedState N δ η (KSDebitNumericalValue.controllerReport v δ η θ hd)

/-- The actual finite Jacobi output before inserting the frozen zero coordinates. -/
def liveDirection (v : Fin N → Fin d → ℂ) (δ η θ M : ℝ) (hd : 0 < d)
    (s : Prepared v δ η θ hd) (hs : ¬terminal s) :
    EuclideanSpace ℝ (Fin (KSLiveEnumeration.count s.coeff)) :=
  KSNumericalHessian.output (faceReport v δ η θ hd M s.coeff) 0
    (hessianRadius δ) M (curvatureTolerance N δ)
    (KSLiveEnumeration.count_pos_of_not_vertex s.cube hs)

/-- The actual movement curve, in the same normalized live coordinates as
those used by the finite Hessian stencil. -/
def movementCurve (v : Fin N → Fin d → ℂ) (δ η θ M : ℝ) (hd : 0 < d)
    (s : Prepared v δ η θ hd) (hs : ¬terminal s) (t : ℝ) : ℝ :=
  facePotential v δ η θ s.coeff (t • liveDirection v δ η θ M hd s hs)

/-- The only remaining analytic bounds used by the numerical drift proof.
Its fields refer to the actual optimized potential at the actual states
and actual numerical direction. There are no report-accuracy, curvature,
or local-drift fields. -/
structure RemainingTaylorBounds (v : Fin N → Fin d → ℂ) (δ η θ M : ℝ) (hd : 0 < d) : Prop where
  queries : ∀ (s : Prepared v δ η θ hd), ¬terminal s →
    KSNumericalHessian.LineBounds (facePotential v δ η θ s.coeff) 0 (hessianRadius δ) M
  movement_smooth : ∀ (s : Prepared v δ η θ hd) (hs : ¬terminal s),
    ContDiffOn ℝ 4 (movementCurve v δ η θ M hd s hs)
      (Icc (-movementStep N δ M) (movementStep N δ M))
  movement_fourth : ∀ (s : Prepared v δ η θ hd) (hs : ¬terminal s),
    ∀ t ∈ Icc (-movementStep N δ M) (movementStep N δ M),
      |iteratedDeriv 4 (movementCurve v δ η θ M hd s hs) t| ≤ M

omit [Nonempty (Fin d)] in
theorem numericalDirection_eq_extend (v : Fin N → Fin d → ℂ) (δ η θ M : ℝ) (hd : 0 < d)
    (s : Prepared v δ η θ hd) (hs : ¬terminal s) :
    KSDebitNumericalController.numericalDirection v δ η θ M hd s =
      KSLiveEnumeration.extend s.coeff (liveDirection v δ η θ M hd s hs) := by
  simp only [KSDebitNumericalController.numericalDirection, dif_neg hs, liveDirection]

theorem movementCurve_eq_proposal (v : Fin N → Fin d → ℂ) (δ η θ M : ℝ) (hd : 0 < d)
    (s : Prepared v δ η θ hd) (hs : ¬terminal s) (t : ℝ) :
    movementCurve v δ η θ M hd s hs t =
      KSDebitPreparation.statePotential v δ η θ
        (KSDebitMovement.proposal s.coeff
          (KSDebitNumericalController.numericalDirection v δ η θ M hd s) t) := by
  rw [movementCurve, facePotential, KSWeightedLiveCoordinates.face_smul_eq_proposal,
    numericalDirection_eq_extend v δ η θ M hd s hs]

theorem hessian_remainder_budget (N : ℕ) {δ M a : ℝ}
    (hδ : 0 < δ) (hM : 0 ≤ M) (ha : a ≤ 3 * curvatureTolerance N δ) :
    a * movementStep N δ M ^ 2 / 2 + M * movementStep N δ M ^ 4 / 24 ≤
      driftCoefficient N δ * movementStep N δ M ^ 2 := by
  have hsq := sq_nonneg (movementStep N δ M)
  have hp := mul_le_mul_of_nonneg_right ha hsq
  have hb := mul_le_mul_of_nonneg_right (movement_drift_budget N hδ hM) hsq
  nlinarith

theorem liveDirection_hessian_le_of_contDiff (v : Fin N → Fin d → ℂ) {δ η θ M : ℝ}
    (hδ : 0 < δ) (hη : 0 < η) (hθ : 0 < θ) (hM : 0 ≤ M) (hd : 0 < d)
    (hTaylor : RemainingTaylorBounds v δ η θ M hd)
    (s : Prepared v δ η θ hd) (hs : ¬terminal s)
    (hf : ContDiffAt ℝ 2 (facePotential v δ η θ s.coeff) 0) :
    fderiv ℝ (fderiv ℝ (facePotential v δ η θ s.coeff)) 0
      (liveDirection v δ η θ M hd s hs) (liveDirection v δ η θ M hd s hs) ≤
        3 * curvatureTolerance N δ := by
  let C := KSDebitNumericalController.controller v hδ hη hθ hM hd
  have hneg := KSPreparedHessianRayleigh.prepared_leastRayleigh_neg C s hs
  have hquery := prepared_query_accuracy v hδ hη.le hθ hM hd s hs
  have hh := KSNumericalHessian.output_accuracy (facePotential v δ η θ s.coeff)
    (faceReport v δ η θ hd M s.coeff) 0
    (KSLiveEnumeration.count_pos_of_not_vertex s.cube hs) (hessianRadius_pos hδ)
    hM (curvatureTolerance_pos N hδ) hf (hTaylor.queries s hs) hquery
  have he := hh.2
  rw [KSNumericalHessian.hessian_rayleigh] at he
  change fderiv ℝ (fderiv ℝ (facePotential v δ η θ s.coeff)) 0
      (liveDirection v δ η θ M hd s hs) (liveDirection v δ η θ M hd s hs) ≤ _ at he
  change KSRayleighAccuracy.leastRayleigh
    (KSNumericalHessian.hessian (facePotential v δ η θ s.coeff) 0) < 0 at hneg
  linarith

theorem movement_average_le_of_contDiff (v : Fin N → Fin d → ℂ) {δ η θ M : ℝ}
    (hδ : 0 < δ) (hη : 0 < η) (hθ : 0 < θ) (hM : 0 ≤ M) (hd : 0 < d)
    (hTaylor : RemainingTaylorBounds v δ η θ M hd)
    (s : Prepared v δ η θ hd) (hs : ¬terminal s)
    (hf : ContDiffAt ℝ 2 (facePotential v δ η θ s.coeff) 0) :
    (KSDebitPreparation.statePotential v δ η θ
      (KSDebitMovement.proposal s.coeff
        (KSDebitNumericalController.numericalDirection v δ η θ M hd s) (-movementStep N δ M)) +
      KSDebitPreparation.statePotential v δ η θ
      (KSDebitMovement.proposal s.coeff
        (KSDebitNumericalController.numericalDirection v δ η θ M hd s) (movementStep N δ M))) / 2 ≤
      KSDebitPreparation.statePotential v δ η θ s.coeff +
        driftCoefficient N δ * movementStep N δ M ^ 2 := by
  let f := facePotential v δ η θ s.coeff
  let w := liveDirection v δ η θ M hd s hs
  have hline : ContDiffOn ℝ 4 (fun t : ℝ => f (0 + t • w))
      (Icc (-movementStep N δ M) (movementStep N δ M)) := by
    simpa only [zero_add] using hTaylor.movement_smooth s hs
  have hfourth : ∀ t ∈ Icc (-movementStep N δ M) (movementStep N δ M),
      |iteratedDeriv 4 (fun u : ℝ => f (0 + u • w)) t| ≤ M := by
    simpa only [zero_add] using hTaylor.movement_fourth s hs
  have hh := KSFourthDifference.directional_average_le f 0 w (movementStep_pos N hδ hM)
    hf hline hfourth
  have hcurv := liveDirection_hessian_le_of_contDiff v hδ hη hθ hM hd hTaylor s hs hf
  have hbudget := hessian_remainder_budget N hδ hM hcurv
  have he (t : ℝ) : f (t • w) = KSDebitPreparation.statePotential v δ η θ
      (KSDebitMovement.proposal s.coeff
        (KSDebitNumericalController.numericalDirection v δ η θ M hd s) t) :=
    movementCurve_eq_proposal v δ η θ M hd s hs t
  have hz : f 0 = KSDebitPreparation.statePotential v δ η θ s.coeff := by
    dsimp [f, facePotential]
    rw [KSWeightedLiveCoordinates.face_zero]
  have hn : f (-(movementStep N δ M • w)) = KSDebitPreparation.statePotential v δ η θ
      (KSDebitMovement.proposal s.coeff
        (KSDebitNumericalController.numericalDirection v δ η θ M hd s) (-movementStep N δ M)) := by
    simpa only [neg_smul] using he (-movementStep N δ M)
  simp only [zero_add, zero_sub] at hh
  rw [he (movementStep N δ M), hn, hz] at hh
  change fderiv ℝ (fderiv ℝ f) 0 w w * movementStep N δ M ^ 2 / 2 +
    M * movementStep N δ M ^ 4 / 24 ≤ driftCoefficient N δ * movementStep N δ M ^ 2 at hbudget
  linarith

theorem localPotentialDrift_of_contDiff (v : Fin N → Fin d → ℂ) {δ η θ M : ℝ}
    (hδ : 0 < δ) (hη : 0 < η) (hθ : 0 < θ) (hM : 0 ≤ M) (hd : 0 < d)
    (hTaylor : RemainingTaylorBounds v δ η θ M hd)
    (hf : ∀ (s : Prepared v δ η θ hd), ¬terminal s →
      ContDiffAt ℝ 2 (facePotential v δ η θ s.coeff) 0) :
    KSDebitWalkQuality.LocalPotentialDrift
      (KSDebitNumericalController.controller v hδ hη hθ hM hd) (driftCoefficient N δ) := by
  intro s hs
  exact movement_average_le_of_contDiff v hδ hη hθ hM hd hTaylor s hs (hf s hs)

/-- Ambient C² and negative true curvature are supplied by the actual face
potential and preparation theorems, not by the remaining certificate. -/
theorem liveDirection_hessian_le (v : Fin N → Fin d → ℂ) {δ η θ M : ℝ}
    (hδ : 0 < δ) (hη : 0 < η) (hθ : 0 < θ) (hM : 0 ≤ M) (hd : 0 < d)
    (hTaylor : RemainingTaylorBounds v δ η θ M hd)
    (s : Prepared v δ η θ hd) (hs : ¬terminal s) :
    fderiv ℝ (fderiv ℝ (facePotential v δ η θ s.coeff)) 0
      (liveDirection v δ η θ M hd s hs) (liveDirection v δ η θ M hd s hs) ≤
        3 * curvatureTolerance N δ := by
  apply liveDirection_hessian_le_of_contDiff v hδ hη hθ hM hd hTaylor s hs
  exact (KSDebitFaceSmoothness.contDiffAt_statePotential_face v hδ.le hη.le hθ s.cube).of_le
    (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))

/-- The actual finite numerical controller satisfies the local potential
bound once the explicitly isolated fourth-derivative certificate is proved.
There are no numerical report, direction, curvature, or drift-oracle inputs. -/
theorem localPotentialDrift (v : Fin N → Fin d → ℂ) {δ η θ M : ℝ}
    (hδ : 0 < δ) (hη : 0 < η) (hθ : 0 < θ) (hM : 0 ≤ M) (hd : 0 < d)
    (hTaylor : RemainingTaylorBounds v δ η θ M hd) :
    KSDebitWalkQuality.LocalPotentialDrift
      (KSDebitNumericalController.controller v hδ hη hθ hM hd) (driftCoefficient N δ) := by
  apply localPotentialDrift_of_contDiff v hδ hη hθ hM hd hTaylor
  intro s _
  exact (KSDebitFaceSmoothness.contDiffAt_statePotential_face v hδ.le hη.le hθ s.cube).of_le
    (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))

end MatrixSpencer.KSDebitNumericalDrift
