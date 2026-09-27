import MatrixSpencer.KSFullManuscriptRayleigh
import MatrixSpencer.KSDebitWalkQuality



open Set
open scoped BigOperators Topology
noncomputable section
namespace MatrixSpencer.KSFullManuscriptDrift

open KSFullManuscriptParameters KSFullManuscriptController KSFullManuscriptLiveCoordinates
open KSFullManuscriptQueries KSDebitWalkRun
variable {N d : ℕ} [Nonempty (Fin d)]

theorem diagonalMap_norm_le (x : Fin N → ℝ)
    (w : KSNumericalHessian.Space (KSLiveEnumeration.count x)) : ‖diagonalMap x w‖ ≤ ‖w‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs]
  apply Finset.sum_le_sum
  intro i _
  rw [diagonalMap_apply, mul_pow]
  have hw := weight_le_one x i
  have hs : weight x i ^ 2 ≤ 1 := by
    simpa only [sq_abs, one_pow] using pow_le_pow_left₀ (abs_nonneg _) hw 2
  nlinarith [mul_le_mul_of_nonneg_right hs (sq_nonneg (w i))]

theorem movement_eq (v : Fin N → Fin d → ℂ) (δ η θ M : ℝ) (hd : 0 < d)
    (s : Prepared v δ η θ hd) (hs : ¬terminal s) (t : ℝ) :
    facePotential v δ η θ s.coeff (t • diagonalMap s.coeff (liveDirection v δ η θ M hd s hs)) =
      KSDebitPreparation.statePotential v δ η θ
        (KSDebitMovement.proposal s.coeff (numericalDirection v δ η θ M hd s) t) := by
  rw [facePotential, ← map_smul, face_diagonalMap, KSWeightedLiveCoordinates.face_smul_eq_proposal]
  simp only [numericalDirection, dif_neg hs]


theorem remainder_budget (hN : 0 < N) {δ M a : ℝ} (hδ : 0 < δ) (hM : 0 < M)
    (ha : a ≤ 6 * curvatureTolerance N δ) :
    a * movementStep N δ M ^ 2 / 2 + M * movementStep N δ M ^ 4 / 24 ≤
      driftCoefficient N δ * movementStep N δ M ^ 2 := by
  have hp := mul_le_mul_of_nonneg_right ha (sq_nonneg (movementStep N δ M))
  have hb := mul_le_mul_of_nonneg_right (movement_drift_budget hN hδ hM)
    (sq_nonneg (movementStep N δ M))
  nlinarith

theorem movement_average_le (v : Fin N → Fin d → ℂ) (hN : 0 < N) {δ η θ : ℝ}
    (hδ : 0 < δ) (hη : 0 < η) (hθ : 0 < θ) (hd : 0 < d)
    (s : Prepared v δ η θ hd) (hs : ¬terminal s) :
    let M := KSFullManuscriptTaylor.budget v δ η θ
    (KSDebitPreparation.statePotential v δ η θ
      (KSDebitMovement.proposal s.coeff (numericalDirection v δ η θ M hd s) (-movementStep N δ M)) +
      KSDebitPreparation.statePotential v δ η θ
      (KSDebitMovement.proposal s.coeff (numericalDirection v δ η θ M hd s) (movementStep N δ M))) / 2 ≤
      KSDebitPreparation.statePotential v δ η θ s.coeff +
        driftCoefficient N δ * movementStep N δ M ^ 2 := by
  let M := KSFullManuscriptTaylor.budget v δ η θ
  let f := facePotential v δ η θ s.coeff
  let w := diagonalMap s.coeff (liveDirection v δ η θ M hd s hs)
  have hM := KSFullManuscriptTaylor.budget_pos v hδ hη.le hθ
  have hm := KSFullManuscriptTaylor.movementStep_le_radius v hδ hη.le hθ
  have hw : ‖w‖ ≤ 2 := by
    have he := diagonalMap_norm_le s.coeff (liveDirection v δ η θ M hd s hs)
    rw [liveDirection_norm] at he
    exact he.trans (by norm_num)
  have hmargin (i : KSLiveCurve.Live 1 s.coeff) : δ ≤ 1 - |s.coeff i| :=
    (s.margin i i.property).le
  have hf : ContDiffAt ℝ 2 f 0 :=
    (KSFullManuscriptFaceSmoothness.contDiffAt_statePotential_face v hδ.le hη.le hθ s.cube).of_le
      (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have hline : ContDiffOn ℝ 4 (fun t : ℝ => f (0 + t • w))
      (Icc (-movementStep N δ M) (movementStep N δ M)) := by
    simp only [zero_add]
    apply (KSFullManuscriptTaylor.line_contDiffOn v (η := η) hδ hθ s.cube hmargin w hw).mono
    intro t ht
    constructor <;> linarith [ht.1,ht.2]
  have hfourth : ∀ t ∈ Icc (-movementStep N δ M) (movementStep N δ M),
      |iteratedDeriv 4 (fun u : ℝ => f (0 + u • w)) t| ≤ M := by
    intro t ht
    simpa only [zero_add] using KSFullManuscriptTaylor.line_fourth_le v hδ hη.le hθ
      s.cube hmargin w hw (abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  have hh := KSFourthDifference.directional_average_le f 0 w (movementStep_pos hN hδ hM)
    hf hline hfourth
  have hc := KSFullManuscriptRayleigh.liveDirection_hessian_le v hN hδ hη hθ hd s hs
  have hb := remainder_budget hN hδ hM hc
  have he (t : ℝ) : f (t • w) = KSDebitPreparation.statePotential v δ η θ
      (KSDebitMovement.proposal s.coeff (numericalDirection v δ η θ M hd s) t) :=
    movement_eq v δ η θ M hd s hs t
  have hz : f 0 = KSDebitPreparation.statePotential v δ η θ s.coeff := by
    dsimp [f,facePotential]
    rw [face_zero]
  have hn : f (-(movementStep N δ M • w)) = KSDebitPreparation.statePotential v δ η θ
      (KSDebitMovement.proposal s.coeff (numericalDirection v δ η θ M hd s) (-movementStep N δ M)) := by
    simpa only [neg_smul] using he (-movementStep N δ M)
  simp only [zero_add,zero_sub] at hh
  rw [he (movementStep N δ M), hn, hz] at hh
  change fderiv ℝ (fderiv ℝ f) 0 w w * movementStep N δ M ^ 2 / 2 +
    M * movementStep N δ M ^ 4 / 24 ≤ driftCoefficient N δ * movementStep N δ M ^ 2 at hb
  dsimp only
  linarith


theorem localPotentialDrift (v : Fin N → Fin d → ℂ) (hN : 0 < N) {δ η θ : ℝ}
    (hδ : 0 < δ) (hη : 0 < η) (hθ : 0 < θ) (hd : 0 < d) :
    KSDebitWalkQuality.LocalPotentialDrift
      (controller v hN hδ hη hθ (KSFullManuscriptTaylor.budget_pos v hδ hη.le hθ) hd)
      (driftCoefficient N δ) := by
  intro s hs
  exact movement_average_le v hN hδ hη hθ hd s hs

/-- The actual transition, including the exhaustive numerical retirement,
obeys the same bound. -/
theorem step_potential_le (v : Fin N → Fin d → ℂ) (hN : 0 < N) {δ η θ : ℝ}
    (hδ : 0 < δ) (hη : 0 < η) (hθ : 0 < θ) (hd : 0 < d)
    (s : Prepared v δ η θ hd) (hs : ¬terminal s) :
    let C := controller v hN hδ hη hθ (KSFullManuscriptTaylor.budget_pos v hδ hη.le hθ) hd
    (KSDebitWalkQuality.potential C (step C s false) +
      KSDebitWalkQuality.potential C (step C s true)) / 2 ≤
      KSDebitWalkQuality.potential C s + driftCoefficient N δ * C.stepSize ^ 2 := by
  exact KSDebitWalkQuality.step_potential_le _ (localPotentialDrift v hN hδ hη hθ hd) s hs

end MatrixSpencer.KSFullManuscriptDrift
