import MatrixSpencer.MSManuscriptPolynomialQueryParameters

/-! Substitution of primitive original inputs into all covariance-query and
paid-preparation polynomial parameter bounds at the actual nested factory.
-/
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.MSManuscriptPolynomialQueryFactory
open PhaseRestriction MSManuscriptPolynomialQueryCurvature
  MSManuscriptPolynomialQueryParameters MSManuscriptFactoryPolynomialMovementBounds
local instance {m : Type*} [Fintype m] [DecidableEq m] :
    CStarAlgebra (Matrix m m ℂ) := {}
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

variable {ι n : Type*} [Fintype ι] [LinearOrder ι]
  [Fintype n] [DecidableEq n] {d : ℕ} [Nonempty (Fin d)]
variable (e : Fin d ≃ n) (A : ι → Matrix n n ℂ)
  (hA : ∀ i, (A i).IsHermitian) (hN : ∀ i, ‖A i‖ ≤ 1)
  (x : EuclideanSpace ℝ ι)
  (y : MSManuscriptPhase.Point (ι := Live x) (signingEpsilon ι))
  (hl : 32 ≤ Fintype.card (Live y.val)) (hd : 0 < d)

abbrev config := MSManuscriptNumericalConfig.ofEpochConfig (cfg e A hA hN x y hl) hd

abbrev parameters (s : MSManuscriptNumericalEpochLedger.State (Fintype.card (Live y.val))) :=
  MSManuscriptNumericalEpochRun.params (config e A hA hN x y hl hd) s

theorem centerCap_nonneg (s : MSManuscriptNumericalEpochLedger.State (Fintype.card (Live y.val))) :
    0 ≤ (parameters e A hA hN x y hl hd s).centerCap :=
  (MSManuscriptEpochInput.centerCap_pos (cfg e A hA hN x y hl).offset).le

theorem centerCap_le (s : MSManuscriptNumericalEpochLedger.State (Fintype.card (Live y.val))) :
    (parameters e A hA hN x y hl hd s).centerCap ≤ center (Fintype.card ι) d := by
  have hb := MSManuscriptPolynomialMovementBounds.centerCap_le
    (N:=Fintype.card (Live y.val)) (cfg e A hA hN x y hl).offset
    (Nat.cast_nonneg (Fintype.card ι)) (offset_norm_le e A hA hN x y hl)
  have hc := Nat.cast_le (α:=ℝ).mpr (live_le_original x y)
  change MSManuscriptEpochInput.centerCap (cfg e A hA hN x y hl).offset ≤ _
  rw [cast_center]
  linarith

theorem secondCap_le (s : MSManuscriptNumericalEpochLedger.State (Fintype.card (Live y.val)))
    (k : ℕ) (hk : k ≤ Fintype.card (Live y.val)) :
    MSManuscriptGammaInputBoundScaled.secondCap k d
      (parameters e A hA hN x y hl hd s).centerCap
      (parameters e A hA hN x y hl hd s).regularizer
      (parameters e A hA hN x y hl hd s).floor (Fintype.card (Live y.val)) ≤
      second (Fintype.card ι) d :=
  MSManuscriptPolynomialQueryCurvature.secondCap_le (hk.trans (live_le_original x y))
    (live_le_original x y) hd (centerCap_nonneg e A hA hN x y hl hd s)
    (centerCap_le e A hA hN x y hl hd s)

theorem curvatureBudget_le (s : MSManuscriptNumericalEpochLedger.State (Fintype.card (Live y.val))) :
    MSManuscriptSupportedPaid.curvatureBudget (parameters e A hA hN x y hl hd s) ≤
      curvature (Fintype.card ι) d :=
  MSManuscriptPolynomialQueryCurvature.curvatureBudget_le _ (live_le_original x y) rfl rfl
    (centerCap_nonneg e A hA hN x y hl hd s) (centerCap_le e A hA hN x y hl hd s)

theorem threshold_inverse_le (s : MSManuscriptNumericalEpochLedger.State (Fintype.card (Live y.val))) :
    (parameters e A hA hN x y hl hd s).threshold⁻¹ ≤ thresholdInv (Fintype.card ι) :=
  MSManuscriptPolynomialQueryParameters.threshold_inverse_le (live_le_original x y)

theorem topPrecision_inverse_le (s : MSManuscriptNumericalEpochLedger.State (Fintype.card (Live y.val)))
    (k : ℕ) (hk : k ≤ Fintype.card (Live y.val)) :
    (MSManuscriptGammaMatrix.topPrecision k
      (parameters e A hA hN x y hl hd s).threshold)⁻¹ ≤ precisionInv (Fintype.card ι) :=
  MSManuscriptPolynomialQueryParameters.topPrecision_inverse_le (hk.trans (live_le_original x y))
    (config e A hA hN x y hl hd).threshold_pos (threshold_inverse_le e A hA hN x y hl hd s)

theorem query_inverses (s : MSManuscriptNumericalEpochLedger.State (Fintype.card (Live y.val)))
    (k : ℕ) (hk : k ≤ Fintype.card (Live y.val)) (hk0 : 0 < k) :
    let P := parameters e A hA hN x y hl hd s
    let L := MSManuscriptGammaInputBoundScaled.secondCap k d P.centerCap P.regularizer P.floor
      (Fintype.card (Live y.val))
    let η := MSManuscriptGammaMatrix.topPrecision k P.threshold
    (MSManuscriptGammaDifference.stepSize P.floor L η)⁻¹ ≤ slopeStepInv (Fintype.card ι) d ∧
    (MSManuscriptGammaDifference.valueTolerance P.floor L η)⁻¹ ≤ valueInv (Fintype.card ι) d := by
  dsimp only
  have hL0 := MSManuscriptGammaInputBoundScaled.secondCap_nonneg
    (k:=k) (d:=d) (δ:=(1/8192)) (L:=(Fintype.card (Live y.val):ℝ))
    (centerCap_nonneg e A hA hN x y hl hd s) (by norm_num : (0:ℝ)<1)
  have hη := MSManuscriptGammaMatrix.topPrecision_pos hk0
    (config e A hA hN x y hl hd).threshold_pos
  have hL := secondCap_le e A hA hN x y hl hd s k hk
  have hi := topPrecision_inverse_le e A hA hN x y hl hd s k hk
  exact ⟨slopeStep_inverse_le hL0 hη hL hi, valueTolerance_inverse_le hL0 hη hL hi⟩

theorem paidSize_inverse_le (s : MSManuscriptNumericalEpochRun.Certified
    (config e A hA hN x y hl hd)) :
    (MSManuscriptSupportedPaid.paidSize (parameters e A hA hN x y hl hd s.val))⁻¹ ≤
      paidInv (Fintype.card ι) d :=
  MSManuscriptPolynomialQueryParameters.paidSize_inverse_le _
    (MSManuscriptNumericalEpochRun.params_valid _ s) rfl
    (curvatureBudget_le e A hA hN x y hl hd s.val)
    (threshold_inverse_le e A hA hN x y hl hd s.val)

theorem preparation_budget_le (s : MSManuscriptNumericalEpochRun.Certified
    (config e A hA hN x y hl hd)) :
    MSManuscriptSupportedPreparation.budget (parameters e A hA hN x y hl hd s.val) ≤
      preparation (Fintype.card ι) d :=
  MSManuscriptPolynomialQueryParameters.preparation_budget_le _
    (MSManuscriptNumericalEpochRun.params_valid _ s) (live_le_original x y)
    (paidSize_inverse_le e A hA hN x y hl hd s)

end MatrixSpencer.MSManuscriptPolynomialQueryFactory
