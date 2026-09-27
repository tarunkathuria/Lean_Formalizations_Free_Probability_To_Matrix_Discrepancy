import SeamlessKS.NumericQueries
import SeamlessKS.LiveHessian
import SeamlessKS.WalkGeometry

/-! Drift of the actual value-query walk. The only internal analytic interface
records actual fourth derivatives of the explicitly defined smooth potential;
it contains no branch, direction, Hessian-oracle, or drift assumption. -/
open Matrix Set
open scoped BigOperators Topology MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
noncomputable section
namespace SeamlessKS.WalkDrift
open MatrixSpencer SeamlessKS.State SeamlessKS.StatePotential SeamlessKS.LivePotential
open SeamlessKS.Parameters SeamlessKS.Walk
open MatrixSpencer.KSLiveEnumeration (count liveEquiv)
variable {N d : ℕ}

structure AnalyticBounds (v : Fin N → Fin d → ℂ) (s : WalkState N) : Prop where
  query : KSFullManuscriptHessian.LineBounds
    (faceValue v (Input.theta v) (zeta N) s.toCubeState) 0 (queryStep v) (derivativeBudget v)
  movement : ∀ w : EuclideanSpace ℝ (Fin (count s.coeff)), ‖w‖=1 →
    ContDiffOn ℝ 4
      (fun t : ℝ => faceValue v (Input.theta v) (zeta N) s.toCubeState
        (t • NormalizedHessian.diagonalMap (liveWeights s) w))
      (Icc (-movementStep v) (movementStep v)) ∧
    ∀ t ∈ Icc (-movementStep v) (movementStep v),
      |iteratedDeriv 4
        (fun q : ℝ => faceValue v (Input.theta v) (zeta N) s.toCubeState
          (q • NormalizedHessian.diagonalMap (liveWeights s) w)) t|≤derivativeBudget v

theorem output_curvature [Nonempty (Fin d)] (O : KSConvexValueOracle.Solver)
    (v : Fin N → Fin d → ℂ) (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1)
    (s : WalkState N) (hs : ¬Walk.terminal s) (hb : AnalyticBounds v s)
    (hn : chosenLabel O v s=none) :
    ‖liveOutput O v s hs‖=1 ∧
    KSRayleighAccuracy.realRayleigh
      (KSFullManuscriptHessian.weighted (liveWeights s)
        (KSNumericalHessian.hessian (faceValue v (Input.theta v) (zeta N) s.toCubeState) 0))
      (liveOutput O v s hs)<beta v/2 := by
  have hN := Input.labels_pos v hd hp
  have hB := (debit_bounds v hp s.toCubeState).1
  have hθ := Input.theta_pos v hd hp
  have hζ := zeta_pos hN
  have hρ := rho_pos hN
  have hnegative := LiveHessian.leastRayleigh_neg_of_none O v s (liveCount_pos s hs) hB
    hθ (localAccuracy_pos v hd hp) hρ hζ (outwardStep_pos hN) (zeta_eq N).le
    (by unfold outwardStep; linarith) hn
  have hf := (contDiffAt_faceValue v s.toCubeState hB hθ hζ).of_le
    (WithTop.coe_le_coe.mpr (show (2 : ℕ∞)≤⊤ from le_top))
  exact LocalNumerics.output_curvature _ _ 0 (liveWeights s)
    (NormalizedHessian.sourceWeight_sq_le_two hζ.le (livePositions s.coeff)
      (fun i => (livePositions_interior s.coeff i).le))
    (liveCount_pos s hs) (NumericQueries.liveCount_le s.coeff) hρ
    (beta_pos v hd hp) (derivativeBudget_pos v hd hp) hf hb.query
    (NumericQueries.queryAccuracy O v hd hp s) hnegative.le

theorem rawStep_none_potential [Nonempty (Fin d)] (O : KSConvexValueOracle.Solver)
    (v : Fin N → Fin d → ℂ) (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1)
    (s : WalkState N) (hs : ¬Walk.terminal s) (hn : chosenLabel O v s=none) (b : Bool) :
    potential v (Input.theta v) (zeta N) (rawStep O v hd hp s hs b)=
    faceValue v (Input.theta v) (zeta N) s.toCubeState
      (signedStep v b • NormalizedHessian.diagonalMap (liveWeights s) (liveOutput O v s hs)) := by
  rw [WalkGeometry.rawStep_none O v hd hp s hs hn b]
  unfold faceValue
  rw [show liveWeights s = NormalizedHessian.sourceWeight (zeta N) (livePositions s.coeff) from rfl]
  rw [face_weighted_proposal]
  rfl

theorem rawStep_symmetric_drift [Nonempty (Fin d)] (O : KSConvexValueOracle.Solver)
    (v : Fin N → Fin d → ℂ) (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1)
    (s : WalkState N) (hs : ¬Walk.terminal s) (hb : AnalyticBounds v s)
    (hn : chosenLabel O v s=none) :
    (potential v (Input.theta v) (zeta N) (rawStep O v hd hp s hs false)+
      potential v (Input.theta v) (zeta N) (rawStep O v hd hp s hs true))/2≤
    potential v (Input.theta v) (zeta N) s.toCubeState+beta v*movementStep v^2 := by
  have hN := Input.labels_pos v hd hp
  have hB := (debit_bounds v hp s.toCubeState).1
  have hc := output_curvature O v hd hp s hs hb hn
  have hf := (contDiffAt_faceValue v s.toCubeState hB (Input.theta_pos v hd hp)
    (zeta_pos hN)).of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞)≤⊤ from le_top))
  have hline := hb.movement (liveOutput O v s hs) hc.1
  have hbudget : derivativeBudget v*movementStep v^2≤beta v :=
    LocalNumerics.movement_remainder_budget (rho_pos hN) (beta_pos v hd hp)
      (derivativeBudget_pos v hd hp)
  have hav := LocalNumerics.symmetric_average_le
    (faceValue v (Input.theta v) (zeta N) s.toCubeState) 0 (liveOutput O v s hs) (liveWeights s)
    (movementStep_pos v hd hp) (beta_pos v hd hp).le hf
    (by simpa only [zero_add] using hline.1)
    (by simpa only [zero_add] using hline.2) hc.2.le hbudget
  rw [rawStep_none_potential O v hd hp s hs hn false,rawStep_none_potential O v hd hp s hs hn true]
  simp only [zero_add,zero_sub,faceValue_zero] at hav
  simp only [signedStep,Bool.false_eq_true,↓reduceIte,neg_smul]
  linarith

theorem rawStep_drift [Nonempty (Fin d)] (O : KSConvexValueOracle.Solver)
    (v : Fin N → Fin d → ℂ) (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1)
    (s : WalkState N) (hs : ¬Walk.terminal s) (hb : AnalyticBounds v s) :
    (potential v (Input.theta v) (zeta N) (rawStep O v hd hp s hs false)+
      potential v (Input.theta v) (zeta N) (rawStep O v hd hp s hs true))/2≤
    potential v (Input.theta v) (zeta N) s.toCubeState+beta v*movementStep v^2 := by
  cases hi : chosenLabel O v s with
  | none => exact rawStep_symmetric_drift O v hd hp s hs hb hi
  | some i =>
    have hN := Input.labels_pos v hd hp
    have hρ := rho_pos hN
    have hh := OutwardSelection.selected_drift O v (Input.theta_pos v hd hp)
      (localAccuracy_pos v hd hp) hρ (outwardStep_pos hN).le
      (by unfold outwardStep; linarith) s i hi
    rw [WalkGeometry.rawStep_some O v hd hp s hs i hi false,
      WalkGeometry.rawStep_some O v hd hp s hs i hi true]
    rw [local_error_budget] at hh
    have hp0 := mul_nonneg (beta_pos v hd hp).le (sq_nonneg (movementStep v))
    linarith

theorem step_drift [Nonempty (Fin d)] (O : KSConvexValueOracle.Solver)
    (v : Fin N → Fin d → ℂ) (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1)
    (s : WalkState N) (hs : ¬Walk.terminal s) (hb : AnalyticBounds v s) :
    (account v (Input.theta v) (zeta N) (Walk.step O v hd hp s false).toCubeState+
      account v (Input.theta v) (zeta N) (Walk.step O v hd hp s true).toCubeState)/2≤
    account v (Input.theta v) (zeta N) s.toCubeState+beta v*movementStep v^2 := by
  have hρ := (rho_pos (Input.labels_pos v hd hp)).le
  have hθ := Input.theta_pos v hd hp
  have hf := prepare_account_nonincreasing hρ v hθ (zeta N) (rawStep O v hd hp s hs false)
  have ht := prepare_account_nonincreasing hρ v hθ (zeta N) (rawStep O v hd hp s hs true)
  have hrf := reserve_mono v s.toCubeState (rawStep O v hd hp s hs false)
    (WalkGeometry.rawStep_preserves_frozen O v hd hp s hs false)
  have hrt := reserve_mono v s.toCubeState (rawStep O v hd hp s hs true)
    (WalkGeometry.rawStep_preserves_frozen O v hd hp s hs true)
  have hr := rawStep_drift O v hd hp s hs hb
  simp only [Walk.step,dif_neg hs]
  unfold account at hf ht ⊢
  linarith

end SeamlessKS.WalkDrift
