import RadialKS.WalkGeometry
import SeamlessKS.AnalyticBounds

/-! Deterministic potential descent for the concrete radial walk. Every
regularity, approximation and negative-curvature fact is derived internally. -/
open Matrix Set
open scoped BigOperators Topology MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
noncomputable section
namespace RadialKS.WalkDrift
open MatrixSpencer SeamlessKS SeamlessKS.State SeamlessKS.StatePotential SeamlessKS.LivePotential
open SeamlessKS.Parameters RadialKS.Walk
open MatrixSpencer.KSLiveEnumeration (count liveEquiv)
open MatrixSpencer.KSFullManuscriptLiveCoordinates (face)
variable {N d : ℕ} [Nonempty (Fin d)]

theorem output_curvature (O : KSConvexValueOracle.Solver)
    (v : Fin N → Fin d → ℂ) (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1)
    (s : WalkState N) (hs : ¬Walk.terminal s) (hn : chosenLabel O v s=none) :
    KSRayleighAccuracy.realRayleigh
      (RawNumerics.half (KSNumericalHessian.hessian
        (faceValue v (Input.theta v) (zeta N) s.toCubeState) 0))
      (liveOutput O v hd hp s hs hn)<beta v/2 := by
  have hN := Input.labels_pos v hd hp
  have hB := (debit_bounds v hp s.toCubeState).1
  obtain ⟨g,hg,ho,hneg⟩ := RadialKS.LiveHessian.exists_unit_raw_negative_of_none O v s
    (SeamlessKS.Walk.liveCount_pos s hs) hB (Input.theta_pos v hd hp)
    (localAccuracy_pos v hd hp) (rho_pos hN) (zeta_pos hN) (outwardStep_pos hN)
    (zeta_eq N).le (by unfold outwardStep; have hr := rho_pos hN; linarith) hn
  have horth : inner ℝ (position s) g = 0 := by
    simp only [PiLp.inner_apply,RCLike.inner_apply']
    exact ho
  have hf := (contDiffAt_faceValue v s.toCubeState hB (Input.theta_pos v hd hp) (zeta_pos hN)).of_le
    (WithTop.coe_le_coe.mpr (show (2 : ℕ∞)≤⊤ from le_top))
  exact RawNumerics.output_curvature _ _ 0 (position s) hN (NumericQueries.liveCount_le s.coeff)
    (rho_pos hN) (beta_pos v hd hp) (derivativeBudget_pos v hd hp) hf
    (SeamlessKS.AnalyticBounds.analyticBounds v hd hp s).query
    (NumericQueries.queryAccuracy O v hd hp s) (rank_pos O v hd hp s hs hn) g hg horth hneg

theorem endpointReport_accuracy (O : KSConvexValueOracle.Solver)
    (v : Fin N → Fin d → ℂ) (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1)
    (s : WalkState N) (g : EuclideanSpace ℝ (Fin (count s.coeff))) (hg : ‖g‖=1) (b : Bool) :
    |endpointReport O v s g b - faceValue v (Input.theta v) (zeta N) s.toCubeState
      (signedStep v b • g)| ≤ localAccuracy v := by
  have hr := rho_pos (Input.labels_pos v hd hp)
  have hz : ‖signedStep v b • g‖ < rho N := by
    rw [norm_smul,Real.norm_eq_abs,hg,mul_one]
    have h := SeamlessKS.Walk.signedStep_bound v hd hp b
    linarith
  exact Value.report_accuracy O v 0 (Input.theta_pos v hd hp)
    (localAccuracy_pos v hd hp) _
    (KSFullManuscriptLiveCoordinates.face_mem_cube s.cube _
      (fun i hi => (s.margin i hi).le) hz)

theorem face_proposal (x : Fin N → ℝ)
    (g : EuclideanSpace ℝ (Fin (count x))) (t : ℝ) :
    face x (t • g) = Progress.proposal x (KSLiveEnumeration.extend x g) t := by
  funext i
  rw [face,map_smul,KSFullManuscriptLiveCoordinates.linear_apply]
  rfl

theorem rawStep_none_potential (O : KSConvexValueOracle.Solver)
    (v : Fin N → Fin d → ℂ) (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1)
    (s : WalkState N) (hs : ¬Walk.terminal s) (hn : chosenLabel O v s=none) :
    potential v (Input.theta v) (zeta N) (rawStep O v hd hp s hs)=
    faceValue v (Input.theta v) (zeta N) s.toCubeState
      (signedStep v (chooseSign O v hd hp s hs hn) • liveOutput O v hd hp s hs hn) := by
  rw [WalkGeometry.rawStep_none O v hd hp s hs hn]
  unfold faceValue
  rw [face_proposal]
  rfl

theorem rawStep_radial_drift (O : KSConvexValueOracle.Solver)
    (v : Fin N → Fin d → ℂ) (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1)
    (s : WalkState N) (hs : ¬Walk.terminal s) (hn : chosenLabel O v s=none) :
    potential v (Input.theta v) (zeta N) (rawStep O v hd hp s hs) ≤
      potential v (Input.theta v) (zeta N) s.toCubeState+beta v*movementStep v^2 := by
  have hN := Input.labels_pos v hd hp
  have hB := (debit_bounds v hp s.toCubeState).1
  have hg := liveOutput_norm O v hd hp s hs hn
  have hc := output_curvature O v hd hp s hs hn
  have hf := (contDiffAt_faceValue v s.toCubeState hB (Input.theta_pos v hd hp)
    (zeta_pos hN)).of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞)≤⊤ from le_top))
  have hline := SeamlessKS.AnalyticBounds.face_line_bounds v hd hp s
    (liveOutput O v hd hp s hs hn) (fun i => by
      have hi := PiLp.norm_apply_le (liveOutput O v hd hp s hs hn) i
      rw [hg,Real.norm_eq_abs] at hi
      exact hi.trans (by norm_num))
    (movementStep v) (min_le_left _ _)
  have hbudget : derivativeBudget v*movementStep v^2≤beta v :=
    LocalNumerics.movement_remainder_budget (rho_pos hN) (beta_pos v hd hp)
      (derivativeBudget_pos v hd hp)
  have hp' := endpointReport_accuracy O v hd hp s _ hg true
  have hm' := endpointReport_accuracy O v hd hp s _ hg false
  have hav := RawNumerics.chosen_potential
    (faceValue v (Input.theta v) (zeta N) s.toCubeState) 0 (liveOutput O v hd hp s hs hn)
    (movementStep_pos v hd hp) (beta_pos v hd hp).le hf
    (by simpa only [zero_add] using hline.1)
    (by simpa only [zero_add] using hline.2) hc.le hbudget
    (show localAccuracy v ≤ beta v * movementStep v^2 / 8 from le_rfl)
    (by simpa only [signedStep,SeamlessKS.Walk.signedStep,↓reduceIte,zero_add] using hp')
    (by simpa only [signedStep,SeamlessKS.Walk.signedStep,Bool.false_eq_true,↓reduceIte,
      zero_sub,neg_smul] using hm')
  rw [rawStep_none_potential O v hd hp s hs hn]
  simp only [zero_add,zero_sub,faceValue_zero] at hav
  change (if chooseSign O v hd hp s hs hn then _ else _) ≤ _ at hav
  cases hb : chooseSign O v hd hp s hs hn <;>
    simpa only [signedStep,SeamlessKS.Walk.signedStep,hb,Bool.false_eq_true,↓reduceIte,
      neg_smul] using hav

theorem rawStep_drift (O : KSConvexValueOracle.Solver)
    (v : Fin N → Fin d → ℂ) (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1)
    (s : WalkState N) (hs : ¬Walk.terminal s) :
    potential v (Input.theta v) (zeta N) (rawStep O v hd hp s hs) ≤
      potential v (Input.theta v) (zeta N) s.toCubeState+beta v*movementStep v^2 := by
  cases hi : chosenLabel O v s with
  | none => exact rawStep_radial_drift O v hd hp s hs hi
  | some i =>
    have hN := Input.labels_pos v hd hp
    have hr := rho_pos hN
    have hh := OutwardSelection.selected_drift O v (Input.theta_pos v hd hp)
      (localAccuracy_pos v hd hp) hr (outwardStep_pos hN).le
      (by unfold outwardStep; linarith) s i hi
    rw [WalkGeometry.rawStep_some O v hd hp s hs i hi]
    rw [local_error_budget] at hh
    have hb := mul_nonneg (beta_pos v hd hp).le (sq_nonneg (movementStep v))
    linarith

theorem step_budget (O : KSConvexValueOracle.Solver)
    (v : Fin N → Fin d → ℂ) (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1)
    (s : WalkState N) :
    DeterministicRun.budget v (Input.theta v) (zeta N) (beta v) (Walk.step O v hd hp s).toCubeState ≤
      DeterministicRun.budget v (Input.theta v) (zeta N) (beta v) s.toCubeState := by
  by_cases hs : Walk.terminal s
  · rw [Walk.step_terminal O v hd hp s hs]
  · have hm := DeterministicRun.movement_budget v (Input.theta v) (zeta N)
      (beta_pos v hd hp).le s.toCubeState (rawStep O v hd hp s hs)
      (WalkGeometry.rawStep_preserves_frozen O v hd hp s hs)
      (rawStep_drift O v hd hp s hs) (WalkGeometry.rawStep_energy O v hd hp s hs)
    have hp' := DeterministicRun.prepare_budget (rho_pos (Input.labels_pos v hd hp)).le v
      (Input.theta_pos v hd hp) (zeta N) (beta_pos v hd hp).le (rawStep O v hd hp s hs)
    simp only [Walk.step,dif_neg hs]
    exact hp'.trans hm

end RadialKS.WalkDrift
