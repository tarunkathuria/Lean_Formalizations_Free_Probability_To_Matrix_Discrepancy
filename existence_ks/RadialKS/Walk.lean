import RadialKS.RawNumerics
import RadialKS.LiveHessian
import SeamlessKS.Walk

/-! The deterministic physical radial walk, using actual SDP value reports
and exact EVD on the coefficient hyperplane orthogonal to the current state. -/
open Set Matrix
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace RadialKS.Walk
open MatrixSpencer SeamlessKS SeamlessKS.State SeamlessKS.StatePotential SeamlessKS.Proposals
open SeamlessKS.Parameters SeamlessKS.LivePotential
open MatrixSpencer.KSLiveEnumeration (count liveEquiv)
open MatrixSpencer.KSFullManuscriptLiveCoordinates (face)
attribute [local instance] Classical.propDecidable
variable {N d : ℕ}

abbrev WalkState (N : ℕ) := SeamlessKS.Walk.WalkState N
abbrev terminal (s : WalkState N) := SeamlessKS.Walk.terminal s
abbrev initial := @SeamlessKS.Walk.initial
abbrev chosenLabel := @SeamlessKS.Walk.chosenLabel
abbrev faceReport := @SeamlessKS.Walk.faceReport
abbrev signedStep := @SeamlessKS.Walk.signedStep

def position (s : WalkState N) : EuclideanSpace ℝ (Fin (count s.coeff)) :=
  WithLp.toLp 2 (livePositions s.coeff)

theorem rank_pos [Nonempty (Fin d)] (O : KSConvexValueOracle.Solver)
    (v : Fin N → Fin d → ℂ) (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1)
    (s : WalkState N) (hs : ¬terminal s) (hn : chosenLabel O v s=none) :
    0 < (Frame.canonical (count s.coeff) (position s)).rank := by
  have hN := Input.labels_pos v hd hp
  obtain ⟨g,hg,ho,_⟩ := RadialKS.LiveHessian.exists_unit_raw_negative_of_none O v s
    (SeamlessKS.Walk.liveCount_pos s hs) (debit_bounds v hp s.toCubeState).1
    (Input.theta_pos v hd hp) (localAccuracy_pos v hd hp) (rho_pos hN)
    (zeta_pos hN) (outwardStep_pos hN) (zeta_eq N).le
    (by unfold outwardStep; have hr := rho_pos hN; linarith) hn
  apply Frame.rank_pos_of_nonzero _ g
  · intro he
    rw [he,norm_zero] at hg
    norm_num at hg
  · simp only [PiLp.inner_apply, RCLike.inner_apply']
    exact ho

def liveOutput [Nonempty (Fin d)] (O : KSConvexValueOracle.Solver)
    (v : Fin N → Fin d → ℂ) (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1)
    (s : WalkState N) (hs : ¬terminal s) (hn : chosenLabel O v s=none) :
    EuclideanSpace ℝ (Fin (count s.coeff)) :=
  RawNumerics.output (faceReport O v s) 0 (position s) N (rho N) (beta v)
    (derivativeBudget v) (rank_pos O v hd hp s hs hn)

theorem liveOutput_norm [Nonempty (Fin d)] (O : KSConvexValueOracle.Solver)
    (v : Fin N → Fin d → ℂ) (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1)
    (s : WalkState N) (hs : ¬terminal s) (hn : chosenLabel O v s=none) :
    ‖liveOutput O v hd hp s hs hn‖=1 := RawNumerics.output_norm _ _ _ _ _ _ _ _

theorem liveOutput_orthogonal [Nonempty (Fin d)] (O : KSConvexValueOracle.Solver)
    (v : Fin N → Fin d → ℂ) (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1)
    (s : WalkState N) (hs : ¬terminal s) (hn : chosenLabel O v s=none) :
    ∑ i, livePositions s.coeff i * liveOutput O v hd hp s hs hn i = 0 := by
  have h := RawNumerics.output_orthogonal (faceReport O v s) 0 (position s) N
    (rho N) (beta v) (derivativeBudget v) (rank_pos O v hd hp s hs hn)
  simp only [PiLp.inner_apply, RCLike.inner_apply'] at h
  exact h

def direction [Nonempty (Fin d)] (O : KSConvexValueOracle.Solver)
    (v : Fin N → Fin d → ℂ) (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1)
    (s : WalkState N) (hs : ¬terminal s) (hn : chosenLabel O v s=none) :
    EuclideanSpace ℝ (Fin N) :=
  KSLiveEnumeration.extend s.coeff (liveOutput O v hd hp s hs hn)

theorem direction_norm [Nonempty (Fin d)] (O : KSConvexValueOracle.Solver)
    (v : Fin N → Fin d → ℂ) (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1)
    (s : WalkState N) (hs : ¬terminal s) (hn : chosenLabel O v s=none) :
    ‖direction O v hd hp s hs hn‖=1 := by
  rw [direction,KSLiveEnumeration.extend_norm]
  exact liveOutput_norm O v hd hp s hs hn

theorem direction_frozen [Nonempty (Fin d)] (O : KSConvexValueOracle.Solver)
    (v : Fin N → Fin d → ℂ) (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1)
    (s : WalkState N) (hs : ¬terminal s) (hn : chosenLabel O v s=none)
    (i : Fin N) (hi : |s.coeff i|=1) : direction O v hd hp s hs hn i=0 :=
  KSLiveEnumeration.extend_frozen s.coeff _ i hi

theorem direction_orthogonal [Nonempty (Fin d)] (O : KSConvexValueOracle.Solver)
    (v : Fin N → Fin d → ℂ) (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1)
    (s : WalkState N) (hs : ¬terminal s) (hn : chosenLabel O v s=none) :
    ∑ i, s.coeff i * direction O v hd hp s hs hn i = 0 := by
  unfold direction
  rw [KSLiveCurve.sum_restrict_live 1 s.coeff
    (fun i => s.coeff i * KSLiveEnumeration.extend s.coeff (liveOutput O v hd hp s hs hn) i)
    (by intro i hi; dsimp only; rw [KSLiveEnumeration.extend_dead _ _ i hi, mul_zero])]
  simp only [KSLiveEnumeration.extend_live]
  have he := (liveEquiv s.coeff).symm.sum_comp
    (fun i => livePositions s.coeff i * liveOutput O v hd hp s hs hn i)
  simpa only [livePositions, Equiv.apply_symm_apply] using
    he.trans (liveOutput_orthogonal O v hd hp s hs hn)

def endpointReport [Nonempty (Fin d)] (O : KSConvexValueOracle.Solver)
    (v : Fin N → Fin d → ℂ) (s : WalkState N)
    (g : EuclideanSpace ℝ (Fin (count s.coeff))) (b : Bool) : ℝ :=
  Value.report O v 0 (Input.theta v) (zeta N) (localAccuracy v)
    (face s.coeff (signedStep v b • g))

def chooseSign [Nonempty (Fin d)] (O : KSConvexValueOracle.Solver)
    (v : Fin N → Fin d → ℂ) (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1)
    (s : WalkState N) (hs : ¬terminal s) (hn : chosenLabel O v s=none) : Bool :=
  DeterministicRun.choosePlus
    (endpointReport O v s (liveOutput O v hd hp s hs hn) true)
    (endpointReport O v s (liveOutput O v hd hp s hs hn) false)

def rawStep [Nonempty (Fin d)] (O : KSConvexValueOracle.Solver)
    (v : Fin N → Fin d → ℂ) (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1)
    (s : WalkState N) (hs : ¬terminal s) : CubeState N (rho N) :=
  match hi : chosenLabel O v s with
  | some i => outwardMove (rho_pos (Input.labels_pos v hd hp)) s i
      (OutwardSelection.selected_live O v _ _ _ _ s i hi)
      (outwardStep N) (outwardStep_pos (Input.labels_pos v hd hp)).le
      (by unfold outwardStep; have hr := rho_pos (Input.labels_pos v hd hp); linarith)
  | none => RadialKS.Progress.radialMove (rho_pos (Input.labels_pos v hd hp)) s
      (direction O v hd hp s hs hi) (direction_norm O v hd hp s hs hi)
      (direction_frozen O v hd hp s hs hi)
      (signedStep v (chooseSign O v hd hp s hs hi))
      (SeamlessKS.Walk.signedStep_bound v hd hp _)

def step [Nonempty (Fin d)] (O : KSConvexValueOracle.Solver)
    (v : Fin N → Fin d → ℂ) (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1)
    (s : WalkState N) : WalkState N :=
  if hs : terminal s then s else
    prepare (rho_pos (Input.labels_pos v hd hp)).le (rawStep O v hd hp s hs)

theorem step_terminal [Nonempty (Fin d)] (O : KSConvexValueOracle.Solver)
    (v : Fin N → Fin d → ℂ) (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1)
    (s : WalkState N) (hs : terminal s) : step O v hd hp s=s := by
  simp only [step,dif_pos hs]

end RadialKS.Walk
