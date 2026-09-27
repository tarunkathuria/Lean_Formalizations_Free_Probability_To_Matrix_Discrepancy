import SeamlessKS.OutwardSelection
import SeamlessKS.LocalNumerics
import SeamlessKS.Parameters
import MatrixSpencer.KSFullManuscriptLiveCoordinates
import MatrixSpencer.KSComplexNorm

/-! The concrete finite-value local walk. No direction or drift is supplied.
The value callback is the affine SDP solver; spectral selection uses the
fixed exact-EVD primitive of the extended computational model. -/
open Set Matrix
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace SeamlessKS.Walk
open MatrixSpencer SeamlessKS.State SeamlessKS.StatePotential SeamlessKS.Proposals
open SeamlessKS.Parameters
open MatrixSpencer.KSLiveEnumeration (count liveEquiv)
open MatrixSpencer.KSFullManuscriptLiveCoordinates (face)
attribute [local instance] Classical.propDecidable

variable {N d : ℕ}
abbrev WalkState (N : ℕ) := PreparedState N (rho N)

def terminal (s : WalkState N) : Prop := State.terminal s.toCubeState

theorem liveCount_pos (s : WalkState N) (hs : ¬terminal s) : 0<count s.coeff := by
  apply KSLiveEnumeration.count_pos_of_not_vertex s.cube
  intro hv
  apply hs
  intro i
  rcases hv i with hi|hi <;> rw [hi] <;> norm_num

def liveWeights (s : WalkState N) : Fin (count s.coeff) → ℝ :=
  NormalizedHessian.sourceWeight (zeta N) (fun i => s.coeff (liveEquiv s.coeff i))

def faceReport [Nonempty (Fin d)] (O : KSConvexValueOracle.Solver)
    (v : Fin N → Fin d → ℂ) (s : WalkState N)
    (z : EuclideanSpace ℝ (Fin (count s.coeff))) : ℝ :=
  Value.report O v 0 (Input.theta v) (zeta N) (hessianAccuracy v)
    (face s.coeff z)

def liveOutput [Nonempty (Fin d)] (O : KSConvexValueOracle.Solver)
    (v : Fin N → Fin d → ℂ) (s : WalkState N) (hs : ¬terminal s) :
    EuclideanSpace ℝ (Fin (count s.coeff)) :=
  LocalNumerics.output (faceReport O v s) 0 (liveWeights s) N (rho N) (beta v)
    (derivativeBudget v) (liveCount_pos s hs)

def direction [Nonempty (Fin d)] (O : KSConvexValueOracle.Solver)
    (v : Fin N → Fin d → ℂ) (s : WalkState N) (hs : ¬terminal s) : EuclideanSpace ℝ (Fin N) :=
  KSLiveEnumeration.extend s.coeff (liveOutput O v s hs)

theorem direction_norm [Nonempty (Fin d)] (O : KSConvexValueOracle.Solver)
    (v : Fin N → Fin d → ℂ) (s : WalkState N) (hs : ¬terminal s) :
    ‖direction O v s hs‖=1 := by
  rw [direction,KSLiveEnumeration.extend_norm]
  exact ExactEVD.output_norm _ _

theorem direction_frozen [Nonempty (Fin d)] (O : KSConvexValueOracle.Solver)
    (v : Fin N → Fin d → ℂ) (s : WalkState N) (hs : ¬terminal s)
    (i : Fin N) (hi : |s.coeff i|=1) : direction O v s hs i=0 :=
  KSLiveEnumeration.extend_frozen s.coeff _ i hi

def chosenLabel [Nonempty (Fin d)] (O : KSConvexValueOracle.Solver)
    (v : Fin N → Fin d → ℂ) (s : WalkState N) : Option (Fin N) :=
  OutwardSelection.select O v (Input.theta v) (zeta N) (localAccuracy v) (outwardStep N) s

def signedStep (v : Fin N → Fin d → ℂ) (b : Bool) : ℝ :=
  if b then movementStep v else -movementStep v

theorem signedStep_bound (v : Fin N → Fin d → ℂ) (hd : 0<d)
    (hp : ∑ i,KSRankOne.atom (v i)=1) (b : Bool) : |signedStep v b|≤rho N/16 := by
  have hh := movementStep_pos v hd hp
  cases b <;> simpa only [signedStep,Bool.false_eq_true,↓reduceIte,abs_neg,abs_of_pos hh] using
    movementStep_le_outwardStep v

/-- The ordinary movement before the separate near-boundary rounding. -/
def rawStep [Nonempty (Fin d)] (O : KSConvexValueOracle.Solver)
    (v : Fin N → Fin d → ℂ) (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1)
    (s : WalkState N) (hs : ¬terminal s) (b : Bool) : CubeState N (rho N) :=
  match hi : chosenLabel O v s with
  | some i => outwardMove (rho_pos (Input.labels_pos v hd hp)) s i
      (OutwardSelection.selected_live O v _ _ _ _ s i hi)
      (outwardStep N) (outwardStep_pos (Input.labels_pos v hd hp)).le
      (by unfold outwardStep; have hr := rho_pos (Input.labels_pos v hd hp); linarith)
  | none => symmetricMove (rho_pos (Input.labels_pos v hd hp))
      (zeta_pos (Input.labels_pos v hd hp)).le s (direction O v s hs)
      (direction_norm O v s hs) (signedStep v b) (signedStep_bound v hd hp b)

/-- Absorb completed states; otherwise move and prepare at the true cube boundary. -/
def step [Nonempty (Fin d)] (O : KSConvexValueOracle.Solver)
    (v : Fin N → Fin d → ℂ) (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1)
    (s : WalkState N) (b : Bool) : WalkState N :=
  if hs : terminal s then s else
    prepare (rho_pos (Input.labels_pos v hd hp)).le (rawStep O v hd hp s hs b)

theorem step_terminal [Nonempty (Fin d)] (O : KSConvexValueOracle.Solver)
    (v : Fin N → Fin d → ℂ) (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1)
    (s : WalkState N) (hs : terminal s) (b : Bool) : step O v hd hp s b=s := by
  simp only [step,dif_pos hs]

def initial (v : Fin N → Fin d → ℂ) (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1) : WalkState N :=
  prepare (rho_pos (Input.labels_pos v hd hp)).le (State.initial (rho_pos (Input.labels_pos v hd hp)).le)

def normReport (v : Fin N → Fin d → ℂ) (s : WalkState N) : ℝ :=
  ExactEVD.normReport (KSComplexTraceSqrt.realificationFin (signedSum v s.coeff))

theorem normReport_accuracy (v : Fin N → Fin d → ℂ) (hd : 0<d)
    (hp : ∑ i,KSRankOne.atom (v i)=1) (s : WalkState N) :
    |normReport v s-‖signedSum v s.coeff‖|≤Input.delta v := by
  unfold normReport
  rw [ExactEVD.normReport_exact _ (KSComplexNorm.realificationFin_symmetric _
    (signedSum_isHermitian v s.coeff)), KSComplexNorm.realificationFin_norm, sub_self, abs_zero]
  exact Input.delta_nonneg v

end SeamlessKS.Walk
