import MatrixSpencer.KSFullManuscriptQueries
import MatrixSpencer.KSDebitWalkRun



open Set
noncomputable section
namespace MatrixSpencer.KSFullManuscriptController

open KSDebitWalkRun KSFullManuscriptDebitValue KSFullManuscriptParameters
variable {N d : ℕ} [Nonempty (Fin d)]

abbrev Prepared (v : Fin N → Fin d → ℂ) (δ η θ : ℝ) (hd : 0 < d) :=
  PreparedState N δ η (controllerReport v δ η θ hd)

def liveDirection (v : Fin N → Fin d → ℂ) (δ η θ M : ℝ) (hd : 0 < d)
    (s : Prepared v δ η θ hd) (hs : ¬terminal s) :
    EuclideanSpace ℝ (Fin (KSLiveEnumeration.count s.coeff)) :=
  KSFullManuscriptHessian.output (KSFullManuscriptQueries.faceReport v δ η θ hd M s.coeff)
    0 (KSFullManuscriptLiveCoordinates.weight s.coeff) N δ M
    (KSLiveEnumeration.count_pos_of_not_vertex s.cube hs)

def numericalDirection (v : Fin N → Fin d → ℂ) (δ η θ M : ℝ) (hd : 0 < d)
    (s : Prepared v δ η θ hd) : EuclideanSpace ℝ (Fin N) := by
  classical
  exact if hs : terminal s then 0 else KSLiveEnumeration.extend s.coeff
    (liveDirection v δ η θ M hd s hs)

theorem liveDirection_norm (v : Fin N → Fin d → ℂ) (δ η θ M : ℝ) (hd : 0 < d)
    (s : Prepared v δ η θ hd) (hs : ¬terminal s) :
    ‖liveDirection v δ η θ M hd s hs‖ = 1 := by
  unfold liveDirection KSFullManuscriptHessian.output
  exact KSJacobiRayleigh.outputVector_norm _ _ _

theorem numericalDirection_norm (v : Fin N → Fin d → ℂ) (δ η θ M : ℝ) (hd : 0 < d)
    (s : Prepared v δ η θ hd) (hs : ¬terminal s) :
    ‖numericalDirection v δ η θ M hd s‖ = 1 := by
  rw [numericalDirection, dif_neg hs, KSLiveEnumeration.extend_norm]
  exact liveDirection_norm v δ η θ M hd s hs

theorem numericalDirection_frozen (v : Fin N → Fin d → ℂ) (δ η θ M : ℝ) (hd : 0 < d)
    (s : Prepared v δ η θ hd) (hs : ¬terminal s) (i : Fin N) (hi : |s.coeff i| = 1) :
    numericalDirection v δ η θ M hd s i = 0 := by
  rw [numericalDirection, dif_neg hs]
  exact KSLiveEnumeration.extend_frozen s.coeff _ i hi

/-- The finite numerical controller has no report or direction oracle fields. -/
def controller (v : Fin N → Fin d → ℂ) (hN : 0 < N) {δ η θ M : ℝ}
    (hδ : 0 < δ) (hη : 0 < η) (hθ : 0 < θ) (hM : 0 < M) (hd : 0 < d) :
    Controller N (Fin d) where
  vectors := v
  δ := δ
  δ_pos := hδ
  η := η
  η_nonneg := hη.le
  θ := θ
  θ_pos := hθ
  report := controllerReport v δ η θ hd
  accuracy := controller_accuracy v δ hη hθ.le hd
  stepSize := movementStep N δ M
  step_pos := movementStep_pos hN hδ hM
  step_le := movementStep_le_quarter N δ M
  direction := numericalDirection v δ η θ M hd
  direction_norm := numericalDirection_norm v δ η θ M hd
  direction_frozen := numericalDirection_frozen v δ η θ M hd

/-- The actual finite binary history tree, with terminal absorption. -/
def run (v : Fin N → Fin d → ℂ) (hN : 0 < N) {δ η θ M : ℝ}
    (hδ : 0 < δ) (hη : 0 < η) (hθ : 0 < θ) (hM : 0 < M) (hd : 0 < d) (T : ℕ) :=
  KSDebitWalkRun.run (controller v hN hδ hη hθ hM hd) T
    (KSDebitWalkRun.initialState (controller v hN hδ hη hθ hM hd))

/-- Every actual trajectory stays in the cube, before the output filter. -/
theorem leaf_mem_cube (v : Fin N → Fin d → ℂ) (hN : 0 < N) {δ η θ M : ℝ}
    (hδ : 0 < δ) (hη : 0 < η) (hθ : 0 < θ) (hM : 0 < M) (hd : 0 < d) (T : ℕ)
    (l : (run v hN hδ hη hθ hM hd T).Leaves) :
    ((run v hN hδ hη hθ hM hd T).leafState l).coeff ∈ ksCube 1 :=
  ((run v hN hδ hη hθ hM hd T).leafState l).cube

end MatrixSpencer.KSFullManuscriptController
