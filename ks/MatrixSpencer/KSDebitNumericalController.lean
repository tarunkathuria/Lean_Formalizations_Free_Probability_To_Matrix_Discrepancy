import MatrixSpencer.KSDebitHessianQueries

/-!
# The explicit numerical debit-walk controller

The controller uses the computed potential report, finite Hessian stencils,
and actual Jacobi direction on the enumerated live block. All controller
fields are proved. The scalar `M` is still a parameter: its adequacy as a
uniform fourth-derivative bound, and hence the local potential drift, are
separate obligations before this is a primitive-input success theorem.
-/

open Set
noncomputable section
namespace MatrixSpencer.KSDebitNumericalController

open KSDebitWalkRun KSDebitNumericalValue KSControllerParameters
variable {N d : ℕ} [Nonempty (Fin d)]

def numericalDirection (v : Fin N → Fin d → ℂ) (δ η θ M : ℝ) (hd : 0 < d)
    (s : PreparedState N δ η (controllerReport v δ η θ hd)) : EuclideanSpace ℝ (Fin N) := by
  classical
  exact if hs : terminal s then 0 else
    KSLiveEnumeration.extend s.coeff
      (KSNumericalHessian.output (KSDebitHessianQueries.faceReport v δ η θ hd M s.coeff)
        0 (hessianRadius δ) M (curvatureTolerance N δ)
        (KSLiveEnumeration.count_pos_of_not_vertex s.cube hs))

theorem numericalDirection_norm (v : Fin N → Fin d → ℂ) (δ η θ M : ℝ) (hd : 0 < d)
    (s : PreparedState N δ η (controllerReport v δ η θ hd)) (hs : ¬terminal s) :
    ‖numericalDirection v δ η θ M hd s‖ = 1 := by
  rw [numericalDirection, dif_neg hs, KSLiveEnumeration.extend_norm]
  exact KSJacobiRayleigh.outputVector_norm _ _ _

theorem numericalDirection_frozen (v : Fin N → Fin d → ℂ) (δ η θ M : ℝ) (hd : 0 < d)
    (s : PreparedState N δ η (controllerReport v δ η θ hd)) (hs : ¬terminal s)
    (i : Fin N) (hi : |s.coeff i| = 1) : numericalDirection v δ η θ M hd s i = 0 := by
  rw [numericalDirection, dif_neg hs]
  exact KSLiveEnumeration.extend_frozen s.coeff _ i hi

/-- The actual finite numerical controller: report accuracy and every
geometric direction/step field are discharged by the previous constructions. -/
def controller (v : Fin N → Fin d → ℂ) {δ η θ M : ℝ}
    (hδ : 0 < δ) (hη : 0 < η) (hθ : 0 < θ) (hM : 0 ≤ M) (hd : 0 < d) :
    Controller N (Fin d) where
  vectors := v
  δ := δ
  δ_pos := hδ
  η := η
  η_nonneg := hη.le
  θ := θ
  θ_pos := hθ
  report := controllerReport v δ η θ hd
  accuracy := controller_accuracy v hδ.le hη hθ hd
  stepSize := movementStep N δ M
  step_pos := movementStep_pos N hδ hM
  step_le := movementStep_le_quarter N δ M
  direction := numericalDirection v δ η θ M hd
  direction_norm := numericalDirection_norm v δ η θ M hd
  direction_frozen := numericalDirection_frozen v δ η θ M hd

/-- Starting and stepping this controller are the already-defined actual
preparation/movement operations, with the finite numerical fields above. -/
def run (v : Fin N → Fin d → ℂ) {δ η θ M : ℝ}
    (hδ : 0 < δ) (hη : 0 < η) (hθ : 0 < θ) (hM : 0 ≤ M) (hd : 0 < d) (T : ℕ) :=
  KSDebitWalkRun.run (controller v hδ hη hθ hM hd) T
    (KSDebitWalkRun.initialState (controller v hδ hη hθ hM hd))

end MatrixSpencer.KSDebitNumericalController
