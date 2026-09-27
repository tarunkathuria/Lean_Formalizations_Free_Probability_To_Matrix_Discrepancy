import MatrixSpencer.MSManuscriptPreparedMovement
import MatrixSpencer.MSConvexSupportedPreparation

/-! The original square walk with convex owner-value queries substituted.
The state, invariants, tuning constants and non-query primitives remain original. -/
open Matrix Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.MSConvexPreparedMovement
open MSManuscriptPreparedMovement MSManuscriptSupportedOwner MSManuscriptSupportedGamma MSManuscriptSupportedPreparation MSManuscriptMovementDrift MSManuscriptPreparedResponse MSManuscriptNumericalMovement
variable [MSConvexOwnerValue.Oracle]
variable {N d : ℕ}
local instance : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
set_option maxHeartbeats 1800000
set_option maxRecDepth 4000
attribute [local irreducible] ownerPotential

theorem output_drift_atStep (P : Parameters N d) (hP : P.Valid) (hN : 0<N)
    (initial : Owner N) (hInitial : State P initial) {y : Owner N×ℕ}
    (ho : MSConvexSupportedPreparation.output P initial=some y)
    (F : Finset (Fin N)) (x : EuclideanSpace ℝ (Fin N))
    (hq : 0<realTrace (covariance y.1.physical F x))
    {ε h : ℝ} (hε : 0<ε) (hh : 0<h) (hhstep : h≤stepSize P ε) :
    (∑s : Draws y.1.physical F x,weight y.1.physical F x s*(
      ownerPotential (P.center+h•ownerPhysicalIncrement P.atoms hP.1 (increment y.1.physical F x s))
        P.atoms (nextOwner y.1.physical F x h) P.regularizer-
      ownerPotential P.center P.atoms y.1.physical P.regularizer)) ≤
      h^2*(responseCap P+ε) := by
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp P.physicalDimension_pos
  have hc := MSConvexSupportedPreparation.output_sound P hP initial hInitial ho
  have ht := prepared P hP hN y.1 (hc.state P hP hInitial) hc.cap F x hq hh
    (hhstep.trans (stepSize_le P ε))
  have hs : h^2≤(stepSize P ε)^2 := (sq_le_sq₀ hh.le (stepSize_pos P hP hε).le).mpr hhstep
  have hR : 0≤P.centerCap := (norm_nonneg _).trans hP.2.2.2.2.2.2
  have hM := uniformBudget_pos (N := N) (d := d) (γ := P.floor) hR hP.2.2.1
  have hb : uniformBudget N d P.centerCap P.regularizer P.floor*h^2/24≤ε :=
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hs hM.le) (by norm_num)).trans
      (stepSize_budget P hP hε)
  have hm := mul_le_mul_of_nonneg_right hb (sq_nonneg h)
  refine ht.trans ?_
  nlinarith

end MatrixSpencer.MSConvexPreparedMovement
