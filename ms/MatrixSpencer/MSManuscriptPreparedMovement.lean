import MatrixSpencer.MSManuscriptMovementDrift
import MatrixSpencer.MSManuscriptPreparedResponse

/-!
# Fully numerical preparation supplies the actual movement drift

The response cap below is derived from the computed preparation output. The
step is an explicit scalar expression in the input-only uniform fourth budget.
No derivative, Taylor, response, numerical-accuracy or favorable-draw oracle
is assumed. Positive short trace is the geometric epoch precondition.
-/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.MSManuscriptPreparedMovement
open MSManuscriptSupportedOwner MSManuscriptSupportedGamma MSManuscriptSupportedPreparation
open MSManuscriptMovementDrift MSManuscriptPreparedResponse MSManuscriptNumericalMovement
variable {N d : ℕ}
local instance : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
set_option maxHeartbeats 1200000
attribute [local irreducible] ownerPotential

/-- Finite arithmetic step choice; the requested error is a second-order
per-movement drift allowance. -/
def stepSize (P : Parameters N d) (ε : ℝ) : ℝ :=
  min (MSManuscriptMatchedInterval.radius P.floor/2)
    (Real.sqrt (24*ε/uniformBudget N d P.centerCap P.regularizer P.floor))

theorem stepSize_pos (P : Parameters N d) (hP : P.Valid) {ε : ℝ} (hε : 0<ε) :
    0<stepSize P ε := by
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp P.physicalDimension_pos
  have hR : 0≤P.centerCap := (norm_nonneg _).trans hP.2.2.2.2.2.2
  exact lt_min (div_pos (MSManuscriptMatchedInterval.radius_pos hP.2.2.2.1) (by norm_num))
    (Real.sqrt_pos.mpr (div_pos (by positivity) (uniformBudget_pos hR hP.2.2.1)))

theorem stepSize_le (P : Parameters N d) (ε : ℝ) :
    stepSize P ε≤MSManuscriptMatchedInterval.radius P.floor/2 := min_le_left _ _

theorem stepSize_budget (P : Parameters N d) (hP : P.Valid) {ε : ℝ} (hε : 0<ε) :
    uniformBudget N d P.centerCap P.regularizer P.floor*(stepSize P ε)^2/24≤ε := by
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp P.physicalDimension_pos
  have hR : 0≤P.centerCap := (norm_nonneg _).trans hP.2.2.2.2.2.2
  have hM := uniformBudget_pos (N := N) (d := d) (γ := P.floor) hR hP.2.2.1
  have hs := (sq_le_sq₀ (stepSize_pos P hP hε).le (Real.sqrt_nonneg _)).mpr
    (min_le_right (MSManuscriptMatchedInterval.radius P.floor/2)
      (Real.sqrt (24*ε/uniformBudget N d P.centerCap P.regularizer P.floor)))
  rw [Real.sq_sqrt (div_nonneg (by positivity) hM.le)] at hs
  have hm := (le_div_iff₀ hM).mp hs
  nlinarith

/-- Prepared-cap form, useful when a prepared owner is stored in the epoch
state with the certificate from the previous transition. -/
theorem prepared (P : Parameters N d) (hP : P.Valid) (hN : 0<N)
    (O : Owner N) (hO : State P O) (hcap : Cap P O)
    (F : Finset (Fin N)) (x : EuclideanSpace ℝ (Fin N))
    (hq : 0<realTrace (covariance O.physical F x))
    {h : ℝ} (hh : 0<h) (hstep : h≤MSManuscriptMatchedInterval.radius P.floor/2) :
    (∑s : Draws O.physical F x,weight O.physical F x s*(
      ownerPotential (P.center+h•ownerPhysicalIncrement P.atoms hP.1 (increment O.physical F x s))
        P.atoms (nextOwner O.physical F x h) P.regularizer-
      ownerPotential P.center P.atoms O.physical P.regularizer)) ≤
      h^2*responseCap P+uniformBudget N d P.centerCap P.regularizer P.floor*h^4/24 := by
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp P.physicalDimension_pos
  exact actual_movement P.center P.atoms hP.1 hP.2.1 O hO.1 hO.2.1 hO.2.2 F x hq
    hP.2.2.1 ((norm_nonneg _).trans hP.2.2.2.2.2.2) hP.2.2.2.2.2.2
    hP.2.2.2.1 hP.2.2.2.2.1 hh hstep (prepared_response_le P hP hN O hO hcap)

/-- The actual preparation output and actual numerical movement, with every
analytic and response bound discharged from primitive input assumptions. -/
theorem output_drift (P : Parameters N d) (hP : P.Valid) (hN : 0<N)
    (initial : Owner N) (hInitial : State P initial) {y : Owner N×ℕ}
    (ho : output P initial=some y)
    (F : Finset (Fin N)) (x : EuclideanSpace ℝ (Fin N))
    (hq : 0<realTrace (covariance y.1.physical F x))
    {ε : ℝ} (hε : 0<ε) :
    (∑s : Draws y.1.physical F x,weight y.1.physical F x s*(
      ownerPotential (P.center+stepSize P ε•ownerPhysicalIncrement P.atoms hP.1 (increment y.1.physical F x s))
        P.atoms (nextOwner y.1.physical F x (stepSize P ε)) P.regularizer-
      ownerPotential P.center P.atoms y.1.physical P.regularizer)) ≤
      (stepSize P ε)^2*(responseCap P+ε) := by
  have hc := output_sound P hP initial hInitial ho
  have hh := prepared P hP hN y.1 (hc.state P hP hInitial) hc.cap F x hq
    (stepSize_pos P hP hε) (stepSize_le P ε)
  have hb := mul_le_mul_of_nonneg_right (stepSize_budget P hP hε) (sq_nonneg (stepSize P ε))
  refine hh.trans ?_
  nlinarith


theorem stepSize_le_quarter (P : Parameters N d) (ε : ℝ) : stepSize P ε≤1/4 :=
  (stepSize_le P ε).trans (by
    have hr : MSManuscriptMatchedInterval.radius P.floor≤1/2 := min_le_left _ _
    linarith)

theorem stepSize_sq_le_half (P : Parameters N d) (hP : P.Valid) {ε : ℝ} (hε : 0<ε) :
    (stepSize P ε)^2≤1/2 := by
  have hp := stepSize_pos P hP hε
  have hq := stepSize_le_quarter P ε
  nlinarith

/-- Cube legality may require a smaller step. Every positive step below the
explicit analytic choice retains the same second-order drift guarantee. -/
theorem output_drift_atStep (P : Parameters N d) (hP : P.Valid) (hN : 0<N)
    (initial : Owner N) (hInitial : State P initial) {y : Owner N×ℕ}
    (ho : output P initial=some y)
    (F : Finset (Fin N)) (x : EuclideanSpace ℝ (Fin N))
    (hq : 0<realTrace (covariance y.1.physical F x))
    {ε h : ℝ} (hε : 0<ε) (hh : 0<h) (hhstep : h≤stepSize P ε) :
    (∑s : Draws y.1.physical F x,weight y.1.physical F x s*(
      ownerPotential (P.center+h•ownerPhysicalIncrement P.atoms hP.1 (increment y.1.physical F x s))
        P.atoms (nextOwner y.1.physical F x h) P.regularizer-
      ownerPotential P.center P.atoms y.1.physical P.regularizer)) ≤
      h^2*(responseCap P+ε) := by
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp P.physicalDimension_pos
  have hc := output_sound P hP initial hInitial ho
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

end MatrixSpencer.MSManuscriptPreparedMovement
