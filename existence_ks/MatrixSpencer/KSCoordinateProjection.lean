import MatrixSpencer.KSHermitianGradientReport
import MatrixSpencer.KSComplexMatrixProjection

/-!
# The physical numerical matrix projection in full Hermitian coordinates

The numerical operation is the previously verified complex matrix report. The
chart and its inverse below only express this physical operation in the Hilbert
coordinates used by the objective iteration. The exact physical projection is
proved equal to the Hilbert metric projection onto the entire density floor.
-/

open Matrix
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section
namespace MatrixSpencer.KSCoordinateProjection

open KSFullHermitianChart KSObjectiveChart KSComplexProjectionGeometry
open KSHermitianGradientReport KSInexactIteration

variable {n : Type*} [Fintype n] [DecidableEq n]
local instance : CStarAlgebra (Matrix n n ℂ) := {}
local instance : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance

omit [DecidableEq n] in
/-- The entry-coordinate real inner product is the usual adjoint trace pairing. -/
theorem complexInner_eq_trace (A B : Matrix n n ℂ) :
    complexInner A B = realTrace (Aᴴ * B) := by
  simp [complexInner, realTrace, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.conjTranspose_apply]
  exact Finset.sum_comm

/-- The full Hermitian chart preserves the actual physical Frobenius pairing. -/
theorem chart_inner (x y : Coordinates n) :
    complexInner (chart n x : Matrix n n ℂ) (chart n y : Matrix n n ℂ) = inner ℝ x y := by
  have hH : (chart n x : Matrix n n ℂ).IsHermitian := (chart n x).property
  rw [complexInner_eq_trace, hH.eq, chart_trace_pairing]

variable {d : ℕ}

/-- Physical Hermitian matrix represented by the analysis coordinates. -/
def physical (x : Coordinates (Fin d)) : Matrix (Fin d) (Fin d) ℂ := chart (Fin d) x

theorem physical_hermitian (x : Coordinates (Fin d)) : (physical x).IsHermitian :=
  (chart (Fin d) x).property

/-- A self-adjoint packaging of the physical numerical report. -/
def physicalReport (a : ℝ) (hd : 0 < d) (has : (d : ℝ) * a ≤ 1) (ν : ℝ)
    (x : Coordinates (Fin d)) : selfAdjoint (Matrix (Fin d) (Fin d) ℂ) :=
  ⟨KSComplexMatrixProjection.report (physical x) a 1 hd ν,
    (KSComplexMatrixProjection.report_feasible (physical x) a 1 hd has ν).1⟩

/-- Coordinate view of the actual physical projection operation. -/
def report (a : ℝ) (hd : 0 < d) (has : (d : ℝ) * a ≤ 1) (ν : ℝ)
    (x : Coordinates (Fin d)) : Coordinates (Fin d) :=
  (chartEquiv (Fin d)).symm (physicalReport a hd has ν x)

/-- Iteration-indexed report in the interface of the objective controller. -/
def projectionReport (a : ℝ) (hd : 0 < d) (has : (d : ℝ) * a ≤ 1) (ν : ℝ) :
    ℕ → Coordinates (Fin d) → Coordinates (Fin d) := fun _ x => report a hd has ν x

/-- Self-adjoint packaging of the exact physical projection, for the specification only. -/
def exactPhysicalProjection (a : ℝ) (hd : 0 < d) (has : (d : ℝ) * a ≤ 1)
    (x : Coordinates (Fin d)) : selfAdjoint (Matrix (Fin d) (Fin d) ℂ) :=
  ⟨KSComplexMatrixProjection.exactProjection (physical x) (physical_hermitian x) a 1 hd has,
    (KSComplexMatrixProjection.exactProjection_isProjection (physical x)
      (physical_hermitian x) a 1 hd has).1.1⟩

def exactCoordinateProjection (a : ℝ) (hd : 0 < d) (has : (d : ℝ) * a ≤ 1)
    (x : Coordinates (Fin d)) : Coordinates (Fin d) :=
  (chartEquiv (Fin d)).symm (exactPhysicalProjection a hd has x)

theorem chart_report (a : ℝ) (hd : 0 < d) (has : (d : ℝ) * a ≤ 1) (ν : ℝ)
    (x : Coordinates (Fin d)) : chart (Fin d) (report a hd has ν x) = physicalReport a hd has ν x :=
  (chartEquiv (Fin d)).apply_symm_apply _

theorem chart_exactProjection (a : ℝ) (hd : 0 < d) (has : (d : ℝ) * a ≤ 1)
    (x : Coordinates (Fin d)) :
    chart (Fin d) (exactCoordinateProjection a hd has x) = exactPhysicalProjection a hd has x :=
  (chartEquiv (Fin d)).apply_symm_apply _

theorem report_mem (a : ℝ) (hd : 0 < d) (has : (d : ℝ) * a ≤ 1) (ν : ℝ)
    (x : Coordinates (Fin d)) : report a hd has ν x ∈ densityFloor (chart (Fin d)) a := by
  have h := KSComplexMatrixProjection.report_feasible (physical x) a 1 hd has ν
  change a • (1 : Matrix (Fin d) (Fin d) ℂ) ≤ (chart (Fin d) (report a hd has ν x) : Matrix _ _ _) ∧ _
  rw [chart_report]
  exact h.2

theorem exactCoordinateProjection_mem (a : ℝ) (hd : 0 < d) (has : (d : ℝ) * a ≤ 1)
    (x : Coordinates (Fin d)) : exactCoordinateProjection a hd has x ∈ densityFloor (chart (Fin d)) a := by
  have h := KSComplexMatrixProjection.exactProjection_isProjection (physical x)
    (physical_hermitian x) a 1 hd has
  change a • (1 : Matrix (Fin d) (Fin d) ℂ) ≤
    (chart (Fin d) (exactCoordinateProjection a hd has x) : Matrix _ _ _) ∧ _
  rw [chart_exactProjection]
  exact h.1.2

/-- Nonemptiness is discharged by the explicitly constructed feasible report. -/
theorem densityFloor_nonempty (a : ℝ) (hd : 0 < d) (has : (d : ℝ) * a ≤ 1) :
    (densityFloor (chart (Fin d)) a).Nonempty :=
  ⟨report a hd has 1 0, report_mem a hd has 1 0⟩

theorem exactCoordinateProjection_variational (a : ℝ) (hd : 0 < d) (has : (d : ℝ) * a ≤ 1)
    (x : Coordinates (Fin d)) (y : Coordinates (Fin d)) (hy : y ∈ densityFloor (chart (Fin d)) a) :
    inner ℝ (x - exactCoordinateProjection a hd has x) (y - exactCoordinateProjection a hd has x) ≤ 0 := by
  have h := (KSComplexMatrixProjection.exactProjection_isProjection (physical x)
    (physical_hermitian x) a 1 hd has).2 (physical y)
      ⟨physical_hermitian y, hy⟩
  rw [← chart_inner]
  simp only [map_sub]
  rw [chart_exactProjection]
  exact h

/-- The exact matrix projection is exactly the Hilbert metric projection used by
`KSObjectiveChart`, for every choice of the nonemptiness witness. -/
theorem metricProjection_eq (a : ℝ) (hd : 0 < d) (has : (d : ℝ) * a ≤ 1)
    (hne : (densityFloor (chart (Fin d)) a).Nonempty) (x : Coordinates (Fin d)) :
    metricProjection (densityFloor (chart (Fin d)) a) hne
      (densityFloor_isClosed (chart (Fin d)) a).isComplete (densityFloor_convex (chart (Fin d)) a) x =
      exactCoordinateProjection a hd has x := by
  exact KSProjectedContraction.metricProjection_eq_of_variational _ hne _ _ x _
    (exactCoordinateProjection_mem a hd has x) (exactCoordinateProjection_variational a hd has x)

/-- Coordinate error is precisely the physical complex Frobenius error. -/
theorem report_exact_distance (a : ℝ) (hd : 0 < d) (has : (d : ℝ) * a ≤ 1) {ν : ℝ}
    (hν : 0 < ν) (x : Coordinates (Fin d)) :
    dist (report a hd has ν x) (exactCoordinateProjection a hd has x) ≤ ν := by
  rw [dist_eq_norm]
  change ‖(chartEquiv (Fin d)).symm (physicalReport a hd has ν x) -
    (chartEquiv (Fin d)).symm (exactPhysicalProjection a hd has x)‖ ≤ ν
  rw [← map_sub, chart_inverse_norm]
  exact KSComplexMatrixProjection.report_accuracy (physical x) (physical_hermitian x) a 1 hd has hν

/-- The actual coordinate report meets the objective iteration's projection-error interface. -/
theorem report_accuracy (a : ℝ) (hd : 0 < d) (has : (d : ℝ) * a ≤ 1) {ν : ℝ}
    (hν : 0 < ν) (hne : (densityFloor (chart (Fin d)) a).Nonempty) (x : Coordinates (Fin d)) :
    dist (report a hd has ν x)
      (metricProjection (densityFloor (chart (Fin d)) a) hne
        (densityFloor_isClosed (chart (Fin d)) a).isComplete (densityFloor_convex (chart (Fin d)) a) x) ≤ ν := by
  rw [metricProjection_eq a hd has hne]
  exact report_exact_distance a hd has hν x

/-- Both numerical projection obligations, with no remaining projection oracle hypothesis. -/
theorem projectionReport_spec (a : ℝ) (hd : 0 < d) (has : (d : ℝ) * a ≤ 1) {ν : ℝ}
    (hν : 0 < ν) (hne : (densityFloor (chart (Fin d)) a).Nonempty) :
    (∀ k x, projectionReport a hd has ν k x ∈ densityFloor (chart (Fin d)) a) ∧
    (∀ k x, dist (projectionReport a hd has ν k x)
      (metricProjection (densityFloor (chart (Fin d)) a) hne
        (densityFloor_isClosed (chart (Fin d)) a).isComplete (densityFloor_convex (chart (Fin d)) a) x) ≤ ν) :=
  ⟨fun _ x => report_mem a hd has ν x, fun _ x => report_accuracy a hd has hν hne x⟩

end MatrixSpencer.KSCoordinateProjection
