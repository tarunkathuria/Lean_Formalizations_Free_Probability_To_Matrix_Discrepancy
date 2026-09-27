import MatrixSpencer.KSComplexProjectionGeometry

/-!
# Certified complex Hermitian density-floor projection report

The report realifies the input, runs the explicit real Jacobi/simplex projection,
and extracts the complex-linear average by fixed block-entry arithmetic. The
exact projection is only a specification. Its correspondence with the full
complex Hermitian domain follows from uniqueness and invariance under the fixed
complex structure, not from restricting the complex feasible set in advance.
-/

open Matrix
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section
namespace MatrixSpencer.KSComplexMatrixProjection

open KSComplexTraceSqrt KSComplexProjectionGeometry
variable {d : ℕ}

theorem doubled_dimension_pos (hd : 0 < d) : 0 < d + d := by omega

theorem doubled_floor {a s : ℝ} (has : (d : ℝ) * a ≤ s) : ((d+d : ℕ) : ℝ) * a ≤ 2 * s := by
  push_cast
  nlinarith

/-- Actual real-arithmetic report before complex-structure averaging. -/
def realReport (A : Matrix (Fin d) (Fin d) ℂ) (a s : ℝ) (hd : 0 < d) (ν : ℝ) :
    Matrix (Fin (d+d)) (Fin (d+d)) ℝ :=
  KSJacobiMatrixProjection.report (realificationFin A) a (2 * s) (doubled_dimension_pos hd) ν

/-- Actual complex report, using only the explicitly computed real blocks. -/
def report (A : Matrix (Fin d) (Fin d) ℂ) (a s : ℝ) (hd : 0 < d) (ν : ℝ) :
    Matrix (Fin d) (Fin d) ℂ := extractFin (realReport A a s hd ν)

/-- The full real exact projection, used in the mathematical specification only. -/
def exactRealProjection (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian)
    (a s : ℝ) (hd : 0 < d) (has : (d : ℝ) * a ≤ s) :
    Matrix (Fin (d+d)) (Fin (d+d)) ℝ :=
  KSJacobiMatrixProjection.exactProjection (realificationFin A) (realificationFin_symmetric A hA)
    a (2 * s) (doubled_dimension_pos hd) (doubled_floor has)

def exactProjection (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian)
    (a s : ℝ) (hd : 0 < d) (has : (d : ℝ) * a ≤ s) : Matrix (Fin d) (Fin d) ℂ :=
  extractFin (exactRealProjection A hA a s hd has)

/-- Variational characterization in the full complex Frobenius geometry. -/
def IsProjection (a s : ℝ) (A P : Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ComplexFeasible a s P ∧
    ∀ Y, ComplexFeasible a s Y → complexInner (A - P) (Y - P) ≤ 0

theorem exactRealProjection_isProjection (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian)
    (a s : ℝ) (hd : 0 < d) (has : (d : ℝ) * a ≤ s) :
    KSJacobiMatrixProjection.IsProjection a (2 * s) (realificationFin A)
      (exactRealProjection A hA a s hd has) :=
  KSJacobiMatrixProjection.exactProjection_isProjection (realificationFin A)
    (realificationFin_symmetric A hA) a (2 * s) (doubled_dimension_pos hd) (doubled_floor has)

/-- Uniqueness of the real projection forces invariance under the complex structure. -/
theorem exactRealProjection_fixed (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian)
    (a s : ℝ) (hd : 0 < d) (has : (d : ℝ) * a ≤ s) :
    KSJacobiMatrixProjection.conjugate complexStructureFin (exactRealProjection A hA a s hd has) =
      exactRealProjection A hA a s hd has := by
  have hp := exactRealProjection_isProjection A hA a s hd has
  have hU := complexStructureFin_orthogonal (d := d)
  have hU' := Matrix.mul_eq_one_comm.mp hU
  have h := KSJacobiMatrixProjection.projection_conjugate complexStructureFin
    (realificationFin A) (exactRealProjection A hA a s hd has) hU hU' hp
  rw [complexStructureFin_fixes_realification] at h
  exact KSJacobiMatrixProjection.projection_unique h hp

theorem realification_exactProjection (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian)
    (a s : ℝ) (hd : 0 < d) (has : (d : ℝ) * a ≤ s) :
    realificationFin (exactProjection A hA a s hd has) = exactRealProjection A hA a s hd has :=
  realificationFin_extractFin_of_fixed _ (exactRealProjection_fixed A hA a s hd has)

/-- Every complex feasible competitor is included in the variational comparison. -/
theorem isProjection_of_real {a s : ℝ} (A P : Matrix (Fin d) (Fin d) ℂ)
    (hp : KSJacobiMatrixProjection.IsProjection a (2 * s) (realificationFin A) (realificationFin P)) :
    IsProjection a s A P := by
  refine ⟨?_, ?_⟩
  · simpa only [extractFin_realificationFin] using extractFin_feasible _ hp.1
  · intro Y hY
    have h := hp.2 (realificationFin Y) (realificationFin_feasible Y hY)
    rw [← realificationFin_sub, ← realificationFin_sub, realificationFin_inner] at h
    linarith

theorem exactProjection_isProjection (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian)
    (a s : ℝ) (hd : 0 < d) (has : (d : ℝ) * a ≤ s) :
    IsProjection a s A (exactProjection A hA a s hd has) := by
  apply isProjection_of_real
  rw [realification_exactProjection]
  exact exactRealProjection_isProjection A hA a s hd has

/-- The exact specification minimizes the ordinary complex Frobenius distance over
all Hermitian matrices above the floor with the given trace. -/
theorem exactProjection_minimizes (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian)
    (a s : ℝ) (hd : 0 < d) (has : (d : ℝ) * a ≤ s)
    (Y : Matrix (Fin d) (Fin d) ℂ) (hY : ComplexFeasible a s Y) :
    complexEnergy (A - exactProjection A hA a s hd has) ≤ complexEnergy (A - Y) := by
  have h := KSJacobiMatrixProjection.projection_distance_le
    (exactRealProjection_isProjection A hA a s hd has) (realificationFin Y)
    (realificationFin_feasible Y hY)
  rw [← realification_exactProjection A hA a s hd has,
    ← realificationFin_sub, ← realificationFin_sub, realificationFin_energy, realificationFin_energy] at h
  linarith

/-- Feasibility holds for the actual report, independently of the input's sign or spectrum. -/
theorem report_feasible (A : Matrix (Fin d) (Fin d) ℂ) (a s : ℝ)
    (hd : 0 < d) (has : (d : ℝ) * a ≤ s) (ν : ℝ) : ComplexFeasible a s (report A a s hd ν) :=
  extractFin_feasible _ (KSJacobiMatrixProjection.report_feasible (realificationFin A)
    a (2 * s) (doubled_dimension_pos hd) (doubled_floor has) ν)

theorem report_posSemidef (A : Matrix (Fin d) (Fin d) ℂ) (a s : ℝ)
    (hd : 0 < d) (has : (d : ℝ) * a ≤ s) (ν : ℝ) (ha : 0 ≤ a) :
    (report A a s hd ν).PosSemidef := by
  have h := (Matrix.PosSemidef.one.smul ha).add
    (Matrix.le_iff.mp (report_feasible A a s hd has ν).2.1)
  simpa only [add_sub_cancel] using h

/-- Complete requested Frobenius error, obtained by a real run at the same tolerance.
No lower eigenvalue or eigenvalue-gap hypothesis is required. -/
theorem report_accuracy (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian)
    (a s : ℝ) (hd : 0 < d) (has : (d : ℝ) * a ≤ s) {ν : ℝ} (hν : 0 < ν) :
    Real.sqrt (complexEnergy (report A a s hd ν - exactProjection A hA a s hd has)) ≤ ν := by
  have hreal := KSJacobiMatrixProjection.report_accuracy (realificationFin A)
    (realificationFin_symmetric A hA) a (2 * s) (doubled_dimension_pos hd) (doubled_floor has) hν
  have he : KSJacobiStep.frobeniusEnergy
      (realReport A a s hd ν - exactRealProjection A hA a s hd has) ≤ ν ^ 2 :=
    (Real.sqrt_le_iff.mp hreal).2
  have hc := extractFin_energy_le (realReport A a s hd ν - exactRealProjection A hA a s hd has)
  rw [extractFin_sub] at hc
  change complexEnergy (report A a s hd ν - exactProjection A hA a s hd has) ≤ _ at hc
  apply Real.sqrt_le_iff.mpr
  refine ⟨hν.le, ?_⟩
  nlinarith [sq_nonneg ν]

end MatrixSpencer.KSComplexMatrixProjection
