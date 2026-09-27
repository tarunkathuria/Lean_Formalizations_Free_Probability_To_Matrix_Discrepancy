import MatrixSpencer.KSJacobiMatrixSqrt
import MatrixSpencer.KSComplexTraceSqrt

/-!
# Numerical fidelity from the proved finite Jacobi routines

The report forms a certified approximate matrix root, sandwiches the second
PSD input with that computed root, then uses the certified trace-root report.
Its parameter bounds are finite sums, scalar arithmetic, and square roots.
Neither input needs a lower eigenvalue bound. This is evaluation at supplied
matrices, not maximization over the density domain.
-/

open Matrix
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section
namespace MatrixSpencer.KSNumericalFidelity

variable {d : ℕ}

def matrixBound (A : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  1 + Real.sqrt (KSJacobiStep.frobeniusEnergy A)

theorem matrixBound_pos (A : Matrix (Fin d) (Fin d) ℝ) : 0 < matrixBound A := by
  unfold matrixBound
  positivity

theorem norm_le_matrixBound (A : Matrix (Fin d) (Fin d) ℝ) : ‖A‖ ≤ matrixBound A :=
  (KSJacobiRayleigh.operatorNorm_le_frobenius A).trans (by unfold matrixBound; linarith)

theorem sqrt_norm_le_matrixBound (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.PosSemidef) :
    ‖CFC.sqrt A‖ ≤ matrixBound A := by
  have hs := CStarRing.norm_star_mul_self (x := CFC.sqrt A)
  rw [Matrix.star_eq_conjTranspose, (CFC.sqrt_nonneg A).posSemidef.isHermitian.eq,
    CFC.sqrt_mul_sqrt_self A hA.nonneg] at hs
  have hb := KSJacobiRayleigh.operatorNorm_le_frobenius A
  change ‖A‖ ≤ Real.sqrt (KSJacobiStep.frobeniusEnergy A) at hb
  unfold matrixBound
  nlinarith [norm_nonneg (CFC.sqrt A), Real.sqrt_nonneg (KSJacobiStep.frobeniusEnergy A)]

def errorCoefficient (A B : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  matrixBound B * (2 * matrixBound A + 1)

def gramTolerance (d : ℕ) (ν : ℝ) : ℝ := (ν / (2 * ((d : ℝ) + 1))) ^ 2

def rootTolerance (A B : Matrix (Fin d) (Fin d) ℝ) (ν : ℝ) : ℝ :=
  min 1 (gramTolerance d ν / (errorCoefficient A B + 1))

theorem errorCoefficient_pos (A B : Matrix (Fin d) (Fin d) ℝ) : 0 < errorCoefficient A B := by
  unfold errorCoefficient
  have ha := matrixBound_pos A
  have hb := matrixBound_pos B
  positivity

theorem rootTolerance_pos (A B : Matrix (Fin d) (Fin d) ℝ) {ν : ℝ} (hν : 0 < ν) :
    0 < rootTolerance A B ν := by
  unfold rootTolerance gramTolerance
  have he := errorCoefficient_pos A B
  positivity

def rootReport (A B : Matrix (Fin d) (Fin d) ℝ) (ν : ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  KSJacobiMatrixSqrt.report A (rootTolerance A B ν)

def gramReport (A B : Matrix (Fin d) (Fin d) ℝ) (ν : ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  rootReport A B ν * B * rootReport A B ν

def realFidelity (A B : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  KSJacobiTraceSqrt.traceSqrt (CFC.sqrt A * B * CFC.sqrt A)

def report (A B : Matrix (Fin d) (Fin d) ℝ) (ν : ℝ) : ℝ :=
  KSJacobiTraceSqrt.report (gramReport A B ν) (ν / 2)

theorem gramReport_posSemidef (A B : Matrix (Fin d) (Fin d) ℝ) (hB : B.PosSemidef)
    (ν : ℝ) : (gramReport A B ν).PosSemidef := by
  have hR := KSJacobiMatrixSqrt.report_posSemidef A (rootTolerance A B ν)
  simpa only [gramReport, rootReport, hR.isHermitian.eq] using
    hB.mul_mul_conjTranspose_same (rootReport A B ν)

theorem trueGram_posSemidef (A B : Matrix (Fin d) (Fin d) ℝ) (hB : B.PosSemidef) :
    (CFC.sqrt A * B * CFC.sqrt A).PosSemidef := by
  simpa only [(CFC.sqrt_nonneg A).posSemidef.isHermitian.eq] using
    hB.mul_mul_conjTranspose_same (CFC.sqrt A)

/-- Error in the computed sandwich is explicitly paid for by its chosen
matrix-root tolerance. All matrix norms are Euclidean operator norms. -/
theorem gramReport_error (A B : Matrix (Fin d) (Fin d) ℝ) (hA : A.PosSemidef)
    {ν : ℝ} (hν : 0 < ν) :
    ‖gramReport A B ν - CFC.sqrt A * B * CFC.sqrt A‖ ≤ gramTolerance d ν := by
  let ρ := rootTolerance A B ν
  let R := rootReport A B ν
  let Q := CFC.sqrt A
  have hρ := rootTolerance_pos A B hν
  have hρone : ρ ≤ 1 := min_le_left _ _
  have herror : ‖R - Q‖ ≤ ρ := KSJacobiMatrixSqrt.report_accuracy A hA hρ
  have hQ : ‖Q‖ ≤ matrixBound A := sqrt_norm_le_matrixBound A hA
  have hBnorm : ‖B‖ ≤ matrixBound B := norm_le_matrixBound B
  have hR : ‖R‖ ≤ matrixBound A + 1 := by
    have h := norm_add_le (R - Q) Q
    rw [sub_add_cancel] at h
    linarith
  have heq : R * B * R - Q * B * Q = (R - Q) * B * R + Q * B * (R - Q) := by
    noncomm_ring
  have hprod₁ : ‖(R - Q) * B * R‖ ≤ ρ * matrixBound B * (matrixBound A + 1) := by
    exact (norm_mul_le _ _).trans (mul_le_mul
      ((norm_mul_le _ _).trans (mul_le_mul herror hBnorm (norm_nonneg _) hρ.le)) hR
      (norm_nonneg _) (mul_nonneg hρ.le (matrixBound_pos B).le))
  have hprod₂ : ‖Q * B * (R - Q)‖ ≤ matrixBound A * matrixBound B * ρ := by
    exact (norm_mul_le _ _).trans (mul_le_mul
      ((norm_mul_le _ _).trans (mul_le_mul hQ hBnorm (norm_nonneg _) (matrixBound_pos A).le)) herror
      (norm_nonneg _) (mul_nonneg (matrixBound_pos A).le (matrixBound_pos B).le))
  have hcost : ‖gramReport A B ν - Q * B * Q‖ ≤ ρ * errorCoefficient A B := by
    change ‖R * B * R - Q * B * Q‖ ≤ _
    rw [heq]
    have h := (norm_add_le _ _).trans (add_le_add hprod₁ hprod₂)
    unfold errorCoefficient
    nlinarith
  have hcap : ρ ≤ gramTolerance d ν / (errorCoefficient A B + 1) := min_le_right _ _
  have hp : 0 < errorCoefficient A B + 1 := by have := errorCoefficient_pos A B; linarith
  have hc := (le_div_iff₀ hp).mp hcap
  exact hcost.trans (by nlinarith)

/-- A complete accuracy theorem for the composed real-matrix fidelity
report, including singular inputs. -/
theorem report_accuracy (A B : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) {ν : ℝ} (hν : 0 < ν) :
    |report A B ν - realFidelity A B| ≤ ν := by
  have hG := gramReport_posSemidef A B hB ν
  have htrue := trueGram_posSemidef A B hB
  have happrox := KSJacobiTraceSqrt.report_accuracy (gramReport A B ν) hG
    (ν := ν / 2) (by positivity)
  have hpert := KSJacobiTraceSqrt.traceSqrt_perturbation hG htrue (gramReport_error A B hA hν)
  rw [Fintype.card_fin] at hpert
  have hs : Real.sqrt (gramTolerance d ν) = ν / (2 * ((d : ℝ) + 1)) :=
    Real.sqrt_sq (by positivity)
  rw [hs] at hpert
  have hd : (d : ℝ) * (ν / (2 * ((d : ℝ) + 1))) ≤ ν / 2 := by
    have hden : 0 < 2 * ((d : ℝ) + 1) := by positivity
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hden).mpr
    nlinarith
  exact (abs_sub_le _ (KSJacobiTraceSqrt.traceSqrt (gramReport A B ν)) _).trans
    ((add_le_add happrox (hpert.trans hd)).trans (by linarith))

namespace ComplexReport
open KSComplexTraceSqrt

theorem realificationFin_mul (A B : Matrix (Fin d) (Fin d) ℂ) :
    realificationFin (A * B) = realificationFin A * realificationFin B := by
  unfold realificationFin
  rw [realification_mul, Matrix.submatrix_mul_equiv]

theorem realificationFin_sqrt (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.PosSemidef) :
    CFC.sqrt (realificationFin A) = realificationFin (CFC.sqrt A) := by
  unfold realificationFin
  rw [sqrt_submatrix_equiv _ (realification_posSemidef A hA), realification_sqrt A hA]

theorem realificationFin_fidelity (A B : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    realFidelity (realificationFin A) (realificationFin B) = 2 * fidelity A B := by
  have hG : (CFC.sqrt A * B * CFC.sqrt A).PosSemidef := by
    simpa only [(CFC.sqrt_nonneg A).posSemidef.isHermitian.eq] using
      hB.mul_mul_conjTranspose_same (CFC.sqrt A)
  unfold realFidelity
  rw [realificationFin_sqrt A hA, ← realificationFin_mul, ← realificationFin_mul,
    realificationFin_traceSqrt _ hG]
  rfl

/-- Every operation of the complex fidelity report is real arithmetic on
the explicit doubled block matrices and the proved finite Jacobi routines. -/
def report (A B : Matrix (Fin d) (Fin d) ℂ) (ν : ℝ) : ℝ :=
  KSNumericalFidelity.report (realificationFin A) (realificationFin B) (2 * ν) / 2

theorem report_accuracy (A B : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) {ν : ℝ} (hν : 0 < ν) :
    |report A B ν - fidelity A B| ≤ ν := by
  have hr := KSNumericalFidelity.report_accuracy (realificationFin A) (realificationFin B)
    (realificationFin_posSemidef A hA) (realificationFin_posSemidef B hB)
    (ν := 2 * ν) (by positivity)
  rw [realificationFin_fidelity A B hA hB] at hr
  rcases abs_le.mp hr with ⟨hl, hu⟩
  unfold report
  apply abs_le.mpr
  constructor <;> linarith

end ComplexReport

end MatrixSpencer.KSNumericalFidelity
