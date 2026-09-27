import MatrixSpencer.KSNumericalFidelity
import MatrixSpencer.OwnerPotential

/-!
# Certified finite evaluation of the original owner objective

At a supplied PSD density, this report uses finite arithmetic for the center
and covariance source, and the proved real-Jacobi reports for fidelity and
trace square root. It includes singular covariance sources. Maximizing the
objective over the density set is a separate remaining obligation.
-/

open Matrix
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section
namespace MatrixSpencer.KSNumericalOwnerObjective

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}

def rootTolerance (θ ν : ℝ) : ℝ := ν / (4 * (|θ| + 1))

/-- Finite numerical evaluation at the supplied density. No optimized
potential value or matrix-valued square root is called by the definition. -/
def report (H : Matrix (Fin d) (Fin d) ℂ) (A : ι → Matrix (Fin d) (Fin d) ℂ)
    (C : Matrix ι ι ℝ) (θ : ℝ) (S : Matrix (Fin d) (Fin d) ℂ) (ν : ℝ) : ℝ :=
  realTrace (H * S) +
    2 * KSNumericalFidelity.ComplexReport.report S (covarianceSource A C S) (ν / 4) +
    2 * θ * KSComplexTraceSqrt.report S (rootTolerance θ ν)

theorem report_accuracy (H : Matrix (Fin d) (Fin d) ℂ)
    (A : ι → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (θ : ℝ)
    {S : Matrix (Fin d) (Fin d) ℂ} (hS : S.PosSemidef) {ν : ℝ} (hν : 0 < ν) :
    |report H A C θ S ν - ownerObjective H A C θ S| ≤ ν := by
  have hf := KSNumericalFidelity.ComplexReport.report_accuracy S (covarianceSource A C S)
    hS (covarianceSource_posSemidef A hA hC hS) (ν := ν / 4) (by positivity)
  have ht := KSComplexTraceSqrt.report_accuracy S hS
    (ν := rootTolerance θ ν) (by unfold rootTolerance; positivity)
  have hθ := abs_nonneg θ
  have hρ : 0 ≤ rootTolerance θ ν := by unfold rootTolerance; positivity
  have hden : 0 < 4 * (|θ| + 1) := by positivity
  have hr : 2 * |θ| * rootTolerance θ ν ≤ ν / 2 := by
    unfold rootTolerance
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hden).mpr
    nlinarith
  have he : report H A C θ S ν - ownerObjective H A C θ S =
      2 * (KSNumericalFidelity.ComplexReport.report S (covarianceSource A C S) (ν / 4) -
        fidelity S (covarianceSource A C S)) +
      (2 * θ) * (KSComplexTraceSqrt.report S (rootTolerance θ ν) - realTrace (CFC.sqrt S)) := by
    unfold report ownerObjective
    ring
  rw [he]
  apply (abs_add_le _ _).trans
  rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hf' := mul_le_mul_of_nonneg_left hf (by norm_num : (0 : ℝ) ≤ 2)
  have ht' := mul_le_mul_of_nonneg_left ht (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hθ)
  linarith

/-- The same finite evaluation is valid for every feasible trace-one
density in the genuine potential maximization. -/
theorem report_accuracy_on_density (H : Matrix (Fin d) (Fin d) ℂ)
    (A : ι → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (θ : ℝ)
    {S : Matrix (Fin d) (Fin d) ℂ} (hS : S ∈ densitySet) {ν : ℝ} (hν : 0 < ν) :
    |report H A C θ S ν - ownerObjective H A C θ S| ≤ ν :=
  report_accuracy H A hA hC θ hS.1 hν

end MatrixSpencer.KSNumericalOwnerObjective
