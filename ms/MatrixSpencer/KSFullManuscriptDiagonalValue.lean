import MatrixSpencer.KSFullManuscriptValueOracle
import MatrixSpencer.KSOwnerReindex

/-!
# Ellipsoid evaluation for diagonal owner sources

The numerical Kraus family below is formed by scalar square roots of the
nonnegative diagonal weights. There is no matrix square-root, optimized
potential, or optimizer call in this report's definition. Its correctness
covers the full density domain and also zero weights and singular sources.
-/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSFullManuscriptDiagonalValue

variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]

/-- Explicit scalar-root weighting of each original Hermitian Kraus label. -/
def weighted (A : ι → Matrix n n ℂ) (c : ι → ℝ) (i : ι) : Matrix n n ℂ :=
  Real.sqrt (c i) • A i

theorem source_eq (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i) (S : Matrix n n ℂ) :
    covarianceSource A (Matrix.diagonal c) S = krausChannel (weighted A c) S := by
  simp only [covarianceSource, Matrix.diagonal_apply, ite_smul, zero_smul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  unfold krausChannel weighted
  apply Finset.sum_congr rfl
  intro i _
  simp only [Matrix.conjTranspose_smul, star_trivial, (hA i).eq,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, Real.mul_self_sqrt (hc i)]

theorem potential_eq (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i) (θ : ℝ) :
    ownerPotential H A (Matrix.diagonal c) θ = densityPotential H (weighted A c) θ := by
  unfold ownerPotential densityPotential
  congr 2
  funext S
  simp only [ownerObjective, densityObjective, source_eq A hA c hc]

variable {d : ℕ}

/-- Actual finite ellipsoid value report with explicitly weighted input matrices. -/
def report (a : Fin d) (H : Matrix (Fin d) (Fin d) ℂ)
    (A : ι → Matrix (Fin d) (Fin d) ℂ) (c : ι → ℝ) (hd : 0 < d) (θ ν : ℝ) : ℝ :=
  KSFullManuscriptValueOracle.report a H (weighted A c) hd θ ν

theorem report_accuracy (a : Fin d) (H : Matrix (Fin d) (Fin d) ℂ)
    (A : ι → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ i, (A i).IsHermitian)
    (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i) (hd : 0 < d)
    {θ ν : ℝ} (hθ : 0 ≤ θ) (hν : 0 < ν) :
    |report a H A c hd θ ν - ownerPotential H A (Matrix.diagonal c) θ| ≤ ν := by
  rw [potential_eq H A hA c hc]
  exact KSFullManuscriptValueOracle.report_accuracy a H (weighted A c) hd hθ hν

/-- Physical coordinates may be any explicitly supplied finite relabelling. -/
def reindexedReport (a : Fin d) (e : Fin d ≃ n) (H : Matrix n n ℂ)
    (A : ι → Matrix n n ℂ) (c : ι → ℝ) (hd : 0 < d) (θ ν : ℝ) : ℝ :=
  report a (H.submatrix e e) (fun i => (A i).submatrix e e) c hd θ ν

theorem reindexedReport_accuracy (a : Fin d) (e : Fin d ≃ n) (H : Matrix n n ℂ)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i) (hd : 0 < d)
    {θ ν : ℝ} (hθ : 0 ≤ θ) (hν : 0 < ν) :
    |reindexedReport a e H A c hd θ ν - ownerPotential H A (Matrix.diagonal c) θ| ≤ ν := by
  have h := report_accuracy a (H.submatrix e e) (fun i => (A i).submatrix e e)
    (fun i => (hA i).submatrix e) c hc hd hθ hν
  rw [KSOwnerReindex.ownerPotential_reindex H A hA
    (Matrix.posSemidef_diagonal_iff.mpr hc) θ e] at h
  exact h

end MatrixSpencer.KSFullManuscriptDiagonalValue
