import HigherRankKS.Optimizer
import MatrixSpencer.KSSignSymmetry

/-! Spin symmetry of the actual higher-rank optimizing density. -/

open Matrix MatrixSpencer MatrixSpencer.KSSignSymmetry
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

noncomputable section
namespace HigherRankKS

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]

theorem marginal_sign_conjugate (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) :
    marginal (conjugate signMatrix S) = marginal S := by
  rw [sign_conjugate_blocks]
  rfl

theorem source_sign_input (A : ι → Matrix n n ℂ) (β : ℝ) (c : ι → ℝ)
    (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) :
    source A β c (conjugate signMatrix S) = source A β c S := by
  simp only [source, sourceTerm, sourceBlock, carrier, marginal_sign_conjugate]

theorem source_sign_output (A : ι → Matrix n n ℂ) (β : ℝ) (c : ι → ℝ)
    (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) :
    conjugate signMatrix (source A β c S) = source A β c S := by
  simp only [source, conjugate, Matrix.mul_sum, Matrix.sum_mul,
    Matrix.mul_smul, Matrix.smul_mul]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact conjugate_eq_of_commute signMatrix_sq (signMatrix_commute_doubled _)

theorem objective_sign_invariant (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ)
    (β : ℝ) {c : ι → ℝ} (hc : ∀ i, 0 ≤ c i) (θ : ℝ)
    {S : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hS : S.PosSemidef) :
    objective (signedLift H) A β c θ (conjugate signMatrix S) =
      objective (signedLift H) A β c θ S := by
  have hf := fidelity_conjugate signMatrix_isHermitian signMatrix_sq hS
    (source_posSemidef A β hc hS)
  rw [source_sign_output A β c S] at hf
  simp only [objective, source_sign_input A β c S, hf,
    trace_center_conjugate signMatrix_isHermitian signMatrix_sq (signMatrix_commute_signedLift H),
    sqrt_conjugate signMatrix_isHermitian signMatrix_sq hS,
    realTrace_conjugate signMatrix_isHermitian signMatrix_sq]

theorem optimizer_blockDiagonal (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ)
    {β : ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    {c : ι → ℝ} (hc : ∀ i, 0 ≤ c i) {θ : ℝ} (hθ : 0 < θ)
    {S : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hS : S ∈ densitySet)
    (hmax : ∀ T ∈ densitySet, objective (signedLift H) A β c θ T ≤
      objective (signedLift H) A β c θ S) :
    S = Matrix.fromBlocks S.toBlocks₁₁ 0 0 S.toBlocks₂₂ := by
  have hval := objective_sign_invariant H A β hc θ hS.1
  have hJS := conjugate_mem_density signMatrix_isHermitian signMatrix_sq hS
  apply sign_fixed_blockDiagonal
  exact (strictConcaveOn_objective (signedLift H) A hβ hβ1 hc hθ).eq_of_isMaxOn
    (fun T hT => (hmax T hT).trans_eq hval.symm) hmax hJS hS

end HigherRankKS
