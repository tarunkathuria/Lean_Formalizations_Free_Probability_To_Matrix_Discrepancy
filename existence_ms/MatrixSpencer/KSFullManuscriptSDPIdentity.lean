import MatrixSpencer.KSFullManuscriptFidelityBlockUpper
import MatrixSpencer.DensityFaithfulness

/-!
# Exact semidefinite representation of the full-cube objective

The regularizer block and the fidelity block have explicit attaining points.
For the source-regularized problem the lower-right source is positive definite,
so attainment holds for every density, including singular densities. For the
unregularized Kraus objective, the actual faithful density optimizer proves
attainment of the whole SDP. These are representation theorems, not numerical
calls to a matrix square root or optimizer.
-/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSFullManuscriptSDPIdentity

open KSFullManuscriptFidelityBlockUpper
variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι]

omit [Fintype ι] in
theorem fidelity_one {S : Matrix n n ℂ} (hS : S.PosSemidef) :
    fidelity S 1 = realTrace (CFC.sqrt S) := by
  unfold fidelity fidelityCore
  rw [Matrix.mul_one, CFC.sqrt_mul_sqrt_self S hS.nonneg]

omit [Fintype ι] in
theorem regularizer_block {S : Matrix n n ℂ} (hS : S.PosSemidef) :
    (Matrix.fromBlocks S (CFC.sqrt S) (CFC.sqrt S) 1).PosSemidef := by
  letI : Invertible (1 : Matrix n n ℂ) := invertibleOne
  have hs : (CFC.sqrt S).IsHermitian := (CFC.sqrt_nonneg S).posSemidef.isHermitian
  have hh : (Matrix.fromBlocks S (CFC.sqrt S) (CFC.sqrt S)ᴴ 1).PosSemidef := by
    apply (Matrix.PosDef.one.fromBlocks₂₂ S (CFC.sqrt S)).mpr
    simp only [inv_one, Matrix.mul_one, hs.eq, CFC.sqrt_mul_sqrt_self S hS.nonneg,
      sub_self]
    exact Matrix.PosSemidef.zero
  simpa only [hs.eq] using hh

omit [Fintype ι] in
theorem regularizer_bound {S Y : Matrix n n ℂ} (hS : S.PosSemidef)
    (hY : Y.IsHermitian) (hblock : (Matrix.fromBlocks S Y Y 1).PosSemidef) :
    realTrace Y ≤ realTrace (CFC.sqrt S) := by
  rw [← fidelity_one hS]
  apply block_trace_le_fidelity
  simpa only [hY.eq] using hblock

omit [Fintype ι] in
theorem fidelity_attainment_right {S M : Matrix n n ℂ}
    (hS : S.PosSemidef) (hM : M.PosDef) :
    ∃ X : Matrix n n ℂ, (Matrix.fromBlocks S X Xᴴ M).PosSemidef ∧
      realTrace X = fidelity S M := by
  obtain ⟨X, hX, ht⟩ := KSFullManuscriptFidelityBlock.exists_attaining_block hM hS
  refine ⟨Xᴴ, ?_, ?_⟩
  · simpa only [Matrix.fromBlocks_submatrix_sum_swap_sum_swap, Matrix.conjTranspose_conjTranspose]
      using hX.submatrix Sum.swap
  · rw [realTrace_conjTranspose, ht, fidelity_symm hM.posSemidef hS]

/-- The exact original block constraints, with optional source regularization. -/
def Feasible (Ω : Matrix n n ℂ → Matrix n n ℂ) (lam : ℝ)
    (S Y Z : Matrix n n ℂ) : Prop :=
  realTrace S = 1 ∧ Y.PosSemidef ∧
    (Matrix.fromBlocks S Z Zᴴ (Ω S + lam • 1)).PosSemidef ∧
    (Matrix.fromBlocks S Y Y 1).PosSemidef

def value (H : Matrix n n ℂ) (θ : ℝ) (S Y Z : Matrix n n ℂ) : ℝ :=
  realTrace (H * S) + 2 * realTrace Z + 2 * θ * realTrace Y

def objective (H : Matrix n n ℂ) (Ω : Matrix n n ℂ → Matrix n n ℂ) (θ lam : ℝ)
    (S : Matrix n n ℂ) : ℝ :=
  realTrace (H * S) + 2 * fidelity S (Ω S + lam • 1) + 2 * θ * realTrace (CFC.sqrt S)

omit [Fintype ι] in
theorem feasible_density {Ω : Matrix n n ℂ → Matrix n n ℂ} {lam : ℝ} {S Y Z : Matrix n n ℂ}
    (h : Feasible Ω lam S Y Z) : S ∈ densitySet := by
  refine ⟨?_, h.1⟩
  simpa only [Matrix.submatrix, Matrix.fromBlocks_apply₁₁] using h.2.2.1.submatrix Sum.inl

omit [Fintype ι] in
theorem feasible_value_le {H : Matrix n n ℂ} {Ω : Matrix n n ℂ → Matrix n n ℂ}
    {θ lam : ℝ} {S Y Z : Matrix n n ℂ} (hθ : 0 ≤ θ) (h : Feasible Ω lam S Y Z) :
    value H θ S Y Z ≤ objective H Ω θ lam S := by
  have hS := (feasible_density h).1
  have hZ := block_trace_le_fidelity h.2.2.1
  have hY := regularizer_bound hS h.2.1.isHermitian h.2.2.2
  unfold value objective
  nlinarith

omit [Fintype ι] in
theorem fixed_density_attainment {H : Matrix n n ℂ} {Ω : Matrix n n ℂ → Matrix n n ℂ}
    {θ lam : ℝ} {S : Matrix n n ℂ} (hS : S ∈ densitySet)
    (hM : (Ω S + lam • 1).PosDef) :
    ∃ Y Z : Matrix n n ℂ, Feasible Ω lam S Y Z ∧ value H θ S Y Z = objective H Ω θ lam S := by
  obtain ⟨Z, hZ, ht⟩ := fidelity_attainment_right hS.1 hM
  refine ⟨CFC.sqrt S, Z, ⟨hS.2, (CFC.sqrt_nonneg _).posSemidef, hZ, regularizer_block hS.1⟩, ?_⟩
  simp only [value, objective, ht]

/-- The unregularized SDP has a genuine maximizing triple and its optimum is
exactly the actual Kraus density potential, using its proved faithful optimizer. -/
theorem original_SDP_exact [Nonempty n] (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    {θ : ℝ} (hθ : 0 < θ) :
    ∃ S Y Z : Matrix n n ℂ,
      Feasible (krausChannel B) 0 S Y Z ∧ value H θ S Y Z = densityPotential H B θ ∧
      ∀ S' Y' Z', Feasible (krausChannel B) 0 S' Y' Z' →
        value H θ S' Y' Z' ≤ value H θ S Y Z := by
  let S := densityOptimizer H B θ
  have hs : S ∈ densitySet := densityOptimizer_mem H B θ
  have hp : S.PosDef := densityOptimizer_posDef H B hθ
  obtain ⟨Z, hZ, ht⟩ := KSFullManuscriptFidelityBlock.exists_attaining_block hp (krausChannel_posSemidef B hs.1)
  have hv : value H θ S (CFC.sqrt S) Z = densityPotential H B θ := by
    rw [densityPotential_eq_of_maximizer H B θ hs (densityOptimizer_isMaxOn H B θ)]
    simp only [value, densityObjective, ht]
  refine ⟨S, CFC.sqrt S, Z, ?_, hv, ?_⟩
  · simpa only [Feasible, zero_smul, add_zero] using
      And.intro hs.2 (And.intro (CFC.sqrt_nonneg S).posSemidef (And.intro hZ (regularizer_block hs.1)))
  · intro S' Y' Z' hh
    rw [hv]
    have hb := feasible_value_le (H := H) hθ.le hh
    have he : objective H (krausChannel B) θ 0 S' = densityObjective H B θ S' := by
      simp only [objective, densityObjective, zero_smul, add_zero]
    rw [he] at hb
    exact hb.trans (densityObjective_le_potential H B θ (feasible_density hh))

end MatrixSpencer.KSFullManuscriptSDPIdentity
