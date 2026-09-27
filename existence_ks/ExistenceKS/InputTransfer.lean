import ExistenceKS.FrozenStatement
import MatrixSpencer.KSRankOne

/-! Conversion to the independently stated primitive target.
This helper performs only the input/output change of notation; its signing
premise must be discharged by the new radial walk in the final endpoint. -/
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace ExistenceKS.InputTransfer
open MatrixSpencer

theorem primitive_signing_of_atom_signing {N d : ℕ}
    (v : Fin N → Fin d → ℂ) (B : ℝ)
    (h : ∃ s : Fin N → ℝ, (∀ i, IsSign (s i)) ∧
      ‖∑ i, s i • KSRankOne.atom (v i)‖ ≤ B) :
    ∃ s : Fin N → ℝ, (∀ i, s i = 1 ∨ s i = -1) ∧
      ‖Matrix.toEuclideanCLM (𝕜 := ℂ)
        (∑ i, (s i : ℂ) •
          (fun a b => v i a * star (v i b) : Matrix (Fin d) (Fin d) ℂ))‖ ≤ B := by
  obtain ⟨s,hs,hbound⟩ := h
  refine ⟨s,hs,?_⟩
  have heq : (∑ i, (s i : ℂ) •
      (fun a b => v i a * star (v i b) : Matrix (Fin d) (Fin d) ℂ)) =
      ∑ i, s i • KSRankOne.atom (v i) := by
    apply Finset.sum_congr rfl
    intro i _
    ext a b
    simp only [Matrix.smul_apply, KSRankOne.atom_apply, Complex.real_smul]
    rfl
  rw [heq]
  exact hbound

theorem zero_dimension (C : ℝ) (hC : 0 ≤ C) (N : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (v : Fin N → Fin 0 → ℂ) :
    ∃ s : Fin N → ℝ, (∀ i, s i = 1 ∨ s i = -1) ∧
      ‖Matrix.toEuclideanCLM (𝕜 := ℂ)
        (∑ i, (s i : ℂ) •
          (fun a b => v i a * star (v i b) : Matrix (Fin 0) (Fin 0) ℂ))‖ ≤
          C * Real.sqrt ε := by
  refine ⟨fun _ => 1,fun _ => Or.inl rfl,?_⟩
  have heq : (∑ i, ((1 : ℝ) : ℂ) •
      (fun a b => v i a * star (v i b) : Matrix (Fin 0) (Fin 0) ℂ)) = 0 :=
    Subsingleton.elim _ _
  rw [heq, map_zero, norm_zero]
  exact mul_nonneg hC (Real.sqrt_nonneg ε)

/-- Assemble a primitive theorem after the actual positive-dimensional walk
has supplied its signing. No computational contract is part of this target. -/
theorem close_target_of_positive_dimension (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ (N d : ℕ), 0 < d → ∀ (ε : ℝ), 0 ≤ ε →
      ∀ v : Fin N → Fin d → ℂ,
        (∑ i, KSRankOne.atom (v i)) = 1 →
        (∀ i, ‖KSRankOne.atom (v i)‖ ≤ ε) →
        ∃ s : Fin N → ℝ, (∀ i, IsSign (s i)) ∧
          ‖∑ i, s i • KSRankOne.atom (v i)‖ ≤ C * Real.sqrt ε) :
    Frozen.statement C := by
  intro N d ε hε v hp hsize
  by_cases hd : d = 0
  · subst d
    exact zero_dimension C hC N ε hε v
  · have hp' : (∑ i, KSRankOne.atom (v i)) = 1 := hp
    have hsize' : ∀ i, ‖KSRankOne.atom (v i)‖ ≤ ε := hsize
    exact primitive_signing_of_atom_signing v (C * Real.sqrt ε)
      (h N d (Nat.pos_of_ne_zero hd) ε hε v hp' hsize')

end ExistenceKS.InputTransfer
