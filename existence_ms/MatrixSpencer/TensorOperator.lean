import MatrixSpencer.QuadraticOrder

/-!
# Matrix-order consequence of the two tensor flattenings

The concrete product family `sum_b M_b D_a R_b` satisfies a Gram-sum order
bound. This is the tensor-composition step in the high-spectrum Kraus bound.
Both flattening caps are actual Loewner inequalities on explicitly typed
complex matrices.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

noncomputable section

namespace MatrixSpencer

variable {a b i l j q : Type*}
  [Fintype a] [Fintype b] [Fintype i] [Fintype l] [Fintype j] [Fintype q]
  [DecidableEq b] [DecidableEq l] [DecidableEq j]

/-- The exact high-tensor order inequality before specializing its physical factors. -/
theorem mixedProduct_gramSum_le
    (M : b → Matrix i l ℂ) (D : a → Matrix l j ℂ) (R : b → Matrix j q ℂ)
    {α β : ℝ} (hβ : 0 ≤ β)
    (hF : let F : Matrix (i × l) b ℂ := fun uv r => M r uv.1 uv.2
      Fᴴ * F ≤ α • (1 : Matrix b b ℂ))
    (hG : let G : Matrix a (l × j) ℂ := fun c vz => D c vz.1 vz.2
      Gᴴ * G ≤ β • (1 : Matrix (l × j) (l × j) ℂ)) :
    gramSum (fun c => ∑ r, M r * D c * R r) ≤ (β * α) • gramSum R := by
  apply gramSum_le_of_energy_le
  intro x
  have h := mixedProduct_energy_le_of_gram_caps M D
    (fun r => R r *ᵥ x) hβ hF hG
  have he : entryEnergy (fun u c => ∑ r, ((M r * D c) *ᵥ (R r *ᵥ x)) u) =
      ∑ c, vectorEnergy ((∑ r, M r * D c * R r) *ᵥ x) := by
    simp only [entryEnergy, vectorEnergy, matrixSum_mulVec, Finset.sum_apply,
      Matrix.mulVec_mulVec]
    exact Finset.sum_comm
  rw [he] at h
  exact h

end MatrixSpencer
