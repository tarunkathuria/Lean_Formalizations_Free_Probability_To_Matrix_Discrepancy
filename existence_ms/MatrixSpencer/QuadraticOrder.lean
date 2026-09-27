import MatrixSpencer.TensorContraction

/-!
# Quadratic forms and matrix order

These lemmas transfer the concrete tensor energy inequality to Loewner order.
The order is explicitly the matrix order, and all vector energies are complex
Euclidean energies.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder

noncomputable section

namespace MatrixSpencer

variable {s t u v : Type*} [Fintype s] [Fintype t] [Fintype u] [Fintype v]

/-- A real quadratic-form comparison suffices between Hermitian complex matrices. -/
theorem matrix_le_of_real_quadratic_le {A B : Matrix t t ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : ∀ x : t → ℂ, RCLike.re (star x ⬝ᵥ (A *ᵥ x)) ≤
      RCLike.re (star x ⬝ᵥ (B *ᵥ x))) : A ≤ B := by
  apply Matrix.le_iff.mpr
  refine ⟨hB.sub hA, fun x => ?_⟩
  apply RCLike.nonneg_iff.mpr
  constructor
  · simpa only [Matrix.sub_mulVec, dotProduct_sub, map_sub, sub_nonneg] using h x
  · exact (hB.sub hA).im_star_dotProduct_mulVec_self x

/-- The squared output norm of a rectangular matrix is its Gram quadratic form. -/
theorem vectorEnergy_mulVec_eq_pairing (A : Matrix s t ℂ) (x : t → ℂ) :
    vectorEnergy (A *ᵥ x) = RCLike.re (star x ⬝ᵥ ((Aᴴ * A) *ᵥ x)) := by
  rw [vectorEnergy_eq_pairing, Matrix.star_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_vecMul, ← Matrix.dotProduct_mulVec]

omit [Fintype s] in
/-- Matrix action commutes with a finite sum, in the concrete vector representation. -/
theorem matrixSum_mulVec (A : u → Matrix s t ℂ) (x : t → ℂ) :
    (∑ c, A c) *ᵥ x = ∑ c, A c *ᵥ x := by
  ext r
  simp only [Matrix.mulVec, dotProduct, Matrix.sum_apply,
    Finset.sum_mul, Finset.sum_apply]
  exact Finset.sum_comm

/-- A finite Gram sum, with a genuine matrix type before any order is inferred. -/
def gramSum (A : u → Matrix s t ℂ) : Matrix t t ℂ := ∑ c, (A c)ᴴ * A c

omit [Fintype t] in
theorem gramSum_isHermitian (A : u → Matrix s t ℂ) : (gramSum A).IsHermitian := by
  unfold gramSum Matrix.IsHermitian
  rw [Matrix.conjTranspose_sum]
  apply Finset.sum_congr rfl
  intro c _
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]

/-- Gram-sum quadratic forms are exactly sums of squared Euclidean norms. -/
theorem gramSum_pairing (A : u → Matrix s t ℂ) (x : t → ℂ) :
    RCLike.re (star x ⬝ᵥ ((gramSum A) *ᵥ x)) = ∑ c, vectorEnergy (A c *ᵥ x) := by
  have hs : (gramSum A) *ᵥ x = ∑ c, ((A c)ᴴ * A c) *ᵥ x := by
    ext r
    simp only [gramSum, Matrix.mulVec, dotProduct, Matrix.sum_apply,
      Finset.sum_mul, Finset.sum_apply]
    exact Finset.sum_comm
  rw [hs, dotProduct_sum, map_sum]
  apply Finset.sum_congr rfl
  intro c _
  exact (vectorEnergy_mulVec_eq_pairing _ _).symm

/-- An energy comparison for every vector is the asserted matrix Gram-sum bound. -/
theorem gramSum_le_of_energy_le
    {r : Type*} [Fintype r]
    (A : u → Matrix s t ℂ) (B : v → Matrix r t ℂ) (κ : ℝ)
    (h : ∀ x : t → ℂ, (∑ c, vectorEnergy (A c *ᵥ x)) ≤
      κ * ∑ c, vectorEnergy (B c *ᵥ x)) :
    gramSum A ≤ κ • gramSum B := by
  apply matrix_le_of_real_quadratic_le (gramSum_isHermitian A)
  · change (κ • gramSum B)ᴴ = κ • gramSum B
    rw [Matrix.conjTranspose_smul, star_trivial, (gramSum_isHermitian B).eq]
  · intro x
    simpa only [Matrix.smul_mulVec, dotProduct_smul, RCLike.smul_re,
      gramSum_pairing] using h x

end MatrixSpencer
