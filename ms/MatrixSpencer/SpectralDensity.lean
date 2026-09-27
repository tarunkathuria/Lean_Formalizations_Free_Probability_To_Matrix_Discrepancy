import MatrixSpencer.DensityPotential

/-!
# Spectral witnesses in the actual density domain

Every eigenvalue of a Hermitian center is realized by the trace pairing
with a concrete rank-one density. This connects the potential to spectral
bounds without postulating a maximizer of the Rayleigh quotient.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix

noncomputable section

namespace MatrixSpencer

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The rank-one density associated with an actual spectral-theorem eigenvector. -/
def eigenDensity {H : Matrix n n ℂ} (hH : H.IsHermitian) (i : n) : Matrix n n ℂ :=
  (hH.eigenvectorUnitary : Matrix n n ℂ) * Matrix.diagonal (Pi.single i (1 : ℂ)) *
    (hH.eigenvectorUnitary : Matrix n n ℂ)ᴴ

theorem eigenDensity_mem {H : Matrix n n ℂ} (hH : H.IsHermitian) (i : n) :
    eigenDensity hH i ∈ densitySet := by
  classical
  have hE : (Matrix.diagonal (Pi.single i (1 : ℂ))).PosSemidef := by
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro j
    simp only [Pi.single_apply]
    split_ifs <;> positivity
  refine ⟨hE.mul_mul_conjTranspose_same _, ?_⟩
  have hV : (hH.eigenvectorUnitary : Matrix n n ℂ)ᴴ *
      (hH.eigenvectorUnitary : Matrix n n ℂ) = 1 := unitary.coe_star_mul_self hH.eigenvectorUnitary
  unfold eigenDensity
  rw [realTrace_mul_cycle, hV, Matrix.one_mul]
  simp [realTrace]

/-- Its pairing with the center equals the selected real eigenvalue. -/
theorem realTrace_mul_eigenDensity {H : Matrix n n ℂ} (hH : H.IsHermitian) (i : n) :
    realTrace (H * eigenDensity hH i) = hH.eigenvalues i := by
  classical
  let V : Matrix n n ℂ := hH.eigenvectorUnitary
  let E : Matrix n n ℂ := Matrix.diagonal (Pi.single i (1 : ℂ))
  let D : Matrix n n ℂ := Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues)
  have hV : Vᴴ * V = 1 := unitary.coe_star_mul_self hH.eigenvectorUnitary
  have hspec : H = V * D * Vᴴ := hH.spectral_theorem
  change realTrace (H * (V * E * Vᴴ)) = _
  conv_lhs => rw [hspec]
  calc
    _ = realTrace (V * (D * E) * Vᴴ) := by
      congr 1
      calc
        _ = V * D * (Vᴴ * V) * E * Vᴴ := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hV, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = realTrace (D * E) := by rw [realTrace_mul_cycle, hV, Matrix.one_mul]
    _ = _ := by simp [D, E, Matrix.diagonal_mul_diagonal, realTrace, Pi.single_apply]

/-- Every spectral value is bounded by the actual potential when the regularizer is nonnegative. -/
theorem eigenvalue_le_densityPotential [Nonempty n]
    {ι : Type*} [Fintype ι] {H : Matrix n n ℂ} (hH : H.IsHermitian)
    (B : ι → Matrix n n ℂ) {θ : ℝ} (hθ : 0 ≤ θ) (i : n) :
    hH.eigenvalues i ≤ densityPotential H B θ := by
  have hb := densityObjective_le_potential H B θ (eigenDensity_mem hH i)
  have hf := fidelity_nonneg (eigenDensity hH i) (krausChannel B (eigenDensity hH i))
  have hr := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hθ)
    (realTrace_nonneg (CFC.sqrt_nonneg (eigenDensity hH i)).posSemidef)
  unfold densityObjective at hb
  rw [realTrace_mul_eigenDensity] at hb
  linarith

/-- Any feasible density supplies a spectral lower bound for the actual potential. -/
theorem realTrace_le_densityPotential [Nonempty n]
    {ι : Type*} [Fintype ι] (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    {θ : ℝ} (hθ : 0 ≤ θ) {S : Matrix n n ℂ} (hS : S ∈ densitySet) :
    realTrace (H * S) ≤ densityPotential H B θ := by
  have hb := densityObjective_le_potential H B θ hS
  have hf := fidelity_nonneg S (krausChannel B S)
  have hr := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hθ)
    (realTrace_nonneg (CFC.sqrt_nonneg S).posSemidef)
  unfold densityObjective at hb
  linarith

end MatrixSpencer
