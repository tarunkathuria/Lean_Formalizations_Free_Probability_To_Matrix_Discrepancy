import ExistenceMS.RealInput
import FaithfulMS.SquareDirectExplicit
import FaithfulMS.RectangularDirectExistence

/-! Public existence-only endpoints. N is the number of matrices, d their
size. Neither a solver nor a runtime, density, or walk certificate is assumed. -/
open Matrix
open scoped BigOperators
noncomputable section
namespace FaithfulExistenceMS

theorem rectangular_bound {N d : ℕ} (hN : 1 ≤ N) (hNd : N ≤ d) :
    MatrixSpencer.RectangularDirectOriginal.discrepancyBound N d ≤
      100000000 * Real.sqrt ((N : ℝ) * Real.log (2 * (d : ℝ) / (N : ℝ))) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNdR : (N : ℝ) ≤ d := by exact_mod_cast hNd
  have hratio : (2 : ℝ) ≤ 2 * (d : ℝ) / N := by
    apply (le_div_iff₀ hNp).mpr
    linarith
  have hhalf : (1/2 : ℝ) ≤ Real.log (2 * (d : ℝ) / N) := by
    have htwo : (1/2 : ℝ) ≤ Real.log 2 := by
      have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at h ⊢
      exact h
    exact htwo.trans (Real.log_le_log (by norm_num) hratio)
  have hs : Real.sqrt ((N : ℝ) * (1 + Real.log (2 * (d : ℝ) / N))) ≤
      2 * Real.sqrt ((N : ℝ) * Real.log (2 * (d : ℝ) / N)) := by
    calc
      _ ≤ Real.sqrt (4 * ((N : ℝ) * Real.log (2 * (d : ℝ) / N))) := by
        apply Real.sqrt_le_sqrt
        nlinarith
      _ = _ := by rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]; norm_num
  unfold MatrixSpencer.RectangularDirectOriginal.discrepancyBound
  calc
    _ ≤ 8102676 * (2 * Real.sqrt ((N : ℝ) * Real.log (2 * (d : ℝ) / N))) :=
      mul_le_mul_of_nonneg_left hs (by norm_num)
    _ ≤ _ := by nlinarith [Real.sqrt_nonneg ((N : ℝ) * Real.log (2 * (d : ℝ) / N))]


theorem exists_square (N d : ℕ) (hdN : d ≤ N)
    (A : Fin N → Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀ i, (A i)ᵀ = A i)
    (hAn : ∀ i, ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (A i)‖ ≤ 1) :
    ∃ s : Fin N → ℝ, (∀ i, s i = 1 ∨ s i = -1) ∧
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (∑ i, s i • A i)‖ ≤
        100000000 * Real.sqrt (N : ℝ) :=
by
  letI : FaithfulMS.SquareDirectOracle.Oracle := ⟨FaithfulMS.DirectSDP.exactService⟩
  apply ExistenceMS.RealInput.signing_bound_of_complex A _
  let B : Fin N → MatrixSpencer.CMatrix d := fun i => MatrixSpencer.realMatrixEmbedding (A i)
  have hB : ∀ i, (B i).IsHermitian :=
    fun i => ExistenceMS.RealInput.embedding_hermitian_of_symmetric (A i) (hA i)
  have hBn : ∀ i, MatrixSpencer.spectralNorm (B i) ≤ 1 := by
    intro i
    simpa only [B, MatrixSpencer.spectralNorm, ExistenceMS.RealInput.realMatrixEmbedding_norm] using hAn i
  obtain ⟨s, hs, hb⟩ := FaithfulMS.SquareDirectExplicit.exists_full_signing B hB hBn hdN
  refine ⟨s, hs, hb.trans ?_⟩
  exact mul_le_mul_of_nonneg_right (by norm_num : (10651761 : ℝ) ≤ 100000000)
    (Real.sqrt_nonneg (N : ℝ))

theorem exists_rectangular (N d : ℕ) (hN : 1 ≤ N) (hNd : N ≤ d)
    (A : Fin N → Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀ i, (A i)ᵀ = A i)
    (hAn : ∀ i, ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (A i)‖ ≤ 1) :
    ∃ s : Fin N → ℝ, (∀ i, s i = 1 ∨ s i = -1) ∧
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (∑ i, s i • A i)‖ ≤
        100000000 * Real.sqrt ((N : ℝ) * Real.log (2*(d : ℝ)/(N : ℝ))) :=
by
  apply ExistenceMS.RealInput.signing_bound_of_complex A _
  let B : Fin N → MatrixSpencer.CMatrix d := fun i => MatrixSpencer.realMatrixEmbedding (A i)
  have hB : ∀ i, (B i).IsHermitian :=
    fun i => ExistenceMS.RealInput.embedding_hermitian_of_symmetric (A i) (hA i)
  have hBn : ∀ i, MatrixSpencer.spectralNorm (B i) ≤ 1 := by
    intro i
    simpa only [B, MatrixSpencer.spectralNorm, ExistenceMS.RealInput.realMatrixEmbedding_norm] using hAn i
  obtain ⟨s, hs, hb⟩ := MatrixSpencer.RectangularDirectExistence.exists_signing hNd B hB hBn
  exact ⟨s, hs, hb.trans (rectangular_bound hN hNd)⟩

end FaithfulExistenceMS
