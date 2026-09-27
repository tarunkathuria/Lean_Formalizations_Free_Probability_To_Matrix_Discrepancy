import HigherRankKS.Statement
import HigherRankKS.ExistenceReduction

/-!
# Conditional internal adapter to the literal existence statement

This file does not prove the final unconditional theorem. It packages the
compact-minimum and regularization reductions under the remaining family of
actual dyadic local alternatives. Once that local theorem is proved, the
literal statement follows by one application of this adapter.
-/

open Matrix MatrixSpencer
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace HigherRankKS

/-- The complex-scalar signed sum agrees with the real-scalar potential center. -/
theorem signedSum_eq_center {N d : ℕ} (A : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (σ : Fin N → ℝ) : signedSum A σ = KSPotentialModels.center A σ := by
  apply Finset.sum_congr rfl
  intro i _
  ext j k
  simp only [Matrix.smul_apply, Complex.real_smul, smul_eq_mul]

/-- The matrix C-star norm is precisely the Euclidean operator norm used in the target. -/
theorem norm_toEuclideanCLM {d : ℕ} (M : Matrix (Fin d) (Fin d) ℂ) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) M‖ = ‖M‖ := rfl

/-- A zero-dimensional input has a literal real signing without any local analysis. -/
theorem exists_signing_dimension_zero (N r : ℕ) (hr : 1 ≤ r) (ε : ℝ)
    (A : Fin N → Matrix (Fin 0) (Fin 0) ℂ) :
    ∃ σ : Fin N → ℝ, (∀ i, σ i = 1 ∨ σ i = -1) ∧
      ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (signedSum A σ)‖ ≤
        min 1 (250 * Real.sqrt ε * Real.log (2 * (r : ℝ))) := by
  refine ⟨fun _ => 1, fun _ => Or.inl rfl, ?_⟩
  have hz : signedSum A (fun _ => 1) = 0 := Subsingleton.elim _ _
  rw [hz, map_zero, norm_zero]
  apply le_min zero_le_one
  apply mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
  apply Real.log_nonneg
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  linarith

/-- Conditional internal reduction: only the actual dyadic local alternatives remain.
This theorem is deliberately not an unconditional proof of `ExistenceStatement`. -/
theorem existenceStatement_of_dyadic_local_alternatives
    (halternative : ∀ (N d : ℕ), 0 < d →
      ∀ A : Fin N → Matrix (Fin d) (Fin d) ℂ,
        (∀ i, (A i).PosSemidef) → (∑ i, A i) = 1 →
        ∀ k : ℕ, 1 ≤ k → LocalAlternativeAtMinima A ((1 : ℝ) / 2 ^ k)) :
    ExistenceStatement := by
  intro N d r ε hr hε A hA hsum hnorm hrank
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst d
    exact exists_signing_dimension_zero N r hr ε A
  · letI : NeZero d := ⟨hd.ne'⟩
    obtain ⟨q, ⟨k, hkq⟩, hq, hqlog, hqupper, _⟩ := exists_dyadic_parameters hr
    have hk : 1 ≤ k := by
      by_contra h
      have : k = 0 := by omega
      simp only [this, pow_zero] at hkq
      omega
    have hlocal : LocalAlternativeAtMinima A ((1 : ℝ) / q) := by
      simpa only [hkq, Nat.cast_pow, Nat.cast_ofNat] using halternative N d hd A hA hsum k hk
    obtain ⟨σ, hσ, hbound⟩ := exists_signing_of_local_alternative A hA
      (le_of_eq hsum) hε (fun i => by simpa only [norm_toEuclideanCLM] using hnorm i)
      hr hrank hq hqlog hqupper hlocal
    exact ⟨σ, hσ, by simpa only [norm_toEuclideanCLM, signedSum_eq_center] using hbound⟩

end HigherRankKS
