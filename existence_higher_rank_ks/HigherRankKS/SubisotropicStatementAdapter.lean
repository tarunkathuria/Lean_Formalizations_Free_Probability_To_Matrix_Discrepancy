import HigherRankKS.StatementAdapter



open Matrix MatrixSpencer
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace HigherRankKS

/-- Literal complex-Hermitian subisotropic signing statement from Part III.
Each sign multiplies its whole original matrix. -/
def SubisotropicExistenceStatement : Prop :=
  ∀ (N d r : ℕ) (ε : ℝ), 1 ≤ r → 0 ≤ ε →
    ∀ A : Fin N → Matrix (Fin d) (Fin d) ℂ,
      (∀ i, (A i).PosSemidef) →
      (∑ i, A i) ≤ 1 →
      (∀ i, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A i)‖ ≤ ε) →
      (∀ i, Matrix.rank (A i) ≤ r) →
      ∃ σ : Fin N → ℝ,
        (∀ i, σ i = 1 ∨ σ i = -1) ∧
        ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (signedSum A σ)‖ ≤
          min 1 (250 * Real.sqrt ε * Real.log (2 * (r : ℝ)))

/-- Conditional internal reduction for the full subisotropic input scope. -/
theorem subisotropicExistenceStatement_of_dyadic_local_alternatives
    (halternative : ∀ (N d : ℕ), 0 < d →
      ∀ A : Fin N → Matrix (Fin d) (Fin d) ℂ,
        (∀ i, (A i).PosSemidef) → (∑ i, A i) ≤ 1 →
        ∀ k : ℕ, 1 ≤ k → LocalAlternativeAtMinima A ((1 : ℝ) / 2 ^ k)) :
    SubisotropicExistenceStatement := by
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
    obtain ⟨σ, hσ, hbound⟩ := exists_signing_of_local_alternative A hA hsum hε
      (fun i => by simpa only [norm_toEuclideanCLM] using hnorm i)
      hr hrank hq hqlog hqupper hlocal
    exact ⟨σ, hσ, by simpa only [norm_toEuclideanCLM, signedSum_eq_center] using hbound⟩

/-- A proved subisotropic theorem also certifies the unchanged isotropic target. -/
theorem existenceStatement_of_subisotropic (h : SubisotropicExistenceStatement) :
    ExistenceStatement := by
  intro N d r ε hr hε A hA hsum hnorm hrank
  exact h N d r ε hr hε A hA (le_of_eq hsum) hnorm hrank

end HigherRankKS
