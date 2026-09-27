import AugmentedHigherRankKS.DyadicExistence
import AugmentedHigherRankKS.Statement

/-! Pure matrix-input existence theorem for the augmented-reserve proof.
No solver, eigendecomposition, favorable covariance, local direction,
iteration count, or successful endpoint is an input to this theorem. -/
open Matrix MatrixSpencer
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace AugmentedHigherRankKS
local instance existenceCStar {n : Type*} [Fintype n] [DecidableEq n] :
    CStarAlgebra (Matrix n n ℂ) := {}

theorem signedSum_eq_real_sum {N d : ℕ} (A : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (σ : Fin N → ℝ) : HigherRankKS.signedSum A σ = ∑ i, σ i • A i := by
  apply Finset.sum_congr rfl
  intro i hi
  ext j k
  simp only [Matrix.smul_apply, Complex.real_smul, smul_eq_mul]

/-- Main subisotropic existence result, proved by the new reserve epochs. -/
theorem subisotropic_existence : SubisotropicExistenceStatement := by
  intro N d r ε hr hε A hA hsum hnorm hrank
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst d
    refine ⟨fun _ => 1, fun _ => Or.inl rfl, ?_⟩
    have hz : HigherRankKS.signedSum A (fun _ => 1) = 0 := Subsingleton.elim _ _
    rw [hz, map_zero, norm_zero]
    exact le_min zero_le_one (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
  · letI : NeZero d := ⟨hd.ne'⟩
    have hmasspos : (0 : Matrix (Fin d) (Fin d) ℂ) ≤ ∑ i, A i :=
      Finset.sum_nonneg fun i _ => (hA i).nonneg
    have hmass : ‖∑ i, A i‖ ≤ 1 := by
      simpa only [norm_one] using CStarAlgebra.norm_le_norm_of_nonneg_of_le hmasspos hsum
    by_cases hlarge : 1 ≤ 10000 * Real.sqrt (ε * Real.log (2 * (r : ℝ)))
    · refine ⟨fun _ => 1, fun _ => Or.inl rfl, ?_⟩
      rw [min_eq_left hlarge]
      change ‖HigherRankKS.signedSum A (fun _ => 1)‖ ≤ 1
      simpa [HigherRankKS.signedSum] using hmass
    · obtain ⟨q, ⟨k, hkq⟩, hq, hqlog, hqupper, hβ, hβ2, hrr, _⟩ :=
        HigherRankKS.exists_dyadic_parameters hr
      have hk : 1 ≤ k := by
        by_contra hn
        have hk0 : k = 0 := by omega
        simp only [hk0, pow_zero] at hkq
        omega
      have hqcast : (q : ℝ) = (2 : ℝ)^k := by exact_mod_cast hkq
      have hrr' : (r : ℝ)^((1 : ℝ) / 2 ^ k) ≤ 2 := by simpa only [hqcast] using hrr
      obtain ⟨σ, hσ, hbound⟩ := exists_dyadic_signing A hA hε hnorm hrank k hk hrr'
      refine ⟨σ, hσ, ?_⟩
      rw [min_eq_right (le_of_not_ge hlarge)]
      change ‖HigherRankKS.signedSum A σ‖ ≤ _
      rw [signedSum_eq_real_sum]
      have hs : Real.sqrt ‖∑ i, A i‖ ≤ 1 := by
        simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hmass
      have hnonneg : 0 ≤ 512 * Real.sqrt (ε / ((1 : ℝ) / 2 ^ k)) := by positivity
      have hnorm' := hbound.trans (mul_le_mul_of_nonneg_left hs hnonneg)
      rw [mul_one] at hnorm'
      have he : ε / ((1 : ℝ) / 2 ^ k) = ε * q := by
        rw [hqcast]
        field_simp
      rw [he] at hnorm'
      exact hnorm'.trans (existence_log_constant hr hqupper hε)

/-- The isotropic theorem has exactly the original matrix input assumptions. -/
theorem existence : ExistenceStatement :=
  existenceStatement_of_subisotropic subisotropic_existence

end AugmentedHigherRankKS
