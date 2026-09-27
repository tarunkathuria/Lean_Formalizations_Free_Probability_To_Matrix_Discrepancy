import MatrixSpencer.KSJacobiRayleigh

/-!
# Entrywise finite-difference accuracy supplies the Jacobi matrix budget

Symmetrization is an explicit arithmetic operation. Entrywise error `κ/d`
therefore gives the operator error required by the constructed Jacobi vector.
This closes the matrix-norm bookkeeping; bounds on the actual reported
finite-difference entries remain to be supplied by their Taylor estimates.
-/

open Matrix
open scoped BigOperators
noncomputable section
namespace MatrixSpencer.KSMatrixEntryAccuracy

variable {d : ℕ}

def symmetrize (A : Matrix (Fin d) (Fin d) ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j => (A i j + A j i) / 2

theorem symmetrize_isSymm (A : Matrix (Fin d) (Fin d) ℝ) : (symmetrize A).IsSymm := by
  ext i j
  exact congrArg (fun t : ℝ => t / 2) (add_comm _ _)

theorem symmetrize_entry_error {K A : Matrix (Fin d) (Fin d) ℝ}
    (hK : K.IsSymm) {ε : ℝ} (hentry : ∀ i j, |K i j - A i j| ≤ ε) :
    ∀ i j, |K i j - symmetrize A i j| ≤ ε := by
  intro i j
  have hs : K j i = K i j := congrFun (congrFun hK i) j
  rcases abs_le.mp (hentry i j) with ⟨hl, hu⟩
  have ht := hentry j i
  rw [hs] at ht
  rcases abs_le.mp ht with ⟨hl', hu'⟩
  apply abs_le.mpr
  unfold symmetrize
  constructor <;> linarith

/-- A square matrix's Euclidean operator norm is at most dimension times
its uniform absolute entry bound. The bound also covers dimension zero. -/
theorem operatorNorm_le_card_mul (K : Matrix (Fin d) (Fin d) ℝ)
    {ε : ℝ} (hε : 0 ≤ ε) (hentry : ∀ i j, |K i j| ≤ ε) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) K‖ ≤ (d : ℝ) * ε := by
  apply (KSJacobiRayleigh.operatorNorm_le_frobenius K).trans
  apply (Real.sqrt_le_iff).mpr
  refine ⟨mul_nonneg (Nat.cast_nonneg _) hε, ?_⟩
  calc
    KSJacobiStep.frobeniusEnergy K ≤ ∑ _i : Fin d, ∑ _j : Fin d, ε ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      nlinarith [sq_abs (K i j), sq_nonneg (ε - |K i j|), hentry i j, abs_nonneg (K i j)]
    _ = ((d : ℝ) * ε) ^ 2 := by simp; ring

theorem symmetrized_operator_error {K A : Matrix (Fin d) (Fin d) ℝ}
    (hK : K.IsSymm) (hd : 0 < d) {κ : ℝ} (hκ : 0 ≤ κ)
    (hentry : ∀ i j, |K i j - A i j| ≤ κ / d) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (K - symmetrize A)‖ ≤ κ := by
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hh := operatorNorm_le_card_mul (K - symmetrize A) (div_nonneg hκ hdr.le)
    (symmetrize_entry_error hK hentry)
  rwa [mul_div_cancel₀ κ (ne_of_gt hdr)] at hh

/-- The actual finite Jacobi output on the symmetrized report satisfies the
required Rayleigh bound from entry accuracies alone. -/
theorem jacobi_output_accuracy {K A : Matrix (Fin d) (Fin d) ℝ}
    (hK : K.IsSymm) (hd : 0 < d) {κ : ℝ} (hκ : 0 < κ)
    (hentry : ∀ i j, |K i j - A i j| ≤ κ / d) :
    ‖KSJacobiRayleigh.outputVector (symmetrize A) κ hd‖ = 1 ∧
      KSRayleighAccuracy.realRayleigh K (KSJacobiRayleigh.outputVector (symmetrize A) κ hd) ≤
        KSRayleighAccuracy.leastRayleigh K + 3 * κ :=
  KSJacobiRayleigh.outputVector_accuracy_of_matrix_error K (symmetrize A) (symmetrize_isSymm A) hκ hd
    (symmetrized_operator_error hK hd hκ.le hentry)

end MatrixSpencer.KSMatrixEntryAccuracy
