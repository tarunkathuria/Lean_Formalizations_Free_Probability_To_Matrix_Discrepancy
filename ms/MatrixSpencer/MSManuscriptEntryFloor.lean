import MatrixSpencer.KSJacobiTraceSqrt

/-! Entrywise residual bounds imply a genuine matrix floor. -/
open Matrix
open scoped BigOperators MatrixOrder
noncomputable section
namespace MatrixSpencer.MSManuscriptEntryFloor
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem operator_le_entry_bound (E : Matrix ι ι ℝ) {e : ℝ} (he : 0 ≤ e)
    (hE : ∀ i j, |E i j| ≤ e) : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) E‖ ≤ (Fintype.card ι:ℝ)*e := by
  apply (KSJacobiRayleigh.operatorNorm_le_frobenius E).trans
  apply (Real.sqrt_le_iff).mpr
  refine ⟨by positivity, ?_⟩
  calc
    KSJacobiStep.frobeniusEnergy E ≤ ∑ _i : ι, ∑ _j : ι, e^2 := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (E i j)) he).mpr (hE i j)
    _ = ((Fintype.card ι:ℝ)*e)^2 := by simp; ring

theorem floor_of_entries (P : Matrix ι ι ℝ) (hP : P.IsSymm) {a e : ℝ} (he : 0 ≤ e)
    (hdiag : ∀ i, a ≤ P i i) (hoff : ∀ i j, i≠j → |P i j| ≤ e) :
    (a-(Fintype.card ι:ℝ)*e) • (1 : Matrix ι ι ℝ) ≤ P := by
  let D := Matrix.diagonal (fun i => P i i)
  have hde : D-a • (1 : Matrix ι ι ℝ) = Matrix.diagonal (fun i => P i i-a) := by
    ext i j
    by_cases hij : i=j <;> simp [D,hij]
  have hd : (D-a • (1 : Matrix ι ι ℝ)).PosSemidef := by
    rw [hde]
    exact Matrix.PosSemidef.diagonal (fun i => sub_nonneg.mpr (hdiag i))
  have hsym : (D-P).IsSymm := by
    exact (Matrix.isSymm_diagonal (fun i => P i i)).sub hP
  have hop : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (D-P)‖ ≤ (Fintype.card ι:ℝ)*e := by
    apply operator_le_entry_bound _ he
    intro i j
    by_cases hij : i=j
    · subst j
      simpa [D] using he
    · simpa [D,Matrix.diagonal_apply,hij] using hoff i j hij
  have ho := Matrix.le_iff.mp (KSJacobiTraceSqrt.le_scalar_of_operatorNorm (D-P) hsym hop)
  apply Matrix.le_iff.mpr
  have hsum := hd.add ho
  convert hsum using 1
  module

end MatrixSpencer.MSManuscriptEntryFloor
