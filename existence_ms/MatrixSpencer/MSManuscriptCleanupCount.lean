import MatrixSpencer.MSManuscriptCleanupFloor

/-! Exact deletion-count bookkeeping for the fixed-label cleanup scan. -/
open scoped BigOperators
noncomputable section
namespace MatrixSpencer.MSManuscriptCleanupCount
open MSManuscriptSchurCleanup MSManuscriptCleanupFloor
variable {d : ℕ}

theorem removedCount_eq_sum (G : Matrix (Fin d) (Fin d) ℝ) (δ : ℝ) (j : ℕ) :
    removedCount G δ j = ∑ a ∈ Finset.range j, if ha : a<d then
      (if G ⟨a,ha⟩ ⟨a,ha⟩ < 3*δ then 1 else 0) else 0 := by
  induction j with
  | zero => simp [removedCount]
  | succ j ih =>
    rw [removedCount,Finset.sum_range_succ,←ih]
    split_ifs <;> simp_all

theorem removedCount_eq_low_card (G : Matrix (Fin d) (Fin d) ℝ) (δ : ℝ) :
    removedCount G δ d = Fintype.card {a : Fin d // G a a < 3*δ} := by
  classical
  rw [removedCount_eq_sum]
  rw [← Finset.sum_fin_eq_sum_range (fun a : Fin d => if G a a < 3*δ then (1:ℕ) else 0)]
  rw [Fintype.card_subtype, Finset.card_filter]

theorem count_add_high (G : Matrix (Fin d) (Fin d) ℝ) (δ : ℝ) :
    removedCount G δ d + Fintype.card (High G δ) = d := by
  classical
  rw [removedCount_eq_low_card]
  have h := Fintype.card_subtype_compl (fun a : Fin d => G a a < 3*δ)
  simp only [not_lt, Fintype.card_fin] at h
  have hc := Fintype.card_subtype_le (fun a : Fin d => G a a < 3*δ)
  simp only [Fintype.card_fin] at hc
  change Fintype.card {a : Fin d // G a a < 3*δ} + Fintype.card {a : Fin d // 3*δ ≤ G a a} = d
  omega

end MatrixSpencer.MSManuscriptCleanupCount
