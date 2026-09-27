import MatrixSpencer.MSManuscriptNumericalProvider

/-! Original-label bounds for the actual square numerical signing factories.
Each restricted offset contains only already frozen original contractions.
The invariant `norm offset + number of live labels` therefore does not grow
when a phase restricts again. These are parameter bounds, not a runtime theorem.
-/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.MSManuscriptOriginalOffsetBounds
open PhaseRestriction MSManuscriptMatrixReindex
local instance {m : Type*} [Fintype m] [DecidableEq m] :
    CStarAlgebra (Matrix m m ℂ) := {}
set_option maxHeartbeats 800000
section Generic
variable {ι n : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype n] [DecidableEq n]

/-- A frozen coordinate has absolute value exactly one, without any
reachability or additional cube hypothesis. -/
theorem frozen_abs (x : EuclideanSpace ℝ ι) {i : ι}
    (hi : i ∈ frozenCoordinates x) : |x i| = 1 := by
  rcases (mem_frozenCoordinates x i).mp hi with h | h <;> rw [h] <;> norm_num

/-- Every frozen atom costs at most one in the original operator norm. -/
theorem restrictedOffset_norm_le
    (offset : selfAdjoint (Matrix n n ℂ)) (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (hN : ∀ i, ‖A i‖ ≤ 1)
    (x : EuclideanSpace ℝ ι) :
    ‖restrictedOffset offset A hA x‖ ≤ ‖offset‖ + (frozenCoordinates x).card := by
  unfold restrictedOffset
  apply (norm_add_le _ _).trans
  apply add_le_add_left
  calc
    _ ≤ ∑ i ∈ frozenCoordinates x, ‖x i • hermitianMatrixFamily A hA i‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _i ∈ frozenCoordinates x, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_smul, Real.norm_eq_abs, frozen_abs x hi, one_mul]
      exact hN i
    _ = ((frozenCoordinates x).card : ℝ) := by simp

/-- The global original-label budget survives each restriction. In
particular it can be applied again at every inner or outer live phase. -/
theorem restrictedOffset_norm_add_live_le
    (offset : selfAdjoint (Matrix n n ℂ)) (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (hN : ∀ i, ‖A i‖ ≤ 1)
    (x : EuclideanSpace ℝ ι) :
    ‖restrictedOffset offset A hA x‖ + Fintype.card (Live x) ≤
      ‖offset‖ + Fintype.card ι := by
  have hb := restrictedOffset_norm_le offset A hA hN x
  have hc : (Fintype.card (Live x) : ℝ) + (frozenCoordinates x).card =
      Fintype.card ι := by exact_mod_cast live_card_add_frozen x
  linarith

/-- Restricting the live family cannot charge already frozen labels again. -/
theorem nestedOffset_norm_add_live_le
    (offset : selfAdjoint (Matrix n n ℂ)) (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (hN : ∀ i, ‖A i‖ ≤ 1)
    (x : EuclideanSpace ℝ ι) (y : EuclideanSpace ℝ (Live x)) :
    ‖restrictedOffset (restrictedOffset offset A hA x) (restrictedFamily A x)
      (restrictedFamily_hermitian A hA x) y‖ + Fintype.card (Live y) ≤
      ‖offset‖ + Fintype.card ι :=
  (restrictedOffset_norm_add_live_le _ _ _ (restrictedFamily_contractions A hN x) y).trans
    (restrictedOffset_norm_add_live_le offset A hA hN x)

/-- Physical coordinate reindexing preserves the same global budget. -/
theorem reindexed_restrictedOffset_norm_add_live_le {d : ℕ} (e : Fin d ≃ n)
    (offset : selfAdjoint (Matrix n n ℂ)) (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (hN : ∀ i, ‖A i‖ ≤ 1)
    (x : EuclideanSpace ℝ ι) (y : EuclideanSpace ℝ (Live x)) :
    ‖restrictedOffset (selfAdjointReindex e (restrictedOffset offset A hA x))
      (fun i : Live x => (A i).submatrix e e) (fun i => (hA i).submatrix e) y‖ +
      Fintype.card (Live y) ≤ ‖offset‖ + Fintype.card ι := by
  have hb := restrictedOffset_norm_add_live_le
    (selfAdjointReindex e (restrictedOffset offset A hA x))
    (fun i : Live x => (A i).submatrix e e) (fun i => (hA i).submatrix e)
    (fun i => reindex_contraction e (hN i)) y
  rw [selfAdjointReindex_norm] at hb
  exact hb.trans (restrictedOffset_norm_add_live_le offset A hA hN x)

end Generic
section Factory
variable {ι n : Type*} [Fintype ι] [LinearOrder ι]
  [Fintype n] [DecidableEq n] {d : ℕ} [Nonempty (Fin d)]

/-- This is the exact offset field of the numerical epoch config used by
`MSManuscriptNumericalProvider.provider.atPoint`: first restrict the original
labels at `x`, reindex the physical matrix, then restrict at the inner point
`y` and enumerate its live labels. The original offset is zero. -/
theorem factory_cfg_offset_add_live_le
    (e : Fin d ≃ n) (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (hN : ∀ i, ‖A i‖ ≤ 1)
    (x : EuclideanSpace ℝ ι) (ε : ℝ) (hε : 0 < ε)
    (hsmall : (Fintype.card (Live x) : ℝ) * ε ≤ 1 / 1000)
    (y : MSManuscriptPhase.Point (ι := Live x) ε)
    (hl : 32 ≤ Fintype.card (Live y.val)) :
    ‖(MSManuscriptNumericalEpochFactory.cfg
      (selfAdjointReindex e (restrictedOffset 0 A hA x))
      (fun i : Live x => (A i).submatrix e e) (fun i => (hA i).submatrix e)
      (fun i => reindex_contraction e (hN i)) ε hε hsmall y hl).offset‖ +
      Fintype.card (Live y.val) ≤ Fintype.card ι := by
  change ‖restrictedOffset (selfAdjointReindex e (restrictedOffset 0 A hA x))
    (fun i : Live x => (A i).submatrix e e) (fun i => (hA i).submatrix e) y.val‖ +
    Fintype.card (Live y.val) ≤ Fintype.card ι
  simpa only [norm_zero, zero_add] using
    reindexed_restrictedOffset_norm_add_live_le e 0 A hA hN x y.val

/-- The concrete original-label operator-norm budget is `B = card ι` at
every numerical epoch, including all nested live restrictions. -/
theorem factory_cfg_offset_norm_le
    (e : Fin d ≃ n) (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (hN : ∀ i, ‖A i‖ ≤ 1)
    (x : EuclideanSpace ℝ ι) (ε : ℝ) (hε : 0 < ε)
    (hsmall : (Fintype.card (Live x) : ℝ) * ε ≤ 1 / 1000)
    (y : MSManuscriptPhase.Point (ι := Live x) ε)
    (hl : 32 ≤ Fintype.card (Live y.val)) :
    ‖((MSManuscriptNumericalEpochFactory.cfg
      (selfAdjointReindex e (restrictedOffset 0 A hA x))
      (fun i : Live x => (A i).submatrix e e) (fun i => (hA i).submatrix e)
      (fun i => reindex_contraction e (hN i)) ε hε hsmall y hl).offset :
      Matrix (Fin d) (Fin d) ℂ)‖ ≤ Fintype.card ι := by
  have hb := factory_cfg_offset_add_live_le e A hA hN x ε hε hsmall y hl
  have hc : (0 : ℝ) ≤ Fintype.card (Live y.val) := Nat.cast_nonneg _
  exact (le_add_of_nonneg_right hc).trans hb

end Factory
end MatrixSpencer.MSManuscriptOriginalOffsetBounds
