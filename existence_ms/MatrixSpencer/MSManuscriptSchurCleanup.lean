import MatrixSpencer.MSManuscriptSchurEstimates
import MatrixSpencer.MSManuscriptCleanupParameters

/-! A finite scan of scalar Schur deletions in a Jacobi coordinate system.
The low-coordinate set is fixed from the input diagonal. This is a real-RAM
implementation variant; it does not implement rational Householder cleanup. -/
open Matrix
open scoped BigOperators MatrixOrder
noncomputable section
namespace MatrixSpencer.MSManuscriptSchurCleanup
open KSEighthManuscriptLDL MSManuscriptSchurEstimates MSManuscriptCleanupParameters
set_option maxHeartbeats 1500000
variable {d : ℕ}

def Removed (G : Matrix (Fin d) (Fin d) ℝ) (δ : ℝ) (j : ℕ) (a : Fin d) : Prop :=
  a.val < j ∧ G a a < 3*δ

def runScan (G : Matrix (Fin d) (Fin d) ℝ) (δ : ℝ) : ℕ → Matrix (Fin d) (Fin d) ℝ
  | 0 => G
  | j+1 => if hj : j<d then
      if G ⟨j,hj⟩ ⟨j,hj⟩ < 3*δ then schur (runScan G δ j) ⟨j,hj⟩ else runScan G δ j
    else runScan G δ j

def removedCount (G : Matrix (Fin d) (Fin d) ℝ) (δ : ℝ) : ℕ → ℕ
  | 0 => 0
  | j+1 => if hj : j<d then
      if G ⟨j,hj⟩ ⟨j,hj⟩ < 3*δ then removedCount G δ j+1 else removedCount G δ j
    else removedCount G δ j

theorem runScan_posSemidef (G : Matrix (Fin d) (Fin d) ℝ) (hG : G.PosSemidef)
    (δ : ℝ) (j : ℕ) : (runScan G δ j).PosSemidef := by
  induction j with
  | zero => exact hG
  | succ j ih =>
    unfold runScan
    split_ifs <;> first | exact schur_posSemidef ih _ | exact ih

theorem runScan_le (G : Matrix (Fin d) (Fin d) ℝ) (hG : G.PosSemidef)
    (δ : ℝ) (j : ℕ) : runScan G δ j ≤ G := by
  induction j with
  | zero => exact le_rfl
  | succ j ih =>
    unfold runScan
    split_ifs <;> first | exact (schur_le (runScan_posSemidef G hG δ j) _).trans ih | exact ih

theorem runScan_zero_column (G : Matrix (Fin d) (Fin d) ℝ) (hG : G.PosSemidef)
    (δ : ℝ) (j : ℕ) (a : Fin d) (ha : Removed G δ j a) : column (runScan G δ j) a = 0 := by
  induction j with
  | zero => exact False.elim (Nat.not_lt_zero _ ha.1)
  | succ j ih =>
    by_cases haj : a.val<j
    · have hz := ih ⟨haj,ha.2⟩
      unfold runScan
      split_ifs
      · exact schur_preserves_zero_column (runScan_posSemidef G hG δ j).isHermitian hz _
      · exact hz
      · exact hz
    · have he : a.val=j := by have := ha.1; omega
      have hj : j<d := by rw [←he]; exact a.isLt
      have hai : a=⟨j,hj⟩ := Fin.ext he
      subst a
      simp only [runScan, dif_pos hj, if_pos ha.2]
      exact schur_column_zero (runScan_posSemidef G hG δ j) _

private theorem diagonal_le {P G : Matrix (Fin d) (Fin d) ℝ} (hle : P ≤ G) (a : Fin d) : P a a ≤ G a a := by
  have h := diagonal_nonneg (Matrix.le_iff.mp hle) a
  simpa only [Matrix.sub_apply, sub_nonneg] using h

structure Bounds (G : Matrix (Fin d) (Fin d) ℝ) (δ : ℝ) (j : ℕ) : Prop where
  diagonal : ∀ a, ¬Removed G δ j a → G a a-(j:ℝ)*entryLoss d δ ≤ runScan G δ j a a
  offDiagonal : ∀ a b, a ≠ b → |runScan G δ j a b| ≤ tolerance d δ+(j:ℝ)*entryLoss d δ
  trace : realTrace G-realTrace (runScan G δ j) ≤ 4*δ*(removedCount G δ j:ℝ)

/-- The fixed residual keeps all surviving pivots positive during the entire scan. -/
theorem runScan_bounds (G : Matrix (Fin d) (Fin d) ℝ) (hG : G.PosSemidef)
    {δ : ℝ} (hδ : 0 < δ) (hdiag : ∀ a, δ ≤ G a a)
    (hoff : ∀ a b, a ≠ b → |G a b| ≤ tolerance d δ) (j : ℕ) (hj : j ≤ d) :
    Bounds G δ j := by
  induction j with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · intro a _; simp [runScan]
    · intro a b hab; simpa [runScan] using hoff a b hab
    · simp [runScan, removedCount]
  | succ j ih =>
    have hjd : j<d := by omega
    have hprev := ih (by omega)
    let i : Fin d := ⟨j,hjd⟩
    have hη : 0 < tolerance d δ := tolerance_pos d hδ
    have hl : 0 ≤ entryLoss d δ := entryLoss_nonneg d hδ
    have hjloss : (j:ℝ)*entryLoss d δ ≤ (d:ℝ)*entryLoss d δ :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast (show j≤d by omega)) hl
    have htot := total_entryLoss_le d hδ
    have hηδ := tolerance_le d hδ
    have hnoti : ¬Removed G δ j i := by intro hi; exact Nat.lt_irrefl j hi.1
    have hpiv : δ/2 ≤ runScan G δ j i i := by
      have h := hprev.diagonal i hnoti
      have hd := hdiag i
      linarith
    have hpivpos : 0 < runScan G δ j i i := lt_of_lt_of_le (by positivity) hpiv
    have holdoff : ∀ a b, a≠b → |runScan G δ j a b| ≤ 2*tolerance d δ := by
      intro a b hab
      have h := hprev.offDiagonal a b hab
      linarith
    by_cases hi : G i i < 3*δ
    · have hstep : runScan G δ (j+1) = schur (runScan G δ j) i := by simp only [runScan, dif_pos hjd]; exact if_pos hi
      have hcount : removedCount G δ (j+1) = removedCount G δ j+1 := by simp only [removedCount, dif_pos hjd]; exact if_pos hi
      have hpert (a b : Fin d) (hai : a≠i) (hbi : b≠i) :
          |schur (runScan G δ j) i a b-runScan G δ j a b| ≤ entryLoss d δ := by
        have h := schur_perturbation_bound (runScan G δ j) i a b (show 0<δ/2 by positivity)
          (show 0≤2*tolerance d δ by positivity) hpiv (holdoff a i hai) (holdoff b i hbi)
        convert h using 1
        dsimp [entryLoss]
        ring
      refine ⟨?_, ?_, ?_⟩
      · intro a ha
        have hai : a≠i := by intro h; subst a; exact ha ⟨by dsimp [i]; omega,hi⟩
        have hna : ¬Removed G δ j a := fun h => ha ⟨Nat.lt_succ_of_lt h.1,h.2⟩
        have hprevA := hprev.diagonal a hna
        have habs := (abs_le.mp (hpert a a hai hai)).1
        rw [hstep]
        push_cast
        linarith
      · intro a b hab
        by_cases hbi : b=i
        · subst b
          have hz := schur_column_zero (runScan_posSemidef G hG δ j) i
          have hzero := congrFun hz a
          change schur (runScan G δ j) i a i = 0 at hzero
          rw [hstep,hzero,abs_zero]
          positivity
        · by_cases hai : a=i
          · subst a
            have hz := schur_column_zero (runScan_posSemidef G hG δ j) i
            have hzero := congrFun hz b
            have hs := (schur_posSemidef (runScan_posSemidef G hG δ j) i).isHermitian.eq
            have he : schur (runScan G δ j) i i b = schur (runScan G δ j) i b i := by
              simpa using congrFun (congrFun hs b) i
            rw [hstep,he]
            change |column (schur (runScan G δ j) i) i b| ≤ _
            rw [hz]
            simp only [Pi.zero_apply,abs_zero]
            positivity
          · have he := abs_add_le (schur (runScan G δ j) i a b-runScan G δ j a b) (runScan G δ j a b)
            have hp := hpert a b hai hbi
            have ho := hprev.offDiagonal a b hab
            rw [hstep]
            push_cast
            have heq : schur (runScan G δ j) i a b-runScan G δ j a b+runScan G δ j a b = schur (runScan G δ j) i a b := by ring
            rw [heq] at he
            linarith
      · have ht := schur_trace_loss_le (runScan G δ j) i (show 0<δ/2 by positivity)
          (show 0≤2*tolerance d δ by positivity) hpiv (fun a ha => holdoff a i ha)
        have hup := diagonal_le (runScan_le G hG δ j) i
        have he : (2*tolerance d δ)^2/(δ/2)=entryLoss d δ := by unfold entryLoss; ring
        rw [he] at ht
        simp only [Fintype.card_fin] at ht
        have htrace := hprev.trace
        rw [hstep,hcount]
        push_cast
        linarith
    · have hstep : runScan G δ (j+1) = runScan G δ j := by simp only [runScan, dif_pos hjd]; exact if_neg hi
      have hcount : removedCount G δ (j+1) = removedCount G δ j := by simp only [removedCount, dif_pos hjd]; exact if_neg hi
      refine ⟨?_, ?_, ?_⟩
      · intro a ha
        have hna : ¬Removed G δ j a := fun h => ha ⟨Nat.lt_succ_of_lt h.1,h.2⟩
        have h := hprev.diagonal a hna
        rw [hstep]
        push_cast
        linarith
      · intro a b hab
        have h := hprev.offDiagonal a b hab
        rw [hstep]
        push_cast
        linarith
      · simpa only [hstep,hcount] using hprev.trace

end MatrixSpencer.MSManuscriptSchurCleanup
