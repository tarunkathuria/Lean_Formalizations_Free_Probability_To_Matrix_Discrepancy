import MatrixSpencer.KSManuscriptScaleBounds
import MatrixSpencer.KSEighthInputTaylorBound
import MatrixSpencer.KSJointBoundParameters

/-!
# Polynomial bounds for the actual KS input-entry budgets

Rank-one Frobenius energy equals the squared operator norm. The actual
signed, doubled and Pauli lifts have twice that energy; a single independent
sign block has the original energy. Parseval therefore bounds the exact
arithmetic matrix budgets independently of the smallest nonzero vector or
source eigenvalue. These bounds concern input parameters, not whole-walk cost.
-/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSManuscriptInputBudgetBounds
open KSOwnerInputBounds
set_option maxHeartbeats 1200000
variable {n : Type*} [Fintype n] [DecidableEq n]

lemma energy_fromBlocks (A B C D : Matrix n n ℂ) :
    matrixEnergy (Matrix.fromBlocks A B C D) =
      matrixEnergy A + matrixEnergy B + matrixEnergy C + matrixEnergy D := by
  simp only [matrixEnergy, Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Finset.sum_add_distrib]
  ring

lemma energy_zero : matrixEnergy (0 : Matrix n n ℂ) = 0 := by
  simp [matrixEnergy]

lemma energy_neg (A : Matrix n n ℂ) : matrixEnergy (-A) = matrixEnergy A := by
  simp [matrixEnergy]

lemma energy_I_smul (A : Matrix n n ℂ) : matrixEnergy (Complex.I • A) = matrixEnergy A := by
  simp only [matrixEnergy_eq_entryEnergy, entryEnergy, Matrix.smul_apply, smul_eq_mul,
    Complex.normSq_mul, Complex.normSq_I, one_mul]

lemma energy_atom (v : n → ℂ) : matrixEnergy (KSRankOne.atom v) = ‖KSRankOne.atom v‖^2 := by
  rw [matrixEnergy_eq_trace_square _ (KSRankOne.atom_isHermitian v),
    KSRankOne.atom_sq_real, realTrace_smul, KSRankOne.atom_norm]
  ring

lemma energy_doubled (A : Matrix n n ℂ) : matrixEnergy (KSSpinSource.doubled A) = 2*matrixEnergy A := by
  rw [KSSpinSource.doubled, energy_fromBlocks, energy_zero]
  ring

lemma energy_signedLift (A : Matrix n n ℂ) : matrixEnergy (signedLift A) = 2*matrixEnergy A := by
  rw [signedLift, energy_fromBlocks, energy_zero, energy_neg]
  ring

lemma energy_pauli (A : Matrix n n ℂ) (b : Fin 4) :
    matrixEnergy (KSSpinSource.pauli A b) = 2*matrixEnergy A := by
  fin_cases b
  · exact energy_doubled A
  · simp only [KSSpinSource.pauli, energy_fromBlocks, energy_zero]
    ring
  · simp only [KSSpinSource.pauli, energy_fromBlocks, energy_zero, neg_smul,
      energy_neg, energy_I_smul]
    ring
  · exact energy_signedLift A

lemma energy_leftDensity (A : Matrix n n ℂ) : matrixEnergy (leftDensity A) = matrixEnergy A := by
  simp only [leftDensity, energy_fromBlocks, energy_zero, add_zero]

lemma energy_rightDensity (A : Matrix n n ℂ) : matrixEnergy (rightDensity A) = matrixEnergy A := by
  simp only [rightDensity, energy_fromBlocks, energy_zero, zero_add]

lemma bound_le_two_of_energy_le_one {A : Matrix n n ℂ} (h : matrixEnergy A ≤ 1) :
    matrixBound A ≤ 2 := by
  have hs : Real.sqrt (matrixEnergy A) ≤ 1 := by simpa using Real.sqrt_le_sqrt h
  unfold matrixBound
  linarith

lemma bound_le_three_of_energy_le_two {A : Matrix n n ℂ} (h : matrixEnergy A ≤ 2) :
    matrixBound A ≤ 3 := by
  have hs := Real.sq_sqrt (matrixEnergy_nonneg A)
  have hn := Real.sqrt_nonneg (matrixEnergy A)
  unfold matrixBound
  nlinarith

variable {N d : ℕ}

lemma atom_norm_le_one (v : Fin N → Fin d → ℂ)
    (hp : (∑i,KSRankOne.atom (v i))=1) (i : Fin N) : ‖KSRankOne.atom (v i)‖≤1 := by
  letI : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
  have hle : KSRankOne.atom (v i) ≤ 1 := by
    rw [← hp]
    exact Finset.single_le_sum (fun j _ => (KSRankOne.atom_posSemidef (v j)).nonneg)
      (Finset.mem_univ i)
  apply (CStarAlgebra.norm_le_iff_le_algebraMap _ zero_le_one
    (KSRankOne.atom_posSemidef (v i)).nonneg).mpr
  simpa using hle

lemma atom_energy_le_one (v : Fin N → Fin d → ℂ)
    (hp : (∑i,KSRankOne.atom (v i))=1) (i : Fin N) : matrixEnergy (KSRankOne.atom (v i))≤1 := by
  rw [energy_atom]
  exact (pow_le_pow_left₀ (norm_nonneg _) (atom_norm_le_one v hp i) 2).trans_eq (by norm_num)

lemma atom_bound_le_two (v : Fin N → Fin d → ℂ)
    (hp : (∑i,KSRankOne.atom (v i))=1) (i : Fin N) : matrixBound (KSRankOne.atom (v i))≤2 :=
  bound_le_two_of_energy_le_one (atom_energy_le_one v hp i)

lemma signed_bound_le_three (v : Fin N → Fin d → ℂ)
    (hp : (∑i,KSRankOne.atom (v i))=1) (i : Fin N) :
    matrixBound (signedLift (KSRankOne.atom (v i)))≤3 := by
  apply bound_le_three_of_energy_le_two
  rw [energy_signedLift]
  linarith [atom_energy_le_one v hp i]

lemma doubled_bound_le_three (v : Fin N → Fin d → ℂ)
    (hp : (∑i,KSRankOne.atom (v i))=1) (i : Fin N) :
    matrixBound (KSSpinSource.doubled (KSRankOne.atom (v i)))≤3 := by
  apply bound_le_three_of_energy_le_two
  rw [energy_doubled]
  linarith [atom_energy_le_one v hp i]

lemma pauli_bound_le_three (v : Fin N → Fin d → ℂ)
    (hp : (∑i,KSRankOne.atom (v i))=1) (j : Fin N × Fin 4) :
    matrixBound (KSSpinSource.family (fun i => KSRankOne.atom (v i)) j)≤3 := by
  apply bound_le_three_of_energy_le_two
  rw [KSSpinSource.family, energy_pauli]
  linarith [atom_energy_le_one v hp j.1]

lemma independent_bound_le_two (v : Fin N → Fin d → ℂ)
    (hp : (∑i,KSRankOne.atom (v i))=1) (j : Fin N × Bool) :
    matrixBound (KSEighthActualState.family v j)≤2 := by
  apply bound_le_two_of_energy_le_one
  rcases j with ⟨i,b⟩
  cases b <;> simpa only [KSEighthActualState.family, KSIndependentSource.family,
    Bool.false_eq_true, if_false, if_true, energy_leftDensity, energy_rightDensity] using
      atom_energy_le_one v hp i

/-- The exact physical-atom entry budget is linear in the label count. -/
theorem atomBudget_le (v : Fin N → Fin d → ℂ) (hp : (∑i,KSRankOne.atom (v i))=1) :
    KSDebitUniformFloor.atomBudget v ≤ 1+2*(N:ℝ) := by
  unfold KSDebitUniformFloor.atomBudget
  apply add_le_add_left
  calc _ ≤ ∑ _i : Fin N, (2:ℝ) := Finset.sum_le_sum fun i _ => atom_bound_le_two v hp i
    _ = _ := by simp; ring

theorem slopeBudget_le (v : Fin N → Fin d → ℂ) (hp : (∑i,KSRankOne.atom (v i))=1) :
    KSComplexPolynomialBounds.slopeBudget v ≤ 1+3*(N:ℝ) := by
  unfold KSComplexPolynomialBounds.slopeBudget
  apply add_le_add_left
  calc _ ≤ ∑ _i : Fin N, (3:ℝ) := Finset.sum_le_sum fun i _ => signed_bound_le_three v hp i
    _ = _ := by simp; ring

theorem spinBudget_le (v : Fin N → Fin d → ℂ) (hp : (∑i,KSRankOne.atom (v i))=1) :
    KSDebitUniformFloor.spinBudget v ≤ 1+1152*(N:ℝ) := by
  have hs : (∑j : Fin N × Fin 4, matrixBound (KSSpinSource.family
      (fun i => KSRankOne.atom (v i)) j)^2) ≤ 36*(N:ℝ) := by
    calc _ ≤ ∑ _j : Fin N × Fin 4, (9:ℝ) := by
          apply Finset.sum_le_sum
          intro j _
          have hb := pauli_bound_le_three v hp j
          have hn := (matrixBound_pos (KSSpinSource.family (fun i => KSRankOne.atom (v i)) j)).le
          nlinarith
      _ = _ := by simp; ring
  unfold KSDebitUniformFloor.spinBudget
  linarith

/-- The full-cube polynomial source budget, before any retained-face restriction. -/
theorem sourceBudget_le (v : Fin N → Fin d → ℂ) (hp : (∑i,KSRankOne.atom (v i))=1) :
    KSComplexPolynomialBounds.sourceBudget v ≤ 1+23040*(d:ℝ)*N := by
  have hs : (∑i : Fin N, matrixBound (KSComplexSpinSource.atom v i)^2) ≤ 9*(N:ℝ) := by
    calc _ ≤ ∑ _i : Fin N, (9:ℝ) := by
          apply Finset.sum_le_sum
          intro i _
          have hb := doubled_bound_le_three v hp i
          have hn := (matrixBound_pos (KSComplexSpinSource.atom v i)).le
          change matrixBound (KSComplexSpinSource.atom v i) ≤ 3 at hb
          nlinarith
      _ = _ := by simp; ring
  unfold KSComplexPolynomialBounds.sourceBudget
  calc _ ≤ 1+1280*(Fintype.card (Fin d ⊕ Fin d):ℝ)*(9*N) := by gcongr
    _ = _ := by simp only [Fintype.card_sum,Fintype.card_fin,Nat.cast_add]; ring

/-- The two independent sign-block source uses twice as many labels, each
with its original rank-one Frobenius energy. -/
theorem eighth_sourceCap_le (v : Fin N → Fin d → ℂ) (hp : (∑i,KSRankOne.atom (v i))=1) :
    KSEighthInputTaylorBound.sourceCap v ≤ 1+20480*(d:ℝ)*N := by
  have hs : (∑j : Fin N × Bool, matrixBound (KSEighthActualState.family v j)^2) ≤ 8*(N:ℝ) := by
    calc _ ≤ ∑ _j : Fin N × Bool, (4:ℝ) := by
          apply Finset.sum_le_sum
          intro j _
          have hb := independent_bound_le_two v hp j
          have hn := (matrixBound_pos (KSEighthActualState.family v j)).le
          nlinarith
      _ = _ := by simp; ring
  unfold KSEighthInputTaylorBound.sourceCap KSComplexTraceBounds.sourceBudget
  calc _ ≤ 1+1280*(Fintype.card (Fin d ⊕ Fin d):ℝ)*(8*N) := by gcongr
    _ = _ := by simp only [Fintype.card_sum,Fintype.card_fin,Nat.cast_add]; ring

theorem eighth_centerCap_le (v : Fin N → Fin d → ℂ) (hp : (∑i,KSRankOne.atom (v i))=1) :
    KSEighthInputTaylorBound.centerCap v ≤ 3+9*(N:ℝ) := by
  have h := slopeBudget_le v hp
  change 3*KSComplexPolynomialBounds.slopeBudget v ≤ _
  linarith

theorem eighth_directionCap_le (v : Fin N → Fin d → ℂ) (hp : (∑i,KSRankOne.atom (v i))=1) :
    KSEighthInputTaylorBound.directionCap v ≤ 2+6*(N:ℝ) := by
  have h := slopeBudget_le v hp
  change 2*KSComplexPolynomialBounds.slopeBudget v ≤ _
  linarith

theorem centerRadius_le (v : Fin N → Fin d → ℂ) (hp : (∑i,KSRankOne.atom (v i))=1)
    {δ η : ℝ} (hδ : δ≤1) (hη : (N:ℝ)*η≤1) :
    KSDebitUniformFloor.centerRadius v δ η ≤ 4+4*(N:ℝ) := by
  have hmul := mul_le_mul_of_nonneg_right hδ (KSDebitUniformFloor.atomBudget_pos v).le
  have hA := atomBudget_le v hp
  unfold KSDebitUniformFloor.centerRadius KSDebitUniformFloor.debitBound
  nlinarith

theorem full_centerCap_le (v : Fin N → Fin d → ℂ) (hp : (∑i,KSRankOne.atom (v i))=1)
    {δ η : ℝ} (hδ : δ≤1) (hη : (N:ℝ)*η≤1) :
    KSJointBoundParameters.centerCap v δ η ≤ 6+10*(N:ℝ) := by
  have hR := centerRadius_le v hp hδ hη
  have hS := slopeBudget_le v hp
  unfold KSJointBoundParameters.centerCap
  linarith

/-- The exact full-cube radius at the actual original-input scales. -/
theorem actual_centerRadius_le (v : Fin N → Fin d → ℂ) (hd : 0<d)
    (hp : (∑i,KSRankOne.atom (v i))=1) :
    KSDebitUniformFloor.centerRadius v (Real.sqrt (KSEighthManuscriptPreprocess.epsilon v))
      (Real.sqrt (KSEighthManuscriptPreprocess.epsilon v)/(N:ℝ)) ≤ 4+4*(N:ℝ) := by
  have hδ : Real.sqrt (KSEighthManuscriptPreprocess.epsilon v) ≤ 1 := by
    simpa using Real.sqrt_le_sqrt (KSEighthManuscriptPreprocess.epsilon_le_one v hd hp)
  have hN : (N:ℝ)≠0 := by
    have h := (KSEighthManuscriptPreprocess.count_pos v hd hp).trans_le
      (KSEighthManuscriptPreprocess.count_le v)
    exact_mod_cast h.ne'
  apply centerRadius_le v hp hδ
  simpa only [mul_div_cancel₀ _ hN] using hδ

/-- Actual preprocessing and the exact debit formula discharge the scalar
premises of the full-cube center budget. -/
theorem actual_full_centerCap_le (v : Fin N → Fin d → ℂ) (hd : 0<d)
    (hp : (∑i,KSRankOne.atom (v i))=1) :
    KSJointBoundParameters.centerCap v (Real.sqrt (KSEighthManuscriptPreprocess.epsilon v))
      (Real.sqrt (KSEighthManuscriptPreprocess.epsilon v)/(N:ℝ)) ≤ 6+10*(N:ℝ) := by
  have hδ : Real.sqrt (KSEighthManuscriptPreprocess.epsilon v) ≤ 1 := by
    simpa using Real.sqrt_le_sqrt (KSEighthManuscriptPreprocess.epsilon_le_one v hd hp)
  have hN : (N:ℝ)≠0 := by
    have h := (KSEighthManuscriptPreprocess.count_pos v hd hp).trans_le
      (KSEighthManuscriptPreprocess.count_le v)
    exact_mod_cast h.ne'
  apply full_centerCap_le v hp hδ
  simpa only [mul_div_cancel₀ _ hN] using hδ

end MatrixSpencer.KSManuscriptInputBudgetBounds
