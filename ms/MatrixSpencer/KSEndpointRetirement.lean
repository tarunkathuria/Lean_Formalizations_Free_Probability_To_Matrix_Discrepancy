import MatrixSpencer.KSOwnerRetirement
import MatrixSpencer.KSIndependentSource

/-! Exact transport-probe endpoint tests for the two KS source families. -/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

noncomputable section
namespace MatrixSpencer.KSEndpointRetirement

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n]

open KSOwnerRetirement KSRankOne

theorem weighted_sum_delete {E : Type*} [AddCommGroup E] [Module ℝ E]
    (c : ι → ℝ) (f : ι → E) (i : ι) :
    (∑ j, Function.update c i 0 j • f j) = (∑ j, c j • f j) - c i • f i := by
  apply eq_sub_iff_add_eq.mpr
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  simp only [Function.update_self, zero_smul, add_zero]
  calc
    (∑ j ∈ Finset.univ.erase i, Function.update c i 0 j • f j) + c i • f i =
        (∑ j ∈ Finset.univ.erase i, c j • f j) + c i • f i := by
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
    _ = _ := Finset.sum_erase_add _ _ (Finset.mem_univ i)

theorem leftDensity_atom (v : n → ℂ) :
    leftDensity (atom v) = atom (Sum.elim v (fun _ : n => (0 : ℂ))) := by
  ext i j
  cases i <;> cases j <;> simp [leftDensity, atom, Matrix.fromBlocks,
    Matrix.vecMulVec_apply, Pi.star_apply]

theorem rightDensity_atom (v : n → ℂ) :
    rightDensity (atom v) = atom (Sum.elim (fun _ : n => (0 : ℂ)) v) := by
  ext i j
  cases i <;> cases j <;> simp [rightDensity, atom, Matrix.fromBlocks,
    Matrix.vecMulVec_apply, Pi.star_apply]

theorem left_sandwich (v : n → ℂ) {W : Matrix (n ⊕ n) (n ⊕ n) ℂ}
    (hW : W.IsHermitian) :
    leftDensity (atom v) * W * leftDensity (atom v) =
      realTrace (leftDensity (atom v) * W) • leftDensity (atom v) := by
  rw [leftDensity_atom]
  exact atom_sandwich_real _ hW

theorem right_sandwich (v : n → ℂ) {W : Matrix (n ⊕ n) (n ⊕ n) ℂ}
    (hW : W.IsHermitian) :
    rightDensity (atom v) * W * rightDensity (atom v) =
      realTrace (rightDensity (atom v) * W) • rightDensity (atom v) := by
  rw [rightDensity_atom]
  exact atom_sandwich_real _ hW

theorem independent_source_delete (v : ι → n → ℂ) (c : ι → ℝ) (i : ι)
    {W : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hW : W.IsHermitian) :
    covarianceSource (KSIndependentSource.family (fun j => atom (v j)))
      (KSIndependentSource.coefficientCovariance (Function.update c i 0)) W =
    covarianceSource (KSIndependentSource.family (fun j => atom (v j)))
      (KSIndependentSource.coefficientCovariance c) W -
      c i • (realTrace (rightDensity (atom (v i)) * W) • rightDensity (atom (v i)) +
        realTrace (leftDensity (atom (v i)) * W) • leftDensity (atom (v i))) := by
  rw [KSIndependentSource.source_eq_sum, KSIndependentSource.source_eq_sum,
    weighted_sum_delete, left_sandwich _ hW, right_sandwich _ hW]

theorem spin_source_delete (v : ι → n → ℂ) (c : ι → ℝ) (i : ι)
    {W : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hW : W.IsHermitian) :
    covarianceSource (KSSpinSource.family (fun j => atom (v j)))
      (KSSpinSource.coefficientCovariance (Function.update c i 0)) W =
    covarianceSource (KSSpinSource.family (fun j => atom (v j)))
      (KSSpinSource.coefficientCovariance c) W -
      (c i * realTrace (KSSpinSource.doubled (atom (v i)) * W)) •
        KSSpinSource.doubled (atom (v i)) := by
  rw [KSSpinSource.source_eq_tracePrepare_real v _ hW,
    KSSpinSource.source_eq_tracePrepare_real v _ hW]
  simpa only [smul_smul] using weighted_sum_delete c
    (fun j => realTrace (KSSpinSource.doubled (atom (v j)) * W) •
      KSSpinSource.doubled (atom (v j))) i

theorem independent_covariance_delete_le (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i) (i : ι) :
    KSIndependentSource.coefficientCovariance (Function.update c i 0) ≤
      KSIndependentSource.coefficientCovariance c := by
  apply Matrix.le_iff.mpr
  rw [KSIndependentSource.coefficientCovariance, KSIndependentSource.coefficientCovariance,
    Matrix.diagonal_sub]
  apply Matrix.posSemidef_diagonal_iff.mpr
  intro j
  by_cases hj : j.1 = i
  · change 0 ≤ c j.1 - Function.update c i 0 j.1
    rw [hj, Function.update_self, sub_zero]
    exact hc i
  · simp [Function.update_of_ne hj]

theorem spin_covariance_delete_le (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i) (i : ι) :
    KSSpinSource.coefficientCovariance (Function.update c i 0) ≤
      KSSpinSource.coefficientCovariance c := by
  apply Matrix.le_iff.mpr
  rw [KSSpinSource.coefficientCovariance, KSSpinSource.coefficientCovariance,
    Matrix.diagonal_sub]
  apply Matrix.posSemidef_diagonal_iff.mpr
  intro j
  by_cases hj : j.1 = i
  · change 0 ≤ c j.1 / 2 - Function.update c i 0 j.1 / 2
    rw [hj, Function.update_self, zero_div, sub_zero]
    exact div_nonneg (hc i) (by norm_num)
  · simp [Function.update_of_ne hj]

/-- A signed center displacement is dominated by the removed independent
sign-block source exactly when the two scalar coefficients are dominated. -/
theorem independent_step_le {A : Matrix n n ℂ} (hA : A.PosSemidef)
    {δ p q : ℝ} (hp : δ ≤ p) (hq : -δ ≤ q) :
    δ • signedLift A ≤ q • rightDensity A + p • leftDensity A := by
  have hl : δ • A ≤ p • A := smul_le_smul_of_nonneg_right hp hA.nonneg
  have hr : (-δ) • A ≤ q • A := smul_le_smul_of_nonneg_right hq hA.nonneg
  convert fromBlocks_diagonal_mono hl hr using 1 <;>
    simp [signedLift, leftDensity, rightDensity, Matrix.fromBlocks_smul,
      Matrix.fromBlocks_add, smul_neg, neg_smul]

theorem spin_step_le {A : Matrix n n ℂ} (hA : A.PosSemidef)
    {δ r : ℝ} (hr : |δ| ≤ r) : δ • signedLift A ≤ r • KSSpinSource.doubled A := by
  have hp : δ ≤ r := (le_abs_self δ).trans hr
  have hn : -δ ≤ r := (neg_le_abs δ).trans hr
  have hl : δ • A ≤ r • A := smul_le_smul_of_nonneg_right hp hA.nonneg
  have hright : (-δ) • A ≤ r • A := smul_le_smul_of_nonneg_right hn hA.nonneg
  convert fromBlocks_diagonal_mono hl hright using 1 <;>
    simp [signedLift, KSSpinSource.doubled, Matrix.fromBlocks_smul, smul_neg, neg_smul]

def independentTransport [Nonempty n] (H : Matrix (n ⊕ n) (n ⊕ n) ℂ)
    (v : ι → n → ℂ) (c : ι → ℝ) (θ : ℝ) :=
  transportMatrix H (KSIndependentSource.family (fun j => atom (v j)))
    (KSIndependentSource.coefficientCovariance c) θ

def spinTransport [Nonempty n] (H : Matrix (n ⊕ n) (n ⊕ n) ℂ)
    (v : ι → n → ℂ) (c : ι → ℝ) (θ : ℝ) :=
  transportMatrix H (KSSpinSource.family (fun j => atom (v j)))
    (KSSpinSource.coefficientCovariance c) θ

theorem update_zero_nonneg {c : ι → ℝ} (hc : ∀ j, 0 ≤ c j) (i : ι) :
    ∀ j, 0 ≤ Function.update c i 0 j := by
  intro j
  by_cases hj : j = i
  · rw [hj, Function.update_self]
  · simpa [Function.update_of_ne hj] using hc j

theorem independent_retire [Nonempty n] (H : Matrix (n ⊕ n) (n ⊕ n) ℂ)
    (v : ι → n → ℂ) (c : ι → ℝ) (hc : ∀ j, 0 ≤ c j)
    {θ : ℝ} (hθ : 0 < θ) (i : ι) (δ : ℝ)
    (hp : δ ≤ c i * realTrace (leftDensity (atom (v i)) * independentTransport H v c θ))
    (hq : -δ ≤ c i * realTrace (rightDensity (atom (v i)) * independentTransport H v c θ)) :
    ownerPotential (H + δ • signedLift (atom (v i)))
      (KSIndependentSource.family (fun j => atom (v j)))
      (KSIndependentSource.coefficientCovariance (Function.update c i 0)) θ ≤
    ownerPotential H (KSIndependentSource.family (fun j => atom (v j)))
      (KSIndependentSource.coefficientCovariance c) θ := by
  apply owner_retire_of_matrix_le H _ _
    (KSIndependentSource.family_isHermitian _ (fun j => atom_isHermitian _))
    (KSIndependentSource.coefficientCovariance_posSemidef hc)
    (KSIndependentSource.coefficientCovariance_posSemidef (update_zero_nonneg hc i))
    (independent_covariance_delete_le c hc i) hθ
  have hW := transportMatrix_posSemidef H
    (KSIndependentSource.family (fun j => atom (v j)))
    (KSIndependentSource.coefficientCovariance c) hθ
  rw [independent_source_delete v c i hW.isHermitian]
  have hstep := independent_step_le (atom_posSemidef (v i)) hp hq
  have hstep' : δ • signedLift (atom (v i)) ≤
      c i • (realTrace (rightDensity (atom (v i)) * independentTransport H v c θ) •
        rightDensity (atom (v i)) +
        realTrace (leftDensity (atom (v i)) * independentTransport H v c θ) •
          leftDensity (atom (v i))) := by
    simpa only [smul_add, smul_smul] using hstep
  have hzero := sub_nonpos.mpr hstep'
  have hsum := add_le_add_left hzero
    (H + covarianceSource (KSIndependentSource.family (fun j => atom (v j)))
      (KSIndependentSource.coefficientCovariance c) (independentTransport H v c θ))
  simp only [add_zero] at hsum
  convert hsum using 1 <;> dsimp only [independentTransport] <;> abel

theorem spin_retire [Nonempty n] (H : Matrix (n ⊕ n) (n ⊕ n) ℂ)
    (v : ι → n → ℂ) (c : ι → ℝ) (hc : ∀ j, 0 ≤ c j)
    {θ : ℝ} (hθ : 0 < θ) (i : ι) (δ : ℝ)
    (hq : |δ| ≤ c i * realTrace (KSSpinSource.doubled (atom (v i)) * spinTransport H v c θ)) :
    ownerPotential (H + δ • signedLift (atom (v i)))
      (KSSpinSource.family (fun j => atom (v j)))
      (KSSpinSource.coefficientCovariance (Function.update c i 0)) θ ≤
    ownerPotential H (KSSpinSource.family (fun j => atom (v j)))
      (KSSpinSource.coefficientCovariance c) θ := by
  apply owner_retire_of_matrix_le H _ _
    (KSSpinSource.family_isHermitian _ (fun j => atom_isHermitian _))
    (KSSpinSource.coefficientCovariance_posSemidef hc)
    (KSSpinSource.coefficientCovariance_posSemidef (update_zero_nonneg hc i))
    (spin_covariance_delete_le c hc i) hθ
  have hW := transportMatrix_posSemidef H
    (KSSpinSource.family (fun j => atom (v j)))
    (KSSpinSource.coefficientCovariance c) hθ
  rw [spin_source_delete v c i hW.isHermitian]
  have hstep := spin_step_le (atom_posSemidef (v i)) hq
  have hzero := sub_nonpos.mpr hstep
  have hsum := add_le_add_left hzero
    (H + covarianceSource (KSSpinSource.family (fun j => atom (v j)))
      (KSSpinSource.coefficientCovariance c) (spinTransport H v c θ))
  simp only [add_zero] at hsum
  convert hsum using 1 <;> dsimp only [spinTransport] <;> abel

theorem independent_left_probe_nonneg [Nonempty n]
    (H : Matrix (n ⊕ n) (n ⊕ n) ℂ) (v : ι → n → ℂ) (c : ι → ℝ)
    {θ : ℝ} (hθ : 0 < θ) (i : ι) :
    0 ≤ realTrace (leftDensity (atom (v i)) * independentTransport H v c θ) := by
  apply realTrace_mul_nonneg
  · rw [leftDensity_atom]
    exact atom_posSemidef _
  · exact transportMatrix_posSemidef H _ _ hθ

theorem independent_right_probe_nonneg [Nonempty n]
    (H : Matrix (n ⊕ n) (n ⊕ n) ℂ) (v : ι → n → ℂ) (c : ι → ℝ)
    {θ : ℝ} (hθ : 0 < θ) (i : ι) :
    0 ≤ realTrace (rightDensity (atom (v i)) * independentTransport H v c θ) := by
  apply realTrace_mul_nonneg
  · rw [rightDensity_atom]
    exact atom_posSemidef _
  · exact transportMatrix_posSemidef H _ _ hθ

theorem independent_retire_plus [Nonempty n]
    (H : Matrix (n ⊕ n) (n ⊕ n) ℂ) (v : ι → n → ℂ) (c : ι → ℝ)
    (hc : ∀ j, 0 ≤ c j) {θ : ℝ} (hθ : 0 < θ) (i : ι)
    {a x : ℝ} (hx : x ≤ a)
    (hsafe : a - x ≤ c i * realTrace (leftDensity (atom (v i)) * independentTransport H v c θ)) :
    ownerPotential (H + (a - x) • signedLift (atom (v i)))
      (KSIndependentSource.family (fun j => atom (v j)))
      (KSIndependentSource.coefficientCovariance (Function.update c i 0)) θ ≤
    ownerPotential H (KSIndependentSource.family (fun j => atom (v j)))
      (KSIndependentSource.coefficientCovariance c) θ := by
  apply independent_retire H v c hc hθ i (a - x) hsafe
  exact (by linarith : -(a - x) ≤ 0).trans
    (mul_nonneg (hc i) (independent_right_probe_nonneg H v c hθ i))

theorem independent_retire_minus [Nonempty n]
    (H : Matrix (n ⊕ n) (n ⊕ n) ℂ) (v : ι → n → ℂ) (c : ι → ℝ)
    (hc : ∀ j, 0 ≤ c j) {θ : ℝ} (hθ : 0 < θ) (i : ι)
    {a x : ℝ} (hx : -a ≤ x)
    (hsafe : a + x ≤ c i * realTrace (rightDensity (atom (v i)) * independentTransport H v c θ)) :
    ownerPotential (H + (-a - x) • signedLift (atom (v i)))
      (KSIndependentSource.family (fun j => atom (v j)))
      (KSIndependentSource.coefficientCovariance (Function.update c i 0)) θ ≤
    ownerPotential H (KSIndependentSource.family (fun j => atom (v j)))
      (KSIndependentSource.coefficientCovariance c) θ := by
  apply independent_retire H v c hc hθ i (-a - x)
  · exact (by linarith : -a - x ≤ 0).trans
      (mul_nonneg (hc i) (independent_left_probe_nonneg H v c hθ i))
  · linarith

end MatrixSpencer.KSEndpointRetirement
