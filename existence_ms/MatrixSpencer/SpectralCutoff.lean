import MatrixSpencer.KrausContraction

/-!
# Explicit spectral cutoffs of a positive matrix

The projections are constructed in an actual orthonormal eigenbasis, including
all eigenvalues equal to the threshold in the high projection.
-/

open scoped BigOperators ComplexConjugate MatrixOrder ComplexOrder Matrix

noncomputable section
namespace MatrixSpencer
namespace SpectralCutoff

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Conjugate a real diagonal by the matrix's eigenvector unitary. -/
def spectralMatrix {P : Matrix n n ℂ} (hP : P.IsHermitian) (f : n → ℝ) : Matrix n n ℂ :=
  (hP.eigenvectorUnitary : Matrix n n ℂ) * Matrix.diagonal (fun j => (f j : ℂ)) *
    (hP.eigenvectorUnitary : Matrix n n ℂ)ᴴ

lemma spectralMatrix_hermitian {P : Matrix n n ℂ} (hP : P.IsHermitian) (f : n → ℝ) :
    (spectralMatrix hP f).IsHermitian := by
  apply Matrix.isHermitian_mul_mul_conjTranspose
  exact Matrix.isHermitian_diagonal_iff.mpr (fun j => by
    change star (f j : ℂ) = (f j : ℂ)
    simp)

lemma spectralMatrix_posSemidef {P : Matrix n n ℂ} (hP : P.IsHermitian) {f : n → ℝ}
    (hf : ∀ j, 0 ≤ f j) : (spectralMatrix hP f).PosSemidef := by
  exact (Matrix.posSemidef_diagonal_iff.mpr (fun j => by exact_mod_cast hf j)).mul_mul_conjTranspose_same _

lemma spectralMatrix_sub {P : Matrix n n ℂ} (hP : P.IsHermitian) (f g : n → ℝ) :
    spectralMatrix hP (f - g) = spectralMatrix hP f - spectralMatrix hP g := by
  simp only [spectralMatrix, Pi.sub_apply, Complex.ofReal_sub]
  rw [← Matrix.diagonal_sub, Matrix.mul_sub, Matrix.sub_mul]

lemma spectralMatrix_mono {P : Matrix n n ℂ} (hP : P.IsHermitian)
    {f g : n → ℝ} (hfg : ∀ j, f j ≤ g j) : spectralMatrix hP f ≤ spectralMatrix hP g := by
  apply Matrix.le_iff.mpr
  rw [← spectralMatrix_sub]
  exact spectralMatrix_posSemidef hP (fun j => sub_nonneg.mpr (hfg j))

lemma spectralMatrix_mul {P : Matrix n n ℂ} (hP : P.IsHermitian) (f g : n → ℝ) :
    spectralMatrix hP f * spectralMatrix hP g = spectralMatrix hP (f * g) := by
  have hu : (hP.eigenvectorUnitary : Matrix n n ℂ)ᴴ * hP.eigenvectorUnitary = 1 := by
    exact unitary.coe_star_mul_self hP.eigenvectorUnitary
  simp only [spectralMatrix, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (hP.eigenvectorUnitary : Matrix n n ℂ)ᴴ, hu, Matrix.one_mul,
    ← Matrix.mul_assoc (Matrix.diagonal _), Matrix.diagonal_mul_diagonal]
  simp only [Pi.mul_apply, Complex.ofReal_mul]

lemma spectralMatrix_smul {P : Matrix n n ℂ} (hP : P.IsHermitian) (c : ℝ) (f : n → ℝ) :
    spectralMatrix hP (c • f) = c • spectralMatrix hP f := by
  simp only [spectralMatrix, Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul]
  rw [show (fun j => (c : ℂ) * (f j : ℂ)) = c • (fun j => (f j : ℂ)) by rfl,
    Matrix.diagonal_smul, Matrix.mul_smul, Matrix.smul_mul]

lemma spectralMatrix_one {P : Matrix n n ℂ} (hP : P.IsHermitian) :
    spectralMatrix hP (fun _ => 1) = 1 := by
  simp only [spectralMatrix, Complex.ofReal_one, Matrix.diagonal_one, Matrix.mul_one]
  exact unitary.coe_mul_star_self hP.eigenvectorUnitary

lemma spectralMatrix_eigenvalues {P : Matrix n n ℂ} (hP : P.IsHermitian) :
    spectralMatrix hP hP.eigenvalues = P := by
  exact hP.spectral_theorem.symm

lemma spectralMatrix_trace {P : Matrix n n ℂ} (hP : P.IsHermitian) (f : n → ℝ) :
    realTrace (spectralMatrix hP f) = ∑ j, f j := by
  have hu : (hP.eigenvectorUnitary : Matrix n n ℂ)ᴴ * hP.eigenvectorUnitary = 1 :=
    unitary.coe_star_mul_self hP.eigenvectorUnitary
  rw [spectralMatrix, realTrace_mul_cycle, hu, Matrix.one_mul]
  simp [realTrace, Matrix.trace_diagonal]

/-- The high spectral projection includes eigenvalues equal to the threshold. -/
def high {P : Matrix n n ℂ} (hP : P.IsHermitian) (ε : ℝ) : Matrix n n ℂ :=
  spectralMatrix hP (fun j => if ε ≤ hP.eigenvalues j then 1 else 0)

/-- The complementary low spectral projection. -/
def low {P : Matrix n n ℂ} (hP : P.IsHermitian) (ε : ℝ) : Matrix n n ℂ := 1 - high hP ε

/-- The part of P on the low spectral subspace. -/
def lowPart {P : Matrix n n ℂ} (hP : P.IsHermitian) (ε : ℝ) : Matrix n n ℂ := low hP ε * P

lemma low_eq_spectralMatrix {P : Matrix n n ℂ} (hP : P.IsHermitian) (ε : ℝ) :
    low hP ε = spectralMatrix hP (fun j => if ε ≤ hP.eigenvalues j then 0 else 1) := by
  rw [low, high, ← spectralMatrix_one hP, ← spectralMatrix_sub]
  congr 1
  funext j
  dsimp
  split_ifs <;> norm_num

lemma lowPart_eq_spectralMatrix {P : Matrix n n ℂ} (hP : P.IsHermitian) (ε : ℝ) :
    lowPart hP ε = spectralMatrix hP
      (fun j => if ε ≤ hP.eigenvalues j then 0 else hP.eigenvalues j) := by
  rw [lowPart, low_eq_spectralMatrix]
  conv_lhs => rhs; rw [← spectralMatrix_eigenvalues hP]
  rw [spectralMatrix_mul]
  congr 1
  funext j
  dsimp
  split_ifs <;> simp

lemma high_hermitian {P : Matrix n n ℂ} (hP : P.IsHermitian) (ε : ℝ) :
    (high hP ε).IsHermitian := spectralMatrix_hermitian hP _

lemma low_hermitian {P : Matrix n n ℂ} (hP : P.IsHermitian) (ε : ℝ) :
    (low hP ε).IsHermitian := by
  rw [low_eq_spectralMatrix]
  exact spectralMatrix_hermitian hP _

lemma high_posSemidef {P : Matrix n n ℂ} (hP : P.IsHermitian) (ε : ℝ) :
    (high hP ε).PosSemidef := spectralMatrix_posSemidef hP (fun j => by split_ifs <;> norm_num)

lemma low_posSemidef {P : Matrix n n ℂ} (hP : P.IsHermitian) (ε : ℝ) :
    (low hP ε).PosSemidef := by
  rw [low_eq_spectralMatrix]
  exact spectralMatrix_posSemidef hP (fun j => by split_ifs <;> norm_num)

lemma high_idempotent {P : Matrix n n ℂ} (hP : P.IsHermitian) (ε : ℝ) :
    high hP ε * high hP ε = high hP ε := by
  rw [high, spectralMatrix_mul]
  congr 1
  funext j
  dsimp
  split_ifs <;> norm_num

lemma low_idempotent {P : Matrix n n ℂ} (hP : P.IsHermitian) (ε : ℝ) :
    low hP ε * low hP ε = low hP ε := by
  simp only [low, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
    high_idempotent, sub_self, sub_zero]

lemma high_add_low {P : Matrix n n ℂ} (hP : P.IsHermitian) (ε : ℝ) :
    high hP ε + low hP ε = 1 := by simp [low]

lemma high_mul_low {P : Matrix n n ℂ} (hP : P.IsHermitian) (ε : ℝ) :
    high hP ε * low hP ε = 0 := by simp [low, Matrix.mul_sub, high_idempotent]

lemma high_commute {P : Matrix n n ℂ} (hP : P.IsHermitian) (ε : ℝ) :
    Commute (high hP ε) P := by
  change high hP ε * P = P * high hP ε
  conv_lhs => rhs; rw [← spectralMatrix_eigenvalues hP]
  conv_rhs => lhs; rw [← spectralMatrix_eigenvalues hP]
  rw [high, spectralMatrix_mul, spectralMatrix_mul, mul_comm]

lemma low_commute {P : Matrix n n ℂ} (hP : P.IsHermitian) (ε : ℝ) :
    Commute (low hP ε) P := by
  change low hP ε * P = P * low hP ε
  simp only [low, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
    (high_commute hP ε).eq]

lemma lowPart_posSemidef {P : Matrix n n ℂ} (hP : P.PosSemidef) (ε : ℝ) :
    (lowPart hP.isHermitian ε).PosSemidef := by
  rw [lowPart_eq_spectralMatrix]
  exact spectralMatrix_posSemidef hP.isHermitian (fun j => by
    split_ifs
    · exact le_rfl
    · exact hP.eigenvalues_nonneg j)

lemma lowPart_le {P : Matrix n n ℂ} (hP : P.PosSemidef) (ε : ℝ) :
    lowPart hP.isHermitian ε ≤ P := by
  rw [lowPart_eq_spectralMatrix]
  conv_rhs => rw [← spectralMatrix_eigenvalues hP.isHermitian]
  exact spectralMatrix_mono hP.isHermitian (fun j => by
    split_ifs
    · exact hP.eigenvalues_nonneg j
    · exact le_rfl)

/-- The squared low-part energy is controlled by threshold times total trace. -/
lemma lowPart_trace_sq_le {P : Matrix n n ℂ} (hP : P.PosSemidef) {ε : ℝ} (hε : 0 < ε) :
    realTrace (lowPart hP.isHermitian ε * lowPart hP.isHermitian ε) ≤ ε * realTrace P := by
  rw [lowPart_eq_spectralMatrix, spectralMatrix_mul, spectralMatrix_trace]
  conv_rhs => arg 2; arg 1; rw [← spectralMatrix_eigenvalues hP.isHermitian]
  rw [spectralMatrix_trace, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  dsimp
  split_ifs with hj
  · simpa only [mul_zero] using mul_nonneg hε.le (hP.eigenvalues_nonneg j)
  · exact mul_le_mul_of_nonneg_right (le_of_lt (lt_of_not_ge hj)) (hP.eigenvalues_nonneg j)

/-- The high projection is dominated by inverse threshold times the original matrix. -/
lemma high_le_inv_smul {P : Matrix n n ℂ} (hP : P.PosSemidef) {ε : ℝ} (hε : 0 < ε) :
    high hP.isHermitian ε ≤ ε⁻¹ • P := by
  conv_rhs => rhs; rw [← spectralMatrix_eigenvalues hP.isHermitian]
  rw [← spectralMatrix_smul]
  unfold high
  apply spectralMatrix_mono
  intro j
  dsimp
  split_ifs with hj
  · exact (one_le_inv_mul₀ hε).mpr hj
  · exact mul_nonneg (inv_nonneg.mpr hε.le) (hP.eigenvalues_nonneg j)

lemma high_le_one {P : Matrix n n ℂ} (hP : P.IsHermitian) (ε : ℝ) :
    high hP ε ≤ 1 := by
  apply Matrix.le_iff.mpr
  exact low_posSemidef hP ε

lemma low_le_one {P : Matrix n n ℂ} (hP : P.IsHermitian) (ε : ℝ) :
    low hP ε ≤ 1 := by
  apply Matrix.le_iff.mpr
  simpa only [low, sub_sub_cancel] using high_posSemidef hP ε

lemma low_mul_P_mul_low {P : Matrix n n ℂ} (hP : P.IsHermitian) (ε : ℝ) :
    low hP ε * P * low hP ε = lowPart hP ε := by
  rw [Matrix.mul_assoc, ← (low_commute hP ε).eq, ← Matrix.mul_assoc, low_idempotent]
  rfl

lemma high_mul_P_mul_high {P : Matrix n n ℂ} (hP : P.IsHermitian) (ε : ℝ) :
    high hP ε * P * high hP ε = P - lowPart hP ε := by
  rw [Matrix.mul_assoc, ← (high_commute hP ε).eq, ← Matrix.mul_assoc, high_idempotent]
  simp [lowPart, low, Matrix.sub_mul]

end SpectralCutoff
end MatrixSpencer
