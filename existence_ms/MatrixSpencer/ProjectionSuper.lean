import MatrixSpencer.JordanFrame
import MatrixSpencer.SpectralCutoff
import MatrixSpencer.QuadraticOrder

/-!
# Physical compression as an actual Hilbert--Schmidt projection
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder
open Matrix

noncomputable section
namespace MatrixSpencer
namespace ProjectionSuper

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n]

/-- The actual coordinate matrix of X ↦ H X Hᴴ. -/
def compression (H : Matrix n n ℂ) : Matrix (n × n) (n × n) ℂ :=
  krausSuper (fun _ : Unit => H)

omit [DecidableEq n] in
lemma compression_mulVec (H : Matrix n n ℂ) (x : n × n → ℂ) :
    compression H *ᵥ x = matrixVector (H * matrixUnvector x * Hᴴ) := by
  ext ij
  simpa only [compression, krausChannel, Fintype.sum_unique, matrixVector] using
    krausSuper_mulVec (fun _ : Unit => H) (matrixUnvector x) ij.1 ij.2

omit [Fintype n] [DecidableEq n] in
lemma compression_hermitian {H : Matrix n n ℂ} (hH : H.IsHermitian) :
    (compression H).IsHermitian := KrausContraction.super_hermitian _ (fun _ => hH)

lemma compression_idempotent {H : Matrix n n ℂ} (hH : H.IsHermitian) (hHH : H * H = H) :
    compression H * compression H = compression H := by
  apply Matrix.ext_of_mulVec_single
  intro j
  rw [← Matrix.mulVec_mulVec, compression_mulVec, compression_mulVec, matrixUnvector_vector,
    hH.eq]
  congr 1
  simp only [← Matrix.mul_assoc, hHH]
  rw [Matrix.mul_assoc, hHH]

lemma compression_posSemidef {H : Matrix n n ℂ} (hH : H.IsHermitian) (hHH : H * H = H) :
    (compression H).PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self (compression H)
  rw [(compression_hermitian hH).eq, compression_idempotent hH hHH] at h
  exact h

lemma compression_le_one {H : Matrix n n ℂ} (hH : H.IsHermitian) (hHH : H * H = H) :
    compression H ≤ 1 := by
  apply Matrix.le_iff.mpr
  have h := Matrix.posSemidef_conjTranspose_mul_self (1 - compression H)
  simpa only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, (compression_hermitian hH).eq,
    Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
    compression_idempotent hH hHH, sub_self, sub_zero] using h

omit [Fintype ι] [DecidableEq ι] [DecidableEq n] in
lemma compression_synthesis (H : Matrix n n ℂ) (D : ι → Matrix n n ℂ) :
    compression H * krausSynthesis D = krausSynthesis (fun a => H * D a * Hᴴ) := by
  ext ij a
  change (compression H *ᵥ matrixVector (D a)) ij = _
  rw [compression_mulVec, matrixUnvector_vector]
  rfl

/-- Right multiplication by an orthogonal projection decreases entry energy. -/
lemma right_projection_energy_le (X : Matrix n n ℂ) {H : Matrix n n ℂ}
    (hH : H.IsHermitian) (hHH : H * H = H) (hHle : H ≤ 1) :
    entryEnergy (X * H) ≤ entryEnergy X := by
  have h := realTrace_mul_mono (Matrix.posSemidef_conjTranspose_mul_self X) hHle
  rw [entryEnergy_eq_realTrace_adjoint_mul, entryEnergy_eq_realTrace_adjoint_mul,
    Matrix.conjTranspose_mul, hH.eq]
  calc
    _ = realTrace ((Xᴴ * X) * H) := by
      have he : realTrace (H * Xᴴ * (X * H)) = realTrace (Xᴴ * X * H * H) := by
        simpa only [Matrix.mul_assoc] using realTrace_mul_comm H (Xᴴ * X * H)
      rw [he, Matrix.mul_assoc, Matrix.mul_assoc, hHH]
      simp only [Matrix.mul_assoc]
    _ ≤ _ := by simpa only [Matrix.mul_one] using h

lemma left_projection_energy_le (X : Matrix n n ℂ) {H : Matrix n n ℂ}
    (hH : H.IsHermitian) (hHle : H ≤ 1) (hHH : H * H = H) :
    entryEnergy (H * X) ≤ entryEnergy X := by
  have h := (Matrix.le_iff.mp hHle).conjTranspose_mul_mul_same X
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one] at h
  have ht := realTrace_nonneg h
  rw [realTrace_sub] at ht
  rw [entryEnergy_eq_realTrace_adjoint_mul, entryEnergy_eq_realTrace_adjoint_mul,
    Matrix.conjTranspose_mul, hH.eq]
  have he : Xᴴ * H * (H * X) = Xᴴ * H * X := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc H, hHH, ← Matrix.mul_assoc]
  rw [he]
  linarith

/-- The compression projection is dominated by the positive Jordan operator.
This estimate is on the full complex matrix space. -/
lemma compression_le_jordan {P H : Matrix n n ℂ} (hP : P.IsHermitian)
    (hH : H.IsHermitian) (hHH : H * H = H) (hHle : H ≤ 1)
    {ε : ℝ} (hε : 0 ≤ ε) (hHP : ε • H ≤ P) :
    (2 * ε) • compression H ≤ jordanSuper P := by
  apply matrix_le_of_real_quadratic_le
    ((show IsSelfAdjoint (2 * ε) from rfl).smul (compression_hermitian hH))
    (jordanSuper_isHermitian hP)
  intro x
  let X := matrixUnvector x
  have hleft := realTrace_mul_mono (Matrix.posSemidef_self_mul_conjTranspose X) hHP
  have hright := realTrace_mul_mono (Matrix.posSemidef_conjTranspose_mul_self X) hHP
  have hXHX : realTrace (Xᴴ * H * X) = entryEnergy (H * X) := by
    rw [entryEnergy_eq_realTrace_adjoint_mul, Matrix.conjTranspose_mul, hH.eq]
    have he : Xᴴ * H * (H * X) = Xᴴ * H * X := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc H, hHH, ← Matrix.mul_assoc]
    rw [he]
  have hXXH : realTrace (Xᴴ * X * H) = entryEnergy (X * H) := by
    rw [entryEnergy_eq_realTrace_adjoint_mul, Matrix.conjTranspose_mul, hH.eq]
    have he := realTrace_mul_cycle H (Xᴴ * X) H
    rw [hHH] at he
    simpa only [Matrix.mul_assoc] using (he.trans (realTrace_mul_comm H (Xᴴ * X))).symm
  have hE : RCLike.re (star x ⬝ᵥ (compression H *ᵥ x)) = entryEnergy (H * X * H) := by
    have he := vectorEnergy_mulVec_eq_pairing (compression H) x
    rw [(compression_hermitian hH).eq, compression_idempotent hH hHH,
      compression_mulVec, hH.eq] at he
    simpa only [vectorEnergy, matrixVector_energy, compression_mulVec, hH.eq] using he.symm
  have hj : RCLike.re (star x ⬝ᵥ (jordanSuper P *ᵥ x)) =
      realTrace (Xᴴ * P * X) + realTrace (Xᴴ * X * P) := by
    rw [jordanSuper_mulVec]
    change RCLike.re (star (matrixVector X) ⬝ᵥ matrixVector (P * X + X * P)) = _
    rw [matrixVector_dotProduct, Matrix.mul_add, Matrix.trace_add, map_add]
    simp only [realTrace, Matrix.mul_assoc]
  have h₁ := right_projection_energy_le (H * X) hH hHH hHle
  have h₂ := left_projection_energy_le (X * H) hH hHle hHH
  have hc : H * (X * H) = H * X * H := (Matrix.mul_assoc ..).symm
  rw [hc] at h₂
  have hleft' : ε * entryEnergy (H * X) ≤ realTrace (Xᴴ * P * X) := by
    rw [Matrix.mul_smul, realTrace_smul] at hleft
    have he₁ : realTrace (X * Xᴴ * H) = realTrace (Xᴴ * H * X) := by
      simpa only [Matrix.mul_assoc] using realTrace_mul_comm X (Xᴴ * H)
    have he₂ : realTrace (X * Xᴴ * P) = realTrace (Xᴴ * P * X) := by
      simpa only [Matrix.mul_assoc] using realTrace_mul_comm X (Xᴴ * P)
    simpa only [he₁, he₂, hXHX] using hleft
  have hright' : ε * entryEnergy (X * H) ≤ realTrace (Xᴴ * X * P) := by
    simpa only [Matrix.mul_smul, realTrace_smul, hXXH] using hright
  rw [Matrix.smul_mulVec, dotProduct_smul, RCLike.smul_re, hE, hj]
  nlinarith [mul_le_mul_of_nonneg_left h₁ hε, mul_le_mul_of_nonneg_left h₂ hε]

omit [Fintype n] [DecidableEq ι] [DecidableEq n] in
lemma synthesis_mulVec (K : ι → Matrix n n ℂ) (x : ι → ℂ) :
    krausSynthesis K *ᵥ x = matrixVector (∑ a, x a • K a) := by
  ext ij
  simp only [krausSynthesis, Matrix.mulVec, dotProduct, matrixVector, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, mul_comm]

omit [DecidableEq ι] in
/-- Right compression acts contractively on the actual complex coefficient Gram. -/
lemma synthesis_right_projection_gram_le (K : ι → Matrix n n ℂ) {H : Matrix n n ℂ}
    (hH : H.IsHermitian) (hHH : H * H = H) (hHle : H ≤ 1) :
    (krausSynthesis (fun a => K a * H))ᴴ * krausSynthesis (fun a => K a * H) ≤
      (krausSynthesis K)ᴴ * krausSynthesis K := by
  apply matrix_le_of_real_quadratic_le
    (Matrix.posSemidef_conjTranspose_mul_self _).isHermitian
    (Matrix.posSemidef_conjTranspose_mul_self _).isHermitian
  intro x
  rw [← vectorEnergy_mulVec_eq_pairing, ← vectorEnergy_mulVec_eq_pairing,
    synthesis_mulVec, synthesis_mulVec]
  simp only [vectorEnergy, matrixVector_energy]
  have he : (∑ a, x a • (K a * H)) = (∑ a, x a • K a) * H := by
    simp only [Matrix.sum_mul, Matrix.smul_mul]
  rw [he]
  exact right_projection_energy_le _ hH hHH hHle

end ProjectionSuper
end MatrixSpencer
