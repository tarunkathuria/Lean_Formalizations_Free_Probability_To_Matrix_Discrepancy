import MatrixSpencer.ProjectionSuper

/-!
# Exact Kraus coordinate composition and weighted Hilbert--Schmidt energy
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder
open Matrix

noncomputable section
namespace MatrixSpencer
namespace KrausCoordinateEnergy

variable {ι κ m n : Type*} [Fintype ι] [Fintype κ] [Fintype m] [Fintype n]

lemma entryEnergy_adjoint (A : Matrix m n ℂ) : entryEnergy Aᴴ = entryEnergy A := by
  simp only [entryEnergy, Matrix.conjTranspose_apply, Complex.star_def, Complex.normSq_conj]
  exact Finset.sum_comm

lemma entryEnergy_synthesis (K : ι → Matrix m n ℂ) :
    entryEnergy (krausSynthesis K) = ∑ a, entryEnergy (K a) := by
  simp only [entryEnergy, krausSynthesis, Fintype.sum_prod_type]
  calc
    _ = ∑ i, ∑ a, ∑ j, Complex.normSq (K a i j) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

omit [Fintype κ] in
lemma super_synthesis (D : ι → Matrix n n ℂ) (X : κ → Matrix n n ℂ) :
    krausSuper D * krausSynthesis X = krausSynthesis (fun a => krausChannel D (X a)) := by
  ext ij a
  exact krausSuper_mulVec D (X a) ij.1 ij.2

variable [DecidableEq n]

omit [DecidableEq n] in
lemma super_mulVec (D : ι → Matrix n n ℂ) (x : n × n → ℂ) :
    krausSuper D *ᵥ x = matrixVector (krausChannel D (matrixUnvector x)) := by
  ext ij
  exact krausSuper_mulVec D (matrixUnvector x) ij.1 ij.2

lemma right_weighted_super (D : ι → Matrix n n ℂ) (S : Matrix n n ℂ) :
    krausSuper (fun a => D a * S) = krausSuper D * ProjectionSuper.compression S := by
  apply Matrix.ext_of_mulVec_single
  intro j
  rw [← Matrix.mulVec_mulVec, ProjectionSuper.compression_mulVec, super_mulVec,
    super_mulVec, matrixUnvector_vector]
  congr 1
  simp only [krausChannel, Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- A synthesis cap controls the energy of composition with any physical operator. -/
lemma entryEnergy_mul_le {k : Type*} [Fintype k]
    (A : Matrix m n ℂ) (V : Matrix n k ℂ) {β : ℝ}
    (hV : V * Vᴴ ≤ β • (1 : Matrix n n ℂ)) :
    entryEnergy (A * V) ≤ β * entryEnergy A := by
  rw [entryEnergy_eq_realTrace_adjoint_mul, entryEnergy_eq_realTrace_adjoint_mul,
    Matrix.conjTranspose_mul]
  have he : realTrace (Vᴴ * Aᴴ * (A * V)) = realTrace ((Aᴴ * A) * (V * Vᴴ)) := by
    simpa only [realTrace, Matrix.mul_assoc] using
      congrArg RCLike.re (Matrix.trace_mul_comm Vᴴ (Aᴴ * A * V))
  rw [he]
  have h := realTrace_mul_mono (Matrix.posSemidef_conjTranspose_mul_self A) hV
  simpa only [Matrix.mul_smul, Matrix.mul_one, realTrace_smul] using h

lemma sandwiched_energy {P Y : Matrix n n ℂ} (hP : P.PosSemidef) (hY : Y.IsHermitian) :
    entryEnergy (CFC.sqrt P * Y * CFC.sqrt P) = realTrace (P * Y * P * Y) := by
  let S := CFC.sqrt P
  have hS : S.IsHermitian := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg P)).isHermitian
  have hSS : S * S = P := CFC.sqrt_mul_sqrt_self P hP.nonneg
  rw [entryEnergy_eq_realTrace_adjoint_mul]
  change realTrace ((S * Y * S)ᴴ * (S * Y * S)) = _
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hS.eq, hY.eq]
  calc
    _ = realTrace (S * Y * P * Y * S) := by
      calc
        _ = realTrace (S * (Y * ((S * S) * (Y * S)))) := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hSS]; simp only [Matrix.mul_assoc]
    _ = realTrace (S * S * Y * P * Y) := by
      simpa only [Matrix.mul_assoc] using realTrace_mul_comm (S * Y * P * Y) S
    _ = _ := by rw [hSS]

end KrausCoordinateEnergy
end MatrixSpencer
