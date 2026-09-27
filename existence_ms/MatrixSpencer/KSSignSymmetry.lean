import MatrixSpencer.KSIndependentSource
import MatrixSpencer.FidelityCompression

/-! Exact sign-conjugation symmetry of the full optimizing density. -/

open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix

noncomputable section
namespace MatrixSpencer.KSSignSymmetry

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n]

def conjugate (J X : Matrix n n ℂ) : Matrix n n ℂ := J * X * J

theorem conjugate_posSemidef {J X : Matrix n n ℂ} (hJ : J.IsHermitian)
    (hX : X.PosSemidef) : (conjugate J X).PosSemidef := by
  simpa only [conjugate, hJ.eq] using hX.mul_mul_conjTranspose_same J

theorem conjugate_involutive {J : Matrix n n ℂ} (hJ : J * J = 1) (X : Matrix n n ℂ) :
    conjugate J (conjugate J X) = X := by
  simp only [conjugate]
  calc
    J * (J * X * J) * J = (J * J) * X * (J * J) := by simp only [Matrix.mul_assoc]
    _ = X := by rw [hJ, Matrix.one_mul, Matrix.mul_one]

theorem conjugate_eq_of_commute {J X : Matrix n n ℂ}
    (hJ : J * J = 1) (hX : Commute J X) : conjugate J X = X := by
  rw [conjugate, hX.eq, Matrix.mul_assoc, hJ, Matrix.mul_one]

theorem realTrace_conjugate {J : Matrix n n ℂ} (hJ : J.IsHermitian)
    (hJJ : J * J = 1) (X : Matrix n n ℂ) : realTrace (conjugate J X) = realTrace X := by
  have hunit : Jᴴ * J = 1 := by rw [hJ.eq, hJJ]
  simpa only [conjugate, hJ.eq] using realTrace_isometry_embedding J hunit X

theorem conjugate_mem_density {J S : Matrix n n ℂ} (hJ : J.IsHermitian)
    (hJJ : J * J = 1) (hS : S ∈ densitySet) : conjugate J S ∈ densitySet :=
  ⟨conjugate_posSemidef hJ hS.1, (realTrace_conjugate hJ hJJ S).trans hS.2⟩

theorem sqrt_conjugate {J S : Matrix n n ℂ} (hJ : J.IsHermitian)
    (hJJ : J * J = 1) (hS : S.PosSemidef) :
    CFC.sqrt (conjugate J S) = conjugate J (CFC.sqrt S) := by
  have hunit : Jᴴ * J = 1 := by rw [hJ.eq, hJJ]
  simpa only [conjugate, hJ.eq] using sqrt_isometry_embedding J hunit hS

theorem fidelity_conjugate {J S M : Matrix n n ℂ} (hJ : J.IsHermitian)
    (hJJ : J * J = 1) (hS : S.PosSemidef) (hM : M.PosSemidef) :
    fidelity (conjugate J S) (conjugate J M) = fidelity S M := by
  have hunit : Jᴴ * J = 1 := by rw [hJ.eq, hJJ]
  have h := fidelity_isometry_compression J hunit (conjugate_posSemidef hJ hS) hM
  simp only [hJ.eq] at h
  change fidelity (conjugate J S) (conjugate J M) =
    fidelity (conjugate J (conjugate J S)) M at h
  simpa only [conjugate_involutive hJJ] using h

theorem source_conjugate (A : ι → Matrix n n ℂ) (C : Matrix ι ι ℝ)
    (J : Matrix n n ℂ) (hA : ∀ i, Commute J (A i)) (S : Matrix n n ℂ) :
    covarianceSource A C (conjugate J S) = conjugate J (covarianceSource A C S) := by
  simp only [covarianceSource, conjugate, Matrix.mul_sum, Matrix.sum_mul,
    Matrix.mul_smul, Matrix.smul_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  calc
    A i * (J * S * J) * A j = (A i * J) * S * (J * A j) := by simp only [Matrix.mul_assoc]
    _ = (J * A i) * S * (A j * J) := by rw [← (hA i).eq, (hA j).eq]
    _ = J * (A i * S * A j) * J := by simp only [Matrix.mul_assoc]

theorem trace_center_conjugate {J H : Matrix n n ℂ}
    (hJ : J.IsHermitian) (hJJ : J * J = 1) (hH : Commute J H) (S : Matrix n n ℂ) :
    realTrace (H * conjugate J S) = realTrace (H * S) := by
  have he : H * conjugate J S = conjugate J (H * S) := by
    simp only [conjugate]
    calc
      H * (J * S * J) = (H * J) * S * J := by simp only [Matrix.mul_assoc]
      _ = (J * H) * S * J := by rw [← hH.eq]
      _ = J * (H * S) * J := by simp only [Matrix.mul_assoc]
  rw [he, realTrace_conjugate hJ hJJ]

theorem objective_conjugate {J H : Matrix n n ℂ}
    (hJ : J.IsHermitian) (hJJ : J * J = 1) (hH : Commute J H)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (hJA : ∀ i, Commute J (A i)) {C : Matrix ι ι ℝ} (hC : C.PosSemidef)
    (θ : ℝ) {S : Matrix n n ℂ} (hS : S.PosSemidef) :
    ownerObjective H A C θ (conjugate J S) = ownerObjective H A C θ S := by
  simp only [ownerObjective, trace_center_conjugate hJ hJJ hH,
    source_conjugate A C J hJA, fidelity_conjugate hJ hJJ hS
      (covarianceSource_posSemidef A hA hC hS), sqrt_conjugate hJ hJJ hS,
    realTrace_conjugate hJ hJJ]

/-- Invariance and strict concavity force symmetry of every actual optimizer. -/
theorem optimizer_conjugate_eq {J H : Matrix n n ℂ}
    (hJ : J.IsHermitian) (hJJ : J * J = 1) (hH : Commute J H)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (hJA : ∀ i, Commute J (A i)) {C : Matrix ι ι ℝ} (hC : C.PosSemidef)
    {θ : ℝ} (hθ : 0 < θ) {S : Matrix n n ℂ} (hS : S ∈ densitySet)
    (hmax : ∀ T ∈ densitySet, ownerObjective H A C θ T ≤ ownerObjective H A C θ S) :
    conjugate J S = S := by
  have hJS := conjugate_mem_density hJ hJJ hS
  have hval := objective_conjugate hJ hJJ hH A hA hJA hC θ hS.1
  have hmax' : ∀ T ∈ densitySet,
      densityObjective H (covarianceKraus A C) θ T ≤ densityObjective H (covarianceKraus A C) θ S := by
    intro T hT
    simpa only [ownerObjective_eq_densityObjective H A hA hC] using hmax T hT
  have hval' : densityObjective H (covarianceKraus A C) θ (conjugate J S) =
      densityObjective H (covarianceKraus A C) θ S := by
    simpa only [ownerObjective_eq_densityObjective H A hA hC] using hval
  exact (strictConcaveOn_densityObjective H (covarianceKraus A C) hθ).eq_of_isMaxOn
    (fun T hT => (hmax' T hT).trans_eq hval'.symm) hmax' hJS hS

def signMatrix : Matrix (n ⊕ n) (n ⊕ n) ℂ := signedLift (1 : Matrix n n ℂ)

theorem signMatrix_isHermitian : (signMatrix (n := n)).IsHermitian :=
  signedLift_isHermitian Matrix.isHermitian_one

theorem signMatrix_sq : signMatrix (n := n) * signMatrix = 1 := by
  simp [signMatrix, signedLift, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]

theorem signMatrix_commute_doubled (A : Matrix n n ℂ) :
    Commute signMatrix (KSSpinSource.doubled A) := by
  change _ * _ = _ * _
  simp [signMatrix, signedLift, KSSpinSource.doubled, Matrix.fromBlocks_multiply]

theorem signMatrix_commute_signedLift (A : Matrix n n ℂ) :
    Commute signMatrix (signedLift A) := by
  change _ * _ = _ * _
  simp [signMatrix, signedLift, Matrix.fromBlocks_multiply]

theorem signMatrix_commute_independent (A : ι → Matrix n n ℂ) (j : ι × Bool) :
    Commute signMatrix (KSIndependentSource.family A j) := by
  rcases j with ⟨i, b⟩
  cases b <;> change _ * _ = _ * _ <;>
    simp [signMatrix, signedLift, KSIndependentSource.family, leftDensity,
      rightDensity, Matrix.fromBlocks_multiply]

theorem sign_conjugate_blocks (X : Matrix (n ⊕ n) (n ⊕ n) ℂ) :
    conjugate signMatrix X = Matrix.fromBlocks X.toBlocks₁₁ (-X.toBlocks₁₂)
      (-X.toBlocks₂₁) X.toBlocks₂₂ := by
  rw [← Matrix.fromBlocks_toBlocks X]
  simp [conjugate, signMatrix, signedLift, Matrix.fromBlocks_multiply]

theorem sign_fixed_blockDiagonal {X : Matrix (n ⊕ n) (n ⊕ n) ℂ}
    (hX : conjugate signMatrix X = X) :
    X = Matrix.fromBlocks X.toBlocks₁₁ 0 0 X.toBlocks₂₂ := by
  rw [sign_conjugate_blocks] at hX
  ext a b
  cases a <;> cases b
  · rfl
  · rename_i a b
    have h := congrArg (fun M : Matrix (n ⊕ n) (n ⊕ n) ℂ => M (Sum.inl a) (Sum.inr b)) hX
    simp only [Matrix.fromBlocks_apply₁₂, Matrix.neg_apply, Matrix.toBlocks₁₂,
      Matrix.of_apply, Matrix.zero_apply] at h ⊢
    linear_combination -(1 / 2 : ℂ) * h
  · rename_i a b
    have h := congrArg (fun M : Matrix (n ⊕ n) (n ⊕ n) ℂ => M (Sum.inr a) (Sum.inl b)) hX
    simp only [Matrix.fromBlocks_apply₂₁, Matrix.neg_apply, Matrix.toBlocks₂₁,
      Matrix.of_apply, Matrix.zero_apply] at h ⊢
    linear_combination -(1 / 2 : ℂ) * h
  · rfl

end MatrixSpencer.KSSignSymmetry
