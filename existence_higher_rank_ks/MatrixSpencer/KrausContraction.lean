import MatrixSpencer.Realignment
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Tactic

/-!
# Hilbert--Schmidt contraction of a faithful reversible Kraus channel

The Kraus operators are Hermitian and have a positive definite fixed point.
No unitality or positivity of the channel superoperator is assumed. Matrix
operator norms used internally are explicitly the Euclidean operator norm.
-/

open scoped BigOperators ComplexConjugate MatrixOrder ComplexOrder Matrix
  Matrix.Norms.L2Operator

noncomputable section
namespace MatrixSpencer
namespace KrausContraction

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
lemma channel_add (D : ι → Matrix n n ℂ) (X Y : Matrix n n ℂ) :
    krausChannel D (X + Y) = krausChannel D X + krausChannel D Y := by
  simp [krausChannel, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]

lemma channel_smul (D : ι → Matrix n n ℂ) (c : ℂ) (X : Matrix n n ℂ) :
    krausChannel D (c • X) = c • krausChannel D X := by
  simp [krausChannel, Finset.smul_sum]

lemma channel_real_smul (D : ι → Matrix n n ℂ) (c : ℝ) (X : Matrix n n ℂ) :
    krausChannel D (c • X) = c • krausChannel D X := by
  simp [krausChannel, Finset.smul_sum]

omit [DecidableEq n] in
lemma channel_adjoint (D : ι → Matrix n n ℂ) (X : Matrix n n ℂ) :
    krausChannel D Xᴴ = (krausChannel D X)ᴴ := by
  simp [krausChannel, Matrix.conjTranspose_sum, Matrix.conjTranspose_mul,
    Matrix.mul_assoc]

omit [DecidableEq n] in
lemma channel_mono (D : ι → Matrix n n ℂ) : Monotone (krausChannel D) := by
  intro X Y hXY
  apply Matrix.le_iff.mpr
  have h : (∑ a, D a * (Y - X) * (D a)ᴴ).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (Finset.sum_nonneg fun a _ =>
      ((Matrix.le_iff.mp hXY).mul_mul_conjTranspose_same (D a)).nonneg)
  simpa only [Matrix.mul_sub, Matrix.sub_mul, Finset.sum_sub_distrib, krausChannel] using h

omit [Fintype n] [DecidableEq n] in
lemma super_hermitian (D : ι → Matrix n n ℂ) (hD : ∀ a, (D a).IsHermitian) :
    (krausSuper D).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro ij kl
  simp only [krausSuper, star_sum, star_mul]
  apply Finset.sum_congr rfl
  intro a _
  change star (D a kl.2 ij.2 |> conj) * star (D a kl.1 ij.1) = _
  rw [(hD a).apply ij.1 kl.1]
  change star (star (D a kl.2 ij.2)) * D a ij.1 kl.1 = D a ij.1 kl.1 * star (D a ij.2 kl.2)
  rw [star_star]
  rw [(hD a).apply kl.2 ij.2, mul_comm]

/-- The two-sided spectral order interval controls a Hermitian operator norm. -/
lemma norm_le_of_order_interval {A : Matrix n n ℂ} (hA : A.IsHermitian)
    {b : ℝ} (hb : 0 ≤ b) (hl : (-b) • (1 : Matrix n n ℂ) ≤ A)
    (hu : A ≤ b • (1 : Matrix n n ℂ)) : ‖A‖ ≤ b := by
  letI : CStarAlgebra (Matrix n n ℂ) := {}
  rcases subsingleton_or_nontrivial (Matrix n n ℂ) with h | h
  · letI := h
    simpa only [Subsingleton.elim A 0, norm_zero] using hb
  · letI := h
    have hl' : algebraMap ℝ (Matrix n n ℂ) (-b) ≤ A := by
      simpa only [Algebra.algebraMap_eq_smul_one] using hl
    have hu' : A ≤ algebraMap ℝ (Matrix n n ℂ) b := by
      simpa only [Algebra.algebraMap_eq_smul_one] using hu
    rcases CStarAlgebra.norm_or_neg_norm_mem_spectrum (show IsSelfAdjoint A from hA) with hpos | hneg
    · exact (le_algebraMap_iff_spectrum_le (show IsSelfAdjoint A from hA)).mp hu' _ hpos
    · have := (algebraMap_le_iff_le_spectrum (show IsSelfAdjoint A from hA)).mp hl' _ hneg
      linarith

omit [DecidableEq n] in
lemma congruence_mono {A B : Matrix n n ℂ} (hAB : A ≤ B)
    (W : Matrix n n ℂ) (hW : W.IsHermitian) : W * A * W ≤ W * B * W := by
  apply Matrix.le_iff.mpr
  have h := (Matrix.le_iff.mp hAB).mul_mul_conjTranspose_same W
  rw [hW.eq, Matrix.mul_sub, Matrix.sub_mul] at h
  exact h

/-- Faithfulness rules out Hermitian eigenmatrices with eigenvalue outside [-1,1]. -/
lemma hermitian_eigenvalue_abs_le (D : ι → Matrix n n ℂ)
    {P Y : Matrix n n ℂ} (hP : P.PosDef) (hfix : krausChannel D P = P)
    (hY : Y.IsHermitian) (hY0 : Y ≠ 0) {lam : ℝ}
    (heig : krausChannel D Y = lam • Y) : |lam| ≤ 1 := by
  letI : CStarAlgebra (Matrix n n ℂ) := {}
  let S := CFC.sqrt P
  have hS : S.IsHermitian := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg P)).isHermitian
  have hSS : S * S = P := CFC.sqrt_mul_sqrt_self P hP.posSemidef.nonneg
  have hSu : IsUnit S := (CFC.isUnit_sqrt_iff P hP.posSemidef.nonneg).mpr hP.isUnit
  letI := hSu.invertible
  let R := S⁻¹
  have hR : R.IsHermitian := hS.inv
  have hSR : S * R = 1 := Matrix.mul_inv_of_invertible S
  have hRS : R * S = 1 := Matrix.inv_mul_of_invertible S
  let Q := R * Y * R
  have hQ : Q.IsHermitian := by
    simpa only [hR.eq] using Matrix.isHermitian_mul_mul_conjTranspose R hY
  have hrecover : S * Q * S = Y := by
    dsimp [Q]
    simp only [← Matrix.mul_assoc, hSR, Matrix.one_mul]
    rw [Matrix.mul_assoc, hRS, Matrix.mul_one]
  have hRP : R * P * R = 1 := by
    rw [← hSS, ← Matrix.mul_assoc, hRS, Matrix.one_mul, hSR]
  have hQ0 : Q ≠ 0 := by
    intro h0
    apply hY0
    rw [← hrecover, h0, Matrix.mul_zero, Matrix.zero_mul]
  have hu : Q ≤ ‖Q‖ • (1 : Matrix n n ℂ) := by
    simpa only [Algebra.algebraMap_eq_smul_one] using
      (show IsSelfAdjoint Q from hQ).le_algebraMap_norm_self
  have hl : (-‖Q‖) • (1 : Matrix n n ℂ) ≤ Q := by
    simpa only [Algebra.algebraMap_eq_smul_one, neg_smul] using
      (show IsSelfAdjoint Q from hQ).neg_algebraMap_norm_le_self
  have hYu : Y ≤ ‖Q‖ • P := by
    have h := congruence_mono hu S hS
    simpa only [hrecover, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hSS] using h
  have hYl : (-‖Q‖) • P ≤ Y := by
    have h := congruence_mono hl S hS
    simpa only [hrecover, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hSS] using h
  have hOu : lam • Y ≤ ‖Q‖ • P := by
    have h := channel_mono D hYu
    simpa only [heig, channel_real_smul, hfix] using h
  have hOl : (-‖Q‖) • P ≤ lam • Y := by
    have h := channel_mono D hYl
    simpa only [heig, channel_real_smul, hfix] using h
  have hlamu : lam • Q ≤ ‖Q‖ • (1 : Matrix n n ℂ) := by
    have h := congruence_mono hOu R hR
    simpa only [Matrix.mul_smul, Matrix.smul_mul, hRP] using h
  have hlaml : (-‖Q‖) • (1 : Matrix n n ℂ) ≤ lam • Q := by
    have h := congruence_mono hOl R hR
    simpa only [Matrix.mul_smul, Matrix.smul_mul, hRP] using h
  have hlamh : (lam • Q).IsHermitian := (show IsSelfAdjoint lam from rfl).smul (show IsSelfAdjoint Q from hQ)
  have hnorm := norm_le_of_order_interval hlamh (norm_nonneg Q) hlaml hlamu
  rw [norm_smul, Real.norm_eq_abs] at hnorm
  have hn : 0 < ‖Q‖ := norm_pos_iff.mpr hQ0
  nlinarith

/-- A real eigenvalue always has a nonzero Hermitian eigenmatrix. -/
lemma exists_hermitian_eigenmatrix (D : ι → Matrix n n ℂ)
    {X : Matrix n n ℂ} (hX : X ≠ 0) {lam : ℝ}
    (heig : krausChannel D X = lam • X) :
    ∃ Y : Matrix n n ℂ, Y.IsHermitian ∧ Y ≠ 0 ∧ krausChannel D Y = lam • Y := by
  have hadj : krausChannel D Xᴴ = lam • Xᴴ := by
    rw [channel_adjoint, heig, Matrix.conjTranspose_smul]
    rfl
  by_cases hsum : X + Xᴴ = 0
  · refine ⟨Complex.I • X, ?_, ?_, ?_⟩
    · have hanti : Xᴴ = -X := eq_neg_of_add_eq_zero_right hsum
      change (Complex.I • X)ᴴ = Complex.I • X
      simp only [Matrix.conjTranspose_smul, hanti, Complex.star_def, Complex.conj_I,
        neg_smul, smul_neg, neg_neg]
    · exact smul_ne_zero Complex.I_ne_zero hX
    · rw [channel_smul, heig, smul_comm]
  · refine ⟨X + Xᴴ, ?_, hsum, ?_⟩
    · change (X + Xᴴ)ᴴ = X + Xᴴ
      simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose, add_comm]
    · rw [channel_add, heig, hadj, smul_add]

/-- All eigenvalues of the actual channel matrix lie in [-1,1]. -/
lemma super_eigenvalue_abs_le (D : ι → Matrix n n ℂ)
    (hD : ∀ a, (D a).IsHermitian) {P : Matrix n n ℂ}
    (hP : P.PosDef) (hfix : krausChannel D P = P) (j : n × n) :
    |(super_hermitian D hD).eigenvalues j| ≤ 1 := by
  let hK := super_hermitian D hD
  let v := hK.eigenvectorBasis j
  let X : Matrix n n ℂ := fun a b => v (a,b)
  have hX0 : X ≠ 0 := by
    intro hzero
    have hv : v = 0 := by
      ext ab
      exact congr_fun (congr_fun hzero ab.1) ab.2
    exact (hK.eigenvectorBasis.orthonormal.ne_zero j) hv
  have heig : krausChannel D X = hK.eigenvalues j • X := by
    ext a b
    rw [← krausSuper_mulVec D X a b]
    exact congr_fun (hK.mulVec_eigenvectorBasis j) (a,b)
  obtain ⟨Y, hY, hY0, hYeig⟩ := exists_hermitian_eigenmatrix D hX0 heig
  exact hermitian_eigenvalue_abs_le D hP hfix hY hY0 hYeig

/-- The channel matrix has Euclidean operator norm at most one. -/
theorem super_opNorm_le_one (D : ι → Matrix n n ℂ)
    (hD : ∀ a, (D a).IsHermitian) {P : Matrix n n ℂ}
    (hP : P.PosDef) (hfix : krausChannel D P = P) :
    ‖krausSuper D‖ ≤ 1 := by
  letI : CStarAlgebra (Matrix (n × n) (n × n) ℂ) := {}
  let hK := super_hermitian D hD
  have hs : ∀ r ∈ spectrum ℝ (krausSuper D), |r| ≤ 1 := by
    intro r hr
    rw [hK.spectrum_real_eq_range_eigenvalues] at hr
    obtain ⟨j, rfl⟩ := hr
    exact super_eigenvalue_abs_le D hD hP hfix j
  apply norm_le_of_order_interval hK (by norm_num)
  · have h := (algebraMap_le_iff_le_spectrum (show IsSelfAdjoint (krausSuper D) from hK)).mpr
      (fun r hr => (abs_le.mp (hs r hr)).1)
    simpa only [Algebra.algebraMap_eq_smul_one] using h
  · have h := (le_algebraMap_iff_spectrum_le (show IsSelfAdjoint (krausSuper D) from hK)).mpr
      (fun r hr => (abs_le.mp (hs r hr)).2)
    simpa only [Algebra.algebraMap_eq_smul_one] using h

omit [DecidableEq n] in
/-- Vectorization is an exact isometry from the explicit entry energy to Euclidean space. -/
lemma entryEnergy_eq_vectorization_norm_sq (X : Matrix n n ℂ) :
    entryEnergy X = ‖(WithLp.toLp 2 (fun ij : n × n => X ij.1 ij.2) :
      EuclideanSpace ℂ (n × n))‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [entryEnergy, Fintype.sum_prod_type,
    Complex.normSq_eq_norm_sq]
  rfl

/-- Ordinary, unweighted Hilbert--Schmidt contraction for every complex input matrix. -/
theorem channel_entryEnergy_le (D : ι → Matrix n n ℂ)
    (hD : ∀ a, (D a).IsHermitian) {P : Matrix n n ℂ}
    (hP : P.PosDef) (hfix : krausChannel D P = P) (X : Matrix n n ℂ) :
    entryEnergy (krausChannel D X) ≤ entryEnergy X := by
  let v : EuclideanSpace ℂ (n × n) := WithLp.toLp 2 (fun ij => X ij.1 ij.2)
  let K := Matrix.toEuclideanCLM (n := n × n) (𝕜 := ℂ) (krausSuper D)
  have hKnorm : ‖K‖ ≤ 1 := super_opNorm_le_one D hD hP hfix
  have hvnorm : ‖K v‖ ≤ ‖v‖ := by
    exact (K.le_opNorm v).trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hKnorm (norm_nonneg v))
  have hKv : K v = WithLp.toLp 2 (fun ij : n × n => krausChannel D X ij.1 ij.2) := by
    dsimp [K, v]
    congr 1
    funext ij
    exact krausSuper_mulVec D X ij.1 ij.2
  rw [entryEnergy_eq_vectorization_norm_sq, entryEnergy_eq_vectorization_norm_sq, ← hKv]
  exact pow_le_pow_left₀ (norm_nonneg _) hvnorm 2

open scoped Matrix.Norms.Frobenius in
/-- The same contraction in the explicitly scoped Frobenius norm. -/
theorem channel_frobeniusNorm_le (D : ι → Matrix n n ℂ)
    (hD : ∀ a, (D a).IsHermitian) {P : Matrix n n ℂ}
    (hP : P.PosDef) (hfix : krausChannel D P = P) (X : Matrix n n ℂ) :
    ‖krausChannel D X‖ ≤ ‖X‖ := by
  have h := channel_entryEnergy_le D hD hP hfix X
  rw [entryEnergy_eq_frobeniusNorm_sq, entryEnergy_eq_frobeniusNorm_sq] at h
  nlinarith [norm_nonneg (krausChannel D X), norm_nonneg X]

/-- The unnormalized Hilbert--Schmidt trace formulation of the same estimate. -/
theorem channel_hilbertSchmidt_trace_le (D : ι → Matrix n n ℂ)
    (hD : ∀ a, (D a).IsHermitian) {P : Matrix n n ℂ}
    (hP : P.PosDef) (hfix : krausChannel D P = P) (X : Matrix n n ℂ) :
    realTrace ((krausChannel D X)ᴴ * krausChannel D X) ≤ realTrace (Xᴴ * X) := by
  simpa only [entryEnergy_eq_realTrace_adjoint_mul] using
    channel_entryEnergy_le D hD hP hfix X

end KrausContraction
end MatrixSpencer
