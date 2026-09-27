import MatrixSpencer.SuperoperatorCoordinates
import MatrixSpencer.WeightedKraus

/-!
# The actual Jordan-whitened force frame

Its complex Gram is the complexification of the physical real Gram.
In particular the real covariance cap incurs no dimension or factor loss
in this whitening step.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder
open Matrix

noncomputable section

namespace MatrixSpencer

variable {ι κ n : Type*} [Fintype ι] [Fintype κ] [Fintype n]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq n]

omit [Fintype ι] [Fintype n] [DecidableEq n] [DecidableEq ι] [DecidableEq κ] in
theorem matrixSandwichGram_entry (U : Matrix κ ι ℂ) (J : Matrix κ κ ℂ) (a b : ι) :
    (Uᴴ * J * U) a b = star (fun i => U i a) ⬝ᵥ (J *ᵥ fun i => U i b) := by
  rw [Matrix.mul_assoc]
  rfl

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [DecidableEq n] in
theorem trace_jordan_pairing {P A B : Matrix n n ℂ}
    (hP : P.IsHermitian) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    Matrix.trace (Aᴴ * (P * B + B * P)) =
      2 * (realTrace (P * A * B) : ℂ) := by
  have hstar : star (Matrix.trace (P * A * B)) = Matrix.trace (P * B * A) := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      hP.eq, hA.eq, hB.eq]
    simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm (B * A) P
  have h₁ : Matrix.trace (A * (P * B)) = Matrix.trace (P * B * A) := Matrix.trace_mul_comm _ _
  have h₂ : Matrix.trace (A * (B * P)) = Matrix.trace (P * A * B) := by
    simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm (A * B) P
  rw [hA.eq, Matrix.mul_add, Matrix.trace_add, h₁, h₂, ← hstar]
  simpa only [realTrace, RCLike.re_eq_complex_re, Complex.star_def, Complex.ofReal_mul, Complex.ofReal_ofNat, add_comm] using
    Complex.add_conj (Matrix.trace (P * A * B))

omit [Fintype κ] [DecidableEq κ] in
/-- Before taking the positive square root, the Jordan Gram has the exact physical value. -/
theorem jordanSuper_krausGram {P : Matrix n n ℂ} (hP : P.IsHermitian)
    (D : ι → Matrix n n ℂ) (hD : ∀ a, (D a).IsHermitian) :
    (krausSynthesis D)ᴴ * jordanSuper P * krausSynthesis D =
      (2 : ℝ) • realMatrixEmbedding (physicalRealGram P D) := by
  ext a b
  rw [matrixSandwichGram_entry]
  change star (matrixVector (D a)) ⬝ᵥ (jordanSuper P *ᵥ matrixVector (D b)) = _
  rw [jordanSuper_mulVec, matrixUnvector_vector, matrixVector_dotProduct,
    trace_jordan_pairing hP (hD a) (hD b)]
  rfl

/-- The actual force columns are 2^(-1/2) times the positive Jordan square root. -/
def jordanForceSynthesis (P : Matrix n n ℂ) (D : ι → Matrix n n ℂ) : Matrix (n × n) ι ℂ :=
  (Real.sqrt 2)⁻¹ • (CFC.sqrt (jordanSuper P) * krausSynthesis D)

/-- Its complex Gram is exactly the real physical Gram, complexified. -/
theorem jordanForceSynthesis_gram {P : Matrix n n ℂ} (hP : P.PosDef)
    (D : ι → Matrix n n ℂ) (hD : ∀ a, (D a).IsHermitian) :
    (jordanForceSynthesis P D)ᴴ * jordanForceSynthesis P D =
      realMatrixEmbedding (physicalRealGram P D) := by
  have hJ := jordanSuper_posDef hP
  have hc : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (2 : ℝ)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  simp only [jordanForceSynthesis, Matrix.conjTranspose_smul, star_trivial,
    Matrix.conjTranspose_mul, (CFC.sqrt_nonneg (jordanSuper P)).posSemidef.isHermitian.eq,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, hc]
  have heq : (krausSynthesis D)ᴴ * CFC.sqrt (jordanSuper P) *
      (CFC.sqrt (jordanSuper P) * krausSynthesis D) =
      (krausSynthesis D)ᴴ * jordanSuper P * krausSynthesis D := by
    calc
      _ = (krausSynthesis D)ᴴ * (CFC.sqrt (jordanSuper P) * CFC.sqrt (jordanSuper P)) *
          krausSynthesis D := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [CFC.sqrt_mul_sqrt_self (jordanSuper P) hJ.posSemidef.nonneg]
  rw [heq, jordanSuper_krausGram hP.isHermitian D hD, smul_smul]
  norm_num

/-- The same cap controls the physical synthesis operator in Loewner order. -/
theorem jordanForceSynthesis_cap {P : Matrix n n ℂ} (hP : P.PosDef)
    (D : ι → Matrix n n ℂ) (hD : ∀ a, (D a).IsHermitian) {t : ℝ} (ht : 0 ≤ t)
    (hcap : physicalRealGram P D ≤ algebraMap ℝ (Matrix ι ι ℝ) t) :
    jordanForceSynthesis P D * (jordanForceSynthesis P D)ᴴ ≤
      algebraMap ℝ (Matrix (n × n) (n × n) ℂ) t := by
  apply synthesis_cap_of_gram_cap (jordanForceSynthesis P D) ht
  rw [jordanForceSynthesis_gram hP D hD]
  simpa only [realMatrixEmbedding_algebraMap] using realMatrixEmbedding_mono hcap

/-- The physical force frame as an actual positive complex superoperator. -/
def jordanForceFrame (P : Matrix n n ℂ) (D : ι → Matrix n n ℂ) :
    Matrix (n × n) (n × n) ℂ := jordanForceSynthesis P D * (jordanForceSynthesis P D)ᴴ

omit [DecidableEq ι] in
theorem jordanForceFrame_posSemidef (P : Matrix n n ℂ) (D : ι → Matrix n n ℂ) :
    (jordanForceFrame P D).PosSemidef := Matrix.posSemidef_self_mul_conjTranspose _

theorem jordanForceFrame_trace {P : Matrix n n ℂ} (hP : P.PosDef)
    (D : ι → Matrix n n ℂ) (hD : ∀ a, (D a).IsHermitian) :
    realTrace (jordanForceFrame P D) = realTrace (physicalRealGram P D) := by
  have ht := congrArg (fun z : ℂ => z.re)
    (Matrix.trace_mul_comm (jordanForceSynthesis P D) (jordanForceSynthesis P D)ᴴ)
  change realTrace (jordanForceFrame P D) =
    realTrace ((jordanForceSynthesis P D)ᴴ * jordanForceSynthesis P D) at ht
  rw [ht, jordanForceSynthesis_gram hP D hD]
  simp only [realTrace, Matrix.trace, Matrix.diag, realMatrixEmbedding_apply,
    map_sum, RCLike.re_to_real, RCLike.re_eq_complex_re, Complex.ofReal_re]

/-- The frame trace budget follows from the actual fixed-point equation. -/
theorem jordanForceFrame_trace_of_fixedPoint {P : Matrix n n ℂ} (hP : P.PosDef)
    (D : ι → Matrix n n ℂ) (hD : ∀ a, (D a).IsHermitian)
    (hfix : krausChannel D P = P) : realTrace (jordanForceFrame P D) = realTrace P := by
  rw [jordanForceFrame_trace hP D hD]
  have hsource : (∑ a, D a * P * D a) = P := by
    simpa only [krausChannel, fun a => (hD a).eq] using hfix
  have ht := realTrace_kraus_sum D P
  rw [hsource] at ht
  rw [ht]
  change (∑ a, realTrace (P * D a * D a)) = _
  simp only [Matrix.mul_sum, realTrace_sum, Matrix.mul_assoc]

end MatrixSpencer
