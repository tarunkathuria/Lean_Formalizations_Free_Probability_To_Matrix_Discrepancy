import MatrixSpencer.JordanFrame
import MatrixSpencer.JordanWhitening

/-!
# Exact frame trace identities

The superoperator trace is converted to a sum of physical matrix pairings.
All factors of two from the observed-force normalization are retained.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder
open Matrix

noncomputable section
namespace MatrixSpencer

variable {ι m n : Type*} [Fintype ι] [Fintype m] [Fintype n]
  [DecidableEq ι] [DecidableEq m] [DecidableEq n]

omit [Fintype n] [DecidableEq n] [DecidableEq m] [DecidableEq ι] in
theorem frameTrace_eq_sandwich (U : Matrix m ι ℂ) (Q : Matrix m m ℂ) :
    realTrace ((U * Uᴴ) * Q) = realTrace (Uᴴ * Q * U) := by
  exact congrArg RCLike.re ((Matrix.trace_mul_cycle U Uᴴ Q).trans (Matrix.trace_mul_cycle Q U Uᴴ))

omit [Fintype n] [DecidableEq n] [DecidableEq m] [DecidableEq ι] in
theorem frameTrace_eq_sum (U : Matrix m ι ℂ) (Q : Matrix m m ℂ) :
    realTrace ((U * Uᴴ) * Q) =
      ∑ a, RCLike.re (star (fun i => U i a) ⬝ᵥ (Q *ᵥ fun i => U i a)) := by
  rw [frameTrace_eq_sandwich]
  simp only [realTrace, Matrix.trace, Matrix.diag, map_sum, matrixSandwichGram_entry]

omit [Fintype m] [DecidableEq m] [DecidableEq ι] in
/-- The observed frame normalization contributes exactly one half to the response sum. -/
theorem jordanForceFrame_trace_eq_half_sum (P : Matrix n n ℂ)
    (D : ι → Matrix n n ℂ) (Q : Matrix (n × n) (n × n) ℂ) :
    realTrace (jordanForceFrame P D * Q) = (2 : ℝ)⁻¹ *
      ∑ a, RCLike.re (star (CFC.sqrt (jordanSuper P) *ᵥ matrixVector (D a)) ⬝ᵥ
        (Q *ᵥ (CFC.sqrt (jordanSuper P) *ᵥ matrixVector (D a)))) := by
  rw [jordanForceFrame, frameTrace_eq_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  change RCLike.re (star ((Real.sqrt 2)⁻¹ • (CFC.sqrt (jordanSuper P) *ᵥ matrixVector (D a))) ⬝ᵥ
    (Q *ᵥ ((Real.sqrt 2)⁻¹ • (CFC.sqrt (jordanSuper P) *ᵥ matrixVector (D a))))) = _
  rw [star_smul, star_trivial, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul,
    RCLike.smul_re, RCLike.smul_re, ← mul_assoc]
  rw [← mul_inv, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

omit [Fintype m] [DecidableEq m] [Fintype ι] [DecidableEq ι] in
/-- Cancelling the adjacent Jordan factors leaves exactly one half of the unwhitened Gram. -/
theorem jordanForceSynthesis_inverse_sandwich {P : Matrix n n ℂ} (hP : P.PosDef)
    (D : ι → Matrix n n ℂ) (Q : Matrix (n × n) (n × n) ℂ) :
    (jordanForceSynthesis P D)ᴴ *
      (transportInverseSqrt (jordanSuper P) * Q * transportInverseSqrt (jordanSuper P)) *
        jordanForceSynthesis P D =
      (2 : ℝ)⁻¹ • ((krausSynthesis D)ᴴ * Q * krausSynthesis D) := by
  have hJ := jordanSuper_posDef hP
  have hc : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (2 : ℝ)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  simp only [jordanForceSynthesis, Matrix.conjTranspose_smul, star_trivial,
    Matrix.conjTranspose_mul, hJ.posDef_sqrt.isHermitian.eq,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, hc]
  congr 1
  calc
    _ = (krausSynthesis D)ᴴ * (CFC.sqrt (jordanSuper P) * transportInverseSqrt (jordanSuper P)) *
      Q * (transportInverseSqrt (jordanSuper P) * CFC.sqrt (jordanSuper P)) * krausSynthesis D := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [sqrt_mul_transportInverseSqrt hJ, transportInverseSqrt_mul_sqrt hJ,
      Matrix.mul_one, Matrix.mul_one]

omit [Fintype m] [DecidableEq m] [DecidableEq ι] in
theorem jordanForceFrame_inverse_pairing {P : Matrix n n ℂ} (hP : P.PosDef)
    (D : ι → Matrix n n ℂ) (Q : Matrix (n × n) (n × n) ℂ) :
    realTrace (jordanForceFrame P D *
      (transportInverseSqrt (jordanSuper P) * Q * transportInverseSqrt (jordanSuper P))) =
      (2 : ℝ)⁻¹ * realTrace ((krausSynthesis D)ᴴ * Q * krausSynthesis D) := by
  rw [jordanForceFrame, frameTrace_eq_sandwich, jordanForceSynthesis_inverse_sandwich hP,
    realTrace_smul]

omit [Fintype ι] [DecidableEq ι] [Fintype m] [DecidableEq m] in
def tsallisPairSuper (θ : ℝ) (P R : Matrix n n ℂ) : Matrix (n × n) (n × n) ℂ :=
  θ⁻¹ • (twoSidedSuper P R + twoSidedSuper R P)

omit [Fintype ι] [DecidableEq ι] [Fintype m] [DecidableEq m] in
theorem tsallisPairSuper_posDef {θ : ℝ} (hθ : 0 < θ)
    {P R : Matrix n n ℂ} (hP : P.PosDef) (hR : R.PosDef) :
    (tsallisPairSuper θ P R).PosDef :=
  ((twoSidedSuper_posDef hP hR).add (twoSidedSuper_posDef hR hP)).smul (inv_pos.mpr hθ)

omit [Fintype ι] [DecidableEq ι] [Fintype m] [DecidableEq m] in
theorem balancedTsallisInverseSuper_eq_pair (θ : ℝ) (S Z : Matrix n n ℂ) :
    balancedTsallisInverseSuper θ S Z = tsallisPairSuper θ (balancedDensity S Z) (balancedRoot S Z) := rfl

omit [Fintype ι] [DecidableEq ι] [Fintype m] [DecidableEq m] in
/-- The two physical multiplication terms have equal trace on Hermitian inputs. -/
theorem tsallisPairSuper_quadratic (θ : ℝ) (P R : Matrix n n ℂ)
    {X : Matrix n n ℂ} (hX : X.IsHermitian) :
    RCLike.re (star (matrixVector X) ⬝ᵥ (tsallisPairSuper θ P R *ᵥ matrixVector X)) =
      2 * θ⁻¹ * realTrace (R * X * P * X) := by
  rw [tsallisPairSuper, Matrix.smul_mulVec, Matrix.add_mulVec,
    dotProduct_smul, RCLike.smul_re, dotProduct_add, map_add, twoSidedSuper_mulVec,
    twoSidedSuper_mulVec, matrixUnvector_vector, matrixVector_dotProduct, matrixVector_dotProduct]
  change θ⁻¹ * (realTrace (Xᴴ * (P * X * R)) + realTrace (Xᴴ * (R * X * P))) = _
  rw [hX.eq]
  have h₁ : realTrace (X * (P * X * R)) = realTrace (R * X * P * X) := by
    simpa only [Matrix.mul_assoc] using realTrace_mul_comm (X * P * X) R
  have h₂ : realTrace (X * (R * X * P)) = realTrace (R * X * P * X) := by
    simpa only [Matrix.mul_assoc] using realTrace_mul_comm X (R * X * P)
  rw [h₁, h₂]
  ring

omit [Fintype m] [DecidableEq m] [DecidableEq ι] in
theorem tsallisPairSuper_synthesis_trace (θ : ℝ) (P R : Matrix n n ℂ)
    (D : ι → Matrix n n ℂ) (hD : ∀ a, (D a).IsHermitian) :
    realTrace ((krausSynthesis D)ᴴ * tsallisPairSuper θ P R * krausSynthesis D) =
      2 * θ⁻¹ * ∑ a, realTrace (R * D a * P * D a) := by
  rw [← frameTrace_eq_sandwich, frameTrace_eq_sum]
  change (∑ a, RCLike.re (star (matrixVector (D a)) ⬝ᵥ
    (tsallisPairSuper θ P R *ᵥ matrixVector (D a)))) = _
  simp only [tsallisPairSuper_quadratic θ P R (hD _), Finset.mul_sum]

omit [Fintype m] [DecidableEq m] in
/-- The Tsallis-only frame response is the exact physical quadratic sum. -/
theorem jordanForceFrame_regularizer_pairing {θ : ℝ} (hθ : 0 < θ)
    {P R : Matrix n n ℂ} (hP : P.PosDef) (hR : R.PosDef)
    (E : ι → Matrix n n ℂ) (hE : ∀ a, (E a).IsHermitian) :
    realTrace (jordanForceFrame P E *
      (whitenedRegularizer (jordanSuper P) (tsallisPairSuper θ P R))⁻¹) =
      θ⁻¹ * ∑ a, realTrace (R * E a * P * E a) := by
  rw [whitenedRegularizer_inv (tsallisPairSuper_posDef hθ hP hR),
    jordanForceFrame_inverse_pairing hP, tsallisPairSuper_synthesis_trace θ P R E hE]
  ring

omit [Fintype m] [DecidableEq m] [DecidableEq ι] [DecidableEq n] in
theorem krausSuper_mul_synthesis (D E : ι → Matrix n n ℂ) :
    krausSuper D * krausSynthesis E = krausSynthesis (fun a => krausChannel D (E a)) := by
  ext ij a
  exact congrFun (krausSuper_matrixVector D (E a)) ij

omit [Fintype m] [DecidableEq m] in
/-- The full coupled high response keeps the channel and inverse in their original order. -/
theorem jordanForceFrame_coupling_pairing {θ : ℝ} (hθ : 0 < θ)
    {P R : Matrix n n ℂ} (hP : P.PosDef) (hR : R.PosDef)
    (D E : ι → Matrix n n ℂ) (hD : ∀ a, (D a).IsHermitian)
    (hE : ∀ a, (E a).IsHermitian) :
    realTrace (jordanForceFrame P E *
      (whitenedChannel (jordanSuper P) (krausSuper D) *
        (whitenedRegularizer (jordanSuper P) (tsallisPairSuper θ P R))⁻¹ *
          (whitenedChannel (jordanSuper P) (krausSuper D))ᴴ)) =
      θ⁻¹ * ∑ a, realTrace (R * krausChannel D (E a) * P * krausChannel D (E a)) := by
  have hJ := jordanSuper_posDef hP
  have hK := KrausContraction.super_hermitian D hD
  rw [whitened_coupling_eq hJ hK (tsallisPairSuper_posDef hθ hP hR)]
  have heq : transportInverseSqrt (jordanSuper P) * krausSuper D * tsallisPairSuper θ P R *
      krausSuper D * transportInverseSqrt (jordanSuper P) =
      transportInverseSqrt (jordanSuper P) * (krausSuper D * tsallisPairSuper θ P R * krausSuper D) *
        transportInverseSqrt (jordanSuper P) := by simp only [Matrix.mul_assoc]
  rw [heq, jordanForceFrame_inverse_pairing hP]
  have hg : (krausSynthesis E)ᴴ * (krausSuper D * tsallisPairSuper θ P R * krausSuper D) *
      krausSynthesis E = (krausSynthesis (fun a => krausChannel D (E a)))ᴴ *
        tsallisPairSuper θ P R * krausSynthesis (fun a => krausChannel D (E a)) := by
    rw [← krausSuper_mul_synthesis D E, Matrix.conjTranspose_mul, hK.eq]
    simp only [Matrix.mul_assoc]
  have hh : ∀ a, (krausChannel D (E a)).IsHermitian := by
    intro a
    rw [Matrix.IsHermitian, ← KrausContraction.channel_adjoint, (hE a).eq]
  rw [hg, tsallisPairSuper_synthesis_trace θ P R _ hh]
  ring

end MatrixSpencer
