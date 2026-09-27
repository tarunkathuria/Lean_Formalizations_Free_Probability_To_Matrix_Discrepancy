import MatrixSpencer.BalancedTransport
import MatrixSpencer.Sylvester
import MatrixSpencer.KSFullManuscriptFidelityBlockUpper
import MatrixSpencer.FidelityDerivative
import MatrixSpencer.KSComplexOwnerPerturbation

/-! Relative transport estimates independent of the least source eigenvalue. -/
open Matrix MatrixSpencer
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace AugmentedHigherRankKS.BalancedRegularity
variable {n : Type*} [Fintype n] [DecidableEq n]
local instance balancedRegCStar : CStarAlgebra (Matrix n n ℂ) := {}

/-- Frobenius norm with an explicit name so it cannot be confused with the
operator norm used for physical discrepancy matrices. -/
def frob (M : Matrix n n ℂ) : ℝ := Real.sqrt (entryEnergy M)

open scoped Matrix.Norms.Frobenius in
theorem frob_eq_norm (M : Matrix n n ℂ) : frob M = ‖M‖ := by
  rw [frob, entryEnergy_eq_frobeniusNorm_sq, Real.sqrt_sq (norm_nonneg _)]

theorem frob_nonneg (M : Matrix n n ℂ) : 0 ≤ frob M := Real.sqrt_nonneg _

open scoped Matrix.Norms.Frobenius in
theorem frob_add_le (A B : Matrix n n ℂ) : frob (A+B) ≤ frob A + frob B := by
  simp only [frob_eq_norm]
  exact norm_add_le A B

theorem frob_mul_le (A B : Matrix n n ℂ) : frob (A*B) ≤ frob A * frob B := by
  simp only [frob_eq_norm]
  exact Matrix.frobenius_norm_mul A B

@[simp] theorem frob_adjoint (A : Matrix n n ℂ) : frob Aᴴ = frob A := by
  simp only [frob_eq_norm, Matrix.frobenius_norm_conjTranspose]

open scoped Matrix.Norms.Frobenius in
@[simp] theorem frob_neg (A : Matrix n n ℂ) : frob (-A) = frob A := by
  simp only [frob_eq_norm, norm_neg]

def weighted (P U : Matrix n n ℂ) : Matrix n n ℂ :=
  transportInverseSqrt P * U * CFC.sqrt P

def relative (P X : Matrix n n ℂ) : Matrix n n ℂ :=
  transportInverseSqrt P * X * transportInverseSqrt P

theorem weighted_mul {P : Matrix n n ℂ} (hP : P.PosDef) (U V : Matrix n n ℂ) :
    weighted P (U*V) = weighted P U * weighted P V := by
  simp only [weighted, Matrix.mul_assoc, ← Matrix.mul_assoc (CFC.sqrt P)
    (transportInverseSqrt P), sqrt_mul_transportInverseSqrt hP, Matrix.one_mul]

/-- The trace of a square is unchanged by this similarity, even though the
weighted matrix is generally not Hermitian. -/
theorem weighted_square_trace {P U : Matrix n n ℂ} (hP : P.PosDef) :
    realTrace (weighted P U * weighted P U) = realTrace (U*U) := by
  rw [← weighted_mul hP]
  unfold weighted
  rw [realTrace_mul_cycle, sqrt_mul_transportInverseSqrt hP, Matrix.one_mul]

theorem relative_sylvester {P U : Matrix n n ℂ} (hP : P.PosDef)
    (hU : U.IsHermitian) : relative P (sylvester P U) = weighted P U + (weighted P U)ᴴ := by
  have hR := hP.posDef_sqrt.isHermitian.eq
  have hJ := (transportInverseSqrt_posDef hP).isHermitian.eq
  simp only [relative, weighted, sylvester_apply, Matrix.mul_add, Matrix.add_mul,
    Matrix.conjTranspose_mul, hR, hJ, hU.eq]
  rw [← Matrix.mul_assoc (transportInverseSqrt P) P,
    transportInverseSqrt_mul_self_matrix hP]
  simp only [Matrix.mul_assoc, matrix_mul_transportInverseSqrt hP]
  abel

/-- A useful identity behind the source-gap-independent estimate. -/
theorem energy_add_adjoint (T : Matrix n n ℂ) :
    entryEnergy (T+Tᴴ) = 2*entryEnergy T + 2*realTrace (T*T) := by
  have hc := KSFullManuscriptFidelityBlockUpper.realTrace_conjTranspose (T*T)
  simp only [Matrix.conjTranspose_mul] at hc
  simp only [entryEnergy_eq_realTrace_adjoint_mul, Matrix.conjTranspose_add,
    Matrix.conjTranspose_conjTranspose, Matrix.add_mul, Matrix.mul_add, realTrace_add]
  rw [realTrace_mul_comm T Tᴴ, hc]
  ring

/-- A relative right-hand side controls the weighted Hilbert--Schmidt norm
of the actual Sylvester solution, without a minimum-eigenvalue factor. -/
theorem weighted_sylvester_energy {P U : Matrix n n ℂ} (hP : P.PosDef)
    (hU : U.IsHermitian) :
    entryEnergy (weighted P U) ≤ entryEnergy (relative P (sylvester P U)) := by
  rw [relative_sylvester hP hU, energy_add_adjoint, weighted_square_trace hP]
  have hu : 0 ≤ realTrace (U*U) := by
    simpa only [hU.eq] using realTrace_conjTranspose_mul_self_nonneg U
  linarith [entryEnergy_nonneg (weighted P U)]

theorem weighted_sylvester_frob {P U : Matrix n n ℂ} (hP : P.PosDef)
    (hU : U.IsHermitian) : frob (weighted P U) ≤ frob (relative P (sylvester P U)) :=
  Real.sqrt_le_sqrt (weighted_sylvester_energy hP hU)

theorem weighted_inverse_frob {P X : Matrix n n ℂ} (hP : P.PosDef)
    (hX : X.IsHermitian) :
    frob (weighted P ((sylvesterEquiv P hP).symm X)) ≤ frob (relative P X) := by
  simpa only [sylvester_inverse_solve] using
    weighted_sylvester_frob hP (sylvester_inverse_isHermitian P hP hX)

/-- Operator norm is bounded by the explicit Frobenius norm. -/
theorem norm_le_frob (A : Matrix n n ℂ) : ‖A‖ ≤ frob A := by
  have hn := posSemidef_norm_le_realTrace (Matrix.posSemidef_conjTranspose_mul_self A)
  have he := CStarRing.norm_star_mul_self (x := A)
  rw [Matrix.star_eq_conjTranspose] at he
  rw [he, ← entryEnergy_eq_realTrace_adjoint_mul] at hn
  exact (Real.le_sqrt (norm_nonneg A) (entryEnergy_nonneg A)).mpr (by nlinarith)

theorem trace_weighted_bound {P : Matrix n n ℂ} (hP : P.PosSemidef)
    (W : Matrix n n ℂ) : |realTrace (P*W)| ≤ realTrace P * frob W := by
  have hr := Complex.abs_re_le_norm (Matrix.trace (P*W))
  have hn := KSComplexOwnerPerturbation.norm_trace_mul_le P W hP
  have hf := mul_le_mul_of_nonneg_right (norm_le_frob W) (realTrace_nonneg hP)
  exact hr.trans (hn.trans (hf.trans_eq (mul_comm _ _)))

theorem frob_le_sqrt_card_mul_norm (A : Matrix n n ℂ) :
    frob A ≤ Real.sqrt (Fintype.card n : ℝ) * ‖A‖ := by
  have hAA := Matrix.posSemidef_conjTranspose_mul_self A
  have hord := hAA.isHermitian.isSelfAdjoint.le_algebraMap_norm_self
  have he := CStarRing.norm_star_mul_self (x := A)
  rw [Matrix.star_eq_conjTranspose] at he
  rw [he, Algebra.algebraMap_eq_smul_one] at hord
  have ht := realTrace_mul_mono (Matrix.PosSemidef.one : (1 : Matrix n n ℂ).PosSemidef) hord
  simp only [Matrix.one_mul, realTrace_smul, ← entryEnergy_eq_realTrace_adjoint_mul] at ht
  have hone : realTrace (1 : Matrix n n ℂ) = Fintype.card n := by
    simp [realTrace, Matrix.trace, Matrix.diag]
  rw [hone] at ht
  have hs := Real.sqrt_le_sqrt ht
  calc
    frob A ≤ Real.sqrt ((‖A‖ * ‖A‖) * (Fintype.card n : ℝ)) := hs
    _ = Real.sqrt (Fintype.card n : ℝ) * ‖A‖ := by
      rw [Real.sqrt_mul (mul_self_nonneg ‖A‖), Real.sqrt_mul_self (norm_nonneg A)]
      ring


@[simp] theorem relative_add (P A B : Matrix n n ℂ) :
    relative P (A+B) = relative P A + relative P B := by
  simp only [relative, Matrix.mul_add, Matrix.add_mul]

@[simp] theorem relative_sub (P A B : Matrix n n ℂ) :
    relative P (A-B) = relative P A - relative P B := by
  simp only [relative, Matrix.mul_sub, Matrix.sub_mul]

@[simp] theorem relative_smul (P A : Matrix n n ℂ) (r : ℝ) :
    relative P (r • A) = r • relative P A := by
  simp only [relative, Matrix.mul_smul, Matrix.smul_mul]

theorem frob_sub_le (A B : Matrix n n ℂ) : frob (A-B) ≤ frob A + frob B := by
  simpa only [sub_eq_add_neg, frob_neg] using frob_add_le A (-B)

theorem relative_left_product {P : Matrix n n ℂ} (hP : P.PosDef)
    (U X : Matrix n n ℂ) : relative P (U*X) = weighted P U * relative P X := by
  simp only [relative, weighted, Matrix.mul_assoc,
    ← Matrix.mul_assoc (CFC.sqrt P) (transportInverseSqrt P),
    sqrt_mul_transportInverseSqrt hP, Matrix.one_mul]

theorem relative_right_product {P U : Matrix n n ℂ} (hP : P.PosDef)
    (hU : U.IsHermitian) (X : Matrix n n ℂ) :
    relative P (X*U) = relative P X * (weighted P U)ᴴ := by
  simp only [relative, weighted, Matrix.conjTranspose_mul,
    hP.posDef_sqrt.isHermitian.eq, (transportInverseSqrt_posDef hP).isHermitian.eq, hU.eq,
    Matrix.mul_assoc, ← Matrix.mul_assoc (transportInverseSqrt P) (CFC.sqrt P),
    transportInverseSqrt_mul_sqrt hP, Matrix.one_mul]

@[simp] theorem relative_base {P : Matrix n n ℂ} (hP : P.PosDef) : relative P P = 1 := by
  rw [relative, transportInverseSqrt_mul_self_matrix hP, sqrt_mul_transportInverseSqrt hP]

theorem relative_triple_base {P V : Matrix n n ℂ} (hP : P.PosDef)
    (hV : V.IsHermitian) (U : Matrix n n ℂ) :
    relative P (U*P*V) = weighted P U * (weighted P V)ᴴ := by
  rw [relative_right_product hP hV, relative_left_product hP, relative_base hP, Matrix.mul_one]

theorem relative_triple {P V : Matrix n n ℂ} (hP : P.PosDef)
    (hV : V.IsHermitian) (U X : Matrix n n ℂ) :
    relative P (U*X*V) = weighted P U * relative P X * (weighted P V)ᴴ := by
  rw [relative_right_product hP hV, relative_left_product hP]

theorem relative_left_product_bound {P : Matrix n n ℂ} (hP : P.PosDef)
    (U X : Matrix n n ℂ) :
    frob (relative P (U*X)) ≤ frob (weighted P U) * frob (relative P X) := by
  rw [relative_left_product hP]
  exact frob_mul_le _ _

theorem relative_right_product_bound {P U : Matrix n n ℂ} (hP : P.PosDef)
    (hU : U.IsHermitian) (X : Matrix n n ℂ) :
    frob (relative P (X*U)) ≤ frob (relative P X) * frob (weighted P U) := by
  rw [relative_right_product hP hU]
  simpa only [frob_adjoint] using frob_mul_le (relative P X) (weighted P U)ᴴ

theorem relative_triple_base_bound {P V : Matrix n n ℂ} (hP : P.PosDef)
    (hV : V.IsHermitian) (U : Matrix n n ℂ) :
    frob (relative P (U*P*V)) ≤ frob (weighted P U) * frob (weighted P V) := by
  rw [relative_triple_base hP hV]
  simpa only [frob_adjoint] using frob_mul_le (weighted P U) (weighted P V)ᴴ

theorem relative_triple_bound {P V : Matrix n n ℂ} (hP : P.PosDef)
    (hV : V.IsHermitian) (U X : Matrix n n ℂ) :
    frob (relative P (U*X*V)) ≤
      frob (weighted P U) * frob (relative P X) * frob (weighted P V) := by
  rw [relative_triple hP hV]
  have h := (frob_mul_le (weighted P U * relative P X) (weighted P V)ᴴ).trans
    (mul_le_mul_of_nonneg_right (frob_mul_le _ _) (frob_nonneg _))
  simpa only [frob_adjoint] using h


theorem first_coefficient_bound {P U A B : Matrix n n ℂ} (hP : P.PosDef)
    (hU : U.IsHermitian) (heq : sylvester P U = A-B) :
    frob (weighted P U) ≤ frob (relative P A) + frob (relative P B) := by
  have h := weighted_sylvester_frob hP hU
  rw [heq, relative_sub] at h
  exact h.trans (frob_sub_le _ _)

theorem second_coefficient_bound {P U V A B C : Matrix n n ℂ} (hP : P.PosDef)
    (hU : U.IsHermitian) (hV : V.IsHermitian)
    (heq : sylvester P V = A-B-U*C-C*U-U*P*U) :
    frob (weighted P V) ≤ frob (relative P A) + frob (relative P B) +
      2 * frob (weighted P U) * frob (relative P C) + frob (weighted P U)^2 := by
  have h := weighted_sylvester_frob hP hV
  rw [heq] at h
  simp only [relative_sub] at h
  have h1 := frob_sub_le (relative P A) (relative P B)
  have h2 := frob_sub_le (relative P A-relative P B) (relative P (U*C))
  have h3 := frob_sub_le (relative P A-relative P B-relative P (U*C)) (relative P (C*U))
  have h4 := frob_sub_le (relative P A-relative P B-relative P (U*C)-relative P (C*U))
    (relative P (U*P*U))
  have hl := relative_left_product_bound hP U C
  have hr := relative_right_product_bound hP hU C
  have hq := relative_triple_base_bound hP hU U
  nlinarith

theorem third_coefficient_bound {P U V W A B C D : Matrix n n ℂ} (hP : P.PosDef)
    (hU : U.IsHermitian) (hV : V.IsHermitian) (hW : W.IsHermitian)
    (heq : sylvester P W = A-B-U*D-D*U-V*C-C*V-U*C*U-U*P*V-V*P*U) :
    frob (weighted P W) ≤ frob (relative P A) + frob (relative P B) +
      2*frob (weighted P U)*frob (relative P D) +
      2*frob (weighted P V)*frob (relative P C) +
      frob (weighted P U)^2*frob (relative P C) +
      2*frob (weighted P U)*frob (weighted P V) := by
  have h := weighted_sylvester_frob hP hW
  rw [heq] at h
  simp only [relative_sub] at h
  have h1 := frob_sub_le (relative P A) (relative P B)
  have h2 := frob_sub_le (relative P A-relative P B) (relative P (U*D))
  have h3 := frob_sub_le (relative P A-relative P B-relative P (U*D)) (relative P (D*U))
  have h4 := frob_sub_le (relative P A-relative P B-relative P (U*D)-relative P (D*U))
    (relative P (V*C))
  have h5 := frob_sub_le
    (relative P A-relative P B-relative P (U*D)-relative P (D*U)-relative P (V*C))
    (relative P (C*V))
  have h6 := frob_sub_le
    (relative P A-relative P B-relative P (U*D)-relative P (D*U)-relative P (V*C)-relative P (C*V))
    (relative P (U*C*U))
  have h7 := frob_sub_le
    (relative P A-relative P B-relative P (U*D)-relative P (D*U)-relative P (V*C)-relative P (C*V)-relative P (U*C*U))
    (relative P (U*P*V))
  have h8 := frob_sub_le
    (relative P A-relative P B-relative P (U*D)-relative P (D*U)-relative P (V*C)-relative P (C*V)-relative P (U*C*U)-relative P (U*P*V))
    (relative P (V*P*U))
  have ha := relative_left_product_bound hP U D
  have hb := relative_right_product_bound hP hU D
  have hc := relative_left_product_bound hP V C
  have hd := relative_right_product_bound hP hV C
  have he := relative_triple_bound hP hU U C
  have hf := relative_triple_base_bound hP hV U
  have hg := relative_triple_base_bound hP hU V
  nlinarith


/-- Scalar accounting for the first three normalized transport coefficients. -/
theorem three_coefficient_scalars {d L u v w : ℝ}
    (hd : 1 ≤ d) (hL : 0 ≤ L) (hu0 : 0 ≤ u) (hv0 : 0 ≤ v)
    (hu : u ≤ 2*d*L)
    (hv : v ≤ 2*d*L^2 + 2*u*(d*L) + u^2)
    (hw : w ≤ 2*d*L^3 + 2*u*(d*L^2) + 2*v*(d*L) + u^2*(d*L) + 2*u*v) :
    u ≤ 2*d*L ∧ v ≤ 10*d^2*L^2 ∧ w ≤ 70*d^3*L^3 := by
  have hd0 : 0 ≤ d := by linarith
  have hd2 : d ≤ d^2 := by nlinarith
  have hv' : v ≤ 10*d^2*L^2 := by
    calc
      v ≤ 2*d*L^2 + 2*u*(d*L) + u^2 := hv
      _ ≤ 2*d*L^2 + 2*(2*d*L)*(d*L) + (2*d*L)^2 := by gcongr
      _ ≤ 10*d^2*L^2 := by nlinarith [mul_le_mul_of_nonneg_right hd2 (sq_nonneg L)]
  refine ⟨hu, hv', ?_⟩
  have hd3 : d^2 ≤ d^3 := by nlinarith [mul_nonneg (sq_nonneg d) (sub_nonneg.mpr hd)]
  calc
    w ≤ 2*d*L^3 + 2*u*(d*L^2) + 2*v*(d*L) + u^2*(d*L) + 2*u*v := hw
    _ ≤ 2*d*L^3 + 2*(2*d*L)*(d*L^2) + 2*(10*d^2*L^2)*(d*L) +
        (2*d*L)^2*(d*L) + 2*(2*d*L)*(10*d^2*L^2) := by gcongr
    _ ≤ 70*d^3*L^3 := by
      nlinarith [mul_le_mul_of_nonneg_right (hd2.trans hd3) (pow_nonneg hL 3),
        mul_le_mul_of_nonneg_right hd3 (pow_nonneg hL 3)]

/-- Physical trace pairings can be bounded in the balanced coordinates. -/
theorem trace_product_balanced {P : Matrix n n ℂ} (hP : P.PosDef)
    (X U : Matrix n n ℂ) :
    realTrace (X*U) = realTrace (P*weighted P U*relative P X) := by
  have hid : P*weighted P U*relative P X = CFC.sqrt P * U * X * transportInverseSqrt P := by
    simp only [weighted, relative, Matrix.mul_assoc,
      ← Matrix.mul_assoc P (transportInverseSqrt P), matrix_mul_transportInverseSqrt hP,
      ← Matrix.mul_assoc (CFC.sqrt P) (transportInverseSqrt P),
      sqrt_mul_transportInverseSqrt hP, Matrix.one_mul]
  rw [hid, realTrace_mul_cycle]
  simp only [← Matrix.mul_assoc, transportInverseSqrt_mul_sqrt hP, Matrix.one_mul]
  rw [realTrace_mul_comm]

theorem trace_relative {P : Matrix n n ℂ} (hP : P.PosDef) (X : Matrix n n ℂ) :
    realTrace X = realTrace (P*relative P X) := by
  have h := trace_product_balanced hP X (1 : Matrix n n ℂ)
  simpa only [weighted, Matrix.mul_one, transportInverseSqrt_mul_sqrt hP] using h

theorem trace_relative_bound {P : Matrix n n ℂ} (hP : P.PosDef) (X : Matrix n n ℂ) :
    |realTrace X| ≤ realTrace P * frob (relative P X) := by
  rw [trace_relative hP X]
  exact trace_weighted_bound hP.posSemidef _

theorem trace_product_bound {P : Matrix n n ℂ} (hP : P.PosDef) (X U : Matrix n n ℂ) :
    |realTrace (X*U)| ≤ realTrace P * (frob (weighted P U)*frob (relative P X)) := by
  rw [trace_product_balanced hP X U, Matrix.mul_assoc]
  exact (trace_weighted_bound hP.posSemidef _).trans
    (mul_le_mul_of_nonneg_left (frob_mul_le _ _) (realTrace_nonneg hP.posSemidef))

theorem trace_base_product_bound {P : Matrix n n ℂ} (hP : P.PosDef) (U : Matrix n n ℂ) :
    |realTrace (P*U)| ≤ realTrace P * frob (weighted P U) := by
  rw [trace_product_balanced hP P U, relative_base hP, Matrix.mul_one]
  exact trace_weighted_bound hP.posSemidef _


theorem transport_jet_bounds {P U V W A₁ A₂ A₃ B₁ B₂ B₃ : Matrix n n ℂ}
    (hP : P.PosDef) (hU : U.IsHermitian) (hV : V.IsHermitian) (hW : W.IsHermitian)
    (he1 : sylvester P U = A₁-B₁)
    (he2 : sylvester P V = A₂-B₂-U*B₁-B₁*U-U*P*U)
    (he3 : sylvester P W = A₃-B₃-U*B₂-B₂*U-V*B₁-B₁*V-U*B₁*U-U*P*V-V*P*U)
    {d L : ℝ} (hd : 1 ≤ d) (hL : 0 ≤ L)
    (hA1 : frob (relative P A₁) ≤ d*L) (hB1 : frob (relative P B₁) ≤ d*L)
    (hA2 : frob (relative P A₂) ≤ d*L^2) (hB2 : frob (relative P B₂) ≤ d*L^2)
    (hA3 : frob (relative P A₃) ≤ d*L^3) (hB3 : frob (relative P B₃) ≤ d*L^3) :
    frob (weighted P U) ≤ 2*d*L ∧ frob (weighted P V) ≤ 10*d^2*L^2 ∧
      frob (weighted P W) ≤ 70*d^3*L^3 := by
  have h1 := first_coefficient_bound hP hU he1
  have h2 := second_coefficient_bound hP hU hV he2
  have h3 := third_coefficient_bound hP hU hV hW he3
  apply three_coefficient_scalars hd hL (frob_nonneg _) (frob_nonneg _)
  · linarith
  · have hc := mul_le_mul_of_nonneg_left hB1
      (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (frob_nonneg (weighted P U)))
    linarith
  · have hc := mul_le_mul_of_nonneg_left hB2
      (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (frob_nonneg (weighted P U)))
    have hd' := mul_le_mul_of_nonneg_left hB1
      (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (frob_nonneg (weighted P V)))
    have he := mul_le_mul_of_nonneg_left hB1 (sq_nonneg (frob (weighted P U)))
    linarith

/-- Bounds for the trace coefficients in `2 Tr(B(t) R(t))`. -/
theorem fidelity_first_coefficient_bound {P : Matrix n n ℂ} (hP : P.PosDef)
    (U B : Matrix n n ℂ) :
    |2*realTrace (B+P*U)| ≤ 2*realTrace P*(frob (relative P B)+frob (weighted P U)) := by
  rw [realTrace_add, abs_mul, abs_of_pos (by norm_num : (0:ℝ)<2)]
  have h := abs_add_le (realTrace B) (realTrace (P*U))
  have hb := trace_relative_bound hP B
  have hu := trace_base_product_bound hP U
  nlinarith

theorem fidelity_second_coefficient_bound {P : Matrix n n ℂ} (hP : P.PosDef)
    (U V B₁ B₂ : Matrix n n ℂ) :
    |2*realTrace (B₂+B₁*U+P*V)| ≤ 2*realTrace P*
      (frob (relative P B₂)+frob (weighted P U)*frob (relative P B₁)+frob (weighted P V)) := by
  simp only [realTrace_add, abs_mul, abs_of_pos (by norm_num : (0:ℝ)<2)]
  have h1 := abs_add_le (realTrace B₂) (realTrace (B₁*U))
  have h2 := abs_add_le (realTrace B₂+realTrace (B₁*U)) (realTrace (P*V))
  have hb := trace_relative_bound hP B₂
  have hu := trace_product_bound hP B₁ U
  have hv := trace_base_product_bound hP V
  nlinarith

theorem fidelity_third_coefficient_bound {P : Matrix n n ℂ} (hP : P.PosDef)
    (U V W B₁ B₂ B₃ : Matrix n n ℂ) :
    |2*realTrace (B₃+B₂*U+B₁*V+P*W)| ≤ 2*realTrace P*
      (frob (relative P B₃)+frob (weighted P U)*frob (relative P B₂)+
       frob (weighted P V)*frob (relative P B₁)+frob (weighted P W)) := by
  simp only [realTrace_add, abs_mul, abs_of_pos (by norm_num : (0:ℝ)<2)]
  have h1 := abs_add_le (realTrace B₃) (realTrace (B₂*U))
  have h2 := abs_add_le (realTrace B₃+realTrace (B₂*U)) (realTrace (B₁*V))
  have h3 := abs_add_le (realTrace B₃+realTrace (B₂*U)+realTrace (B₁*V)) (realTrace (P*W))
  have hb := trace_relative_bound hP B₃
  have hu := trace_product_bound hP B₂ U
  have hv := trace_product_bound hP B₁ V
  have hw := trace_base_product_bound hP W
  nlinarith


theorem fidelity_scalar_envelopes {d L u v w b₁ b₂ b₃ : ℝ}
    (hd : 1 ≤ d) (hL : 0 ≤ L) (hu0 : 0 ≤ u) (hv0 : 0 ≤ v)
    (hb1 : 0 ≤ b₁) (hb2 : 0 ≤ b₂)
    (hu : u ≤ 2*d*L) (hv : v ≤ 10*d^2*L^2) (hw : w ≤ 70*d^3*L^3)
    (hb1' : b₁ ≤ d*L) (hb2' : b₂ ≤ d*L^2) (hb3' : b₃ ≤ d*L^3) :
    b₁+u ≤ 100*d*L ∧ b₂+u*b₁+v ≤ (100*d*L)^2 ∧
      b₃+u*b₂+v*b₁+w ≤ (100*d*L)^3 := by
  have hd0 : 0 ≤ d := by linarith
  have hd2 : d ≤ d^2 := by nlinarith
  have hd3 : d^2 ≤ d^3 := by nlinarith [mul_nonneg (sq_nonneg d) (sub_nonneg.mpr hd)]
  refine ⟨?_, ?_, ?_⟩
  · nlinarith [mul_nonneg hd0 hL]
  · calc
      b₂+u*b₁+v ≤ d*L^2+(2*d*L)*(d*L)+10*d^2*L^2 := by gcongr
      _ ≤ (100*d*L)^2 := by
        nlinarith [mul_le_mul_of_nonneg_right hd2 (sq_nonneg L),
          mul_nonneg (sq_nonneg d) (sq_nonneg L)]
  · calc
      b₃+u*b₂+v*b₁+w ≤ d*L^3+(2*d*L)*(d*L^2)+(10*d^2*L^2)*(d*L)+70*d^3*L^3 := by
        gcongr
      _ ≤ (100*d*L)^3 := by
        nlinarith [mul_le_mul_of_nonneg_right (hd2.trans hd3) (pow_nonneg hL 3),
          mul_le_mul_of_nonneg_right hd3 (pow_nonneg hL 3),
          mul_nonneg (pow_nonneg hd0 3) (pow_nonneg hL 3)]

/-- The first three Taylor coefficients of fidelity satisfy a common
polynomial relative bound once the transport equations are instantiated. -/
theorem fidelity_jet_bounds {P U V W A₁ A₂ A₃ B₁ B₂ B₃ : Matrix n n ℂ}
    (hP : P.PosDef) (hU : U.IsHermitian) (hV : V.IsHermitian) (hW : W.IsHermitian)
    (he1 : sylvester P U = A₁-B₁)
    (he2 : sylvester P V = A₂-B₂-U*B₁-B₁*U-U*P*U)
    (he3 : sylvester P W = A₃-B₃-U*B₂-B₂*U-V*B₁-B₁*V-U*B₁*U-U*P*V-V*P*U)
    {d L : ℝ} (hd : 1 ≤ d) (hL : 0 ≤ L)
    (hA1 : frob (relative P A₁) ≤ d*L) (hB1 : frob (relative P B₁) ≤ d*L)
    (hA2 : frob (relative P A₂) ≤ d*L^2) (hB2 : frob (relative P B₂) ≤ d*L^2)
    (hA3 : frob (relative P A₃) ≤ d*L^3) (hB3 : frob (relative P B₃) ≤ d*L^3) :
    |2*realTrace (B₁+P*U)| ≤ 2*realTrace P*(100*d*L) ∧
    |2*realTrace (B₂+B₁*U+P*V)| ≤ 2*realTrace P*(100*d*L)^2 ∧
    |2*realTrace (B₃+B₂*U+B₁*V+P*W)| ≤ 2*realTrace P*(100*d*L)^3 := by
  have ht := transport_jet_bounds hP hU hV hW he1 he2 he3 hd hL hA1 hB1 hA2 hB2 hA3 hB3
  have hs := fidelity_scalar_envelopes hd hL (frob_nonneg _) (frob_nonneg _)
    (frob_nonneg _) (frob_nonneg _) ht.1 ht.2.1 ht.2.2 hB1 hB2 hB3
  have hp : 0 ≤ 2*realTrace P := mul_nonneg (by norm_num) (realTrace_nonneg hP.posSemidef)
  exact ⟨(fidelity_first_coefficient_bound hP U B₁).trans
      (mul_le_mul_of_nonneg_left hs.1 hp),
    (fidelity_second_coefficient_bound hP U V B₁ B₂).trans
      (mul_le_mul_of_nonneg_left hs.2.1 hp),
    (fidelity_third_coefficient_bound hP U V W B₁ B₂ B₃).trans
      (mul_le_mul_of_nonneg_left hs.2.2 hp)⟩


end AugmentedHigherRankKS.BalancedRegularity
