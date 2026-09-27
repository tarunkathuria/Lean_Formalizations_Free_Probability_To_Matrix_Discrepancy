import MatrixSpencer.GeneralizedSylvester
import MatrixSpencer.KrausContraction

/-!
# Source-gap-independent order estimates for the Sylvester inverse

The inverse is positive in the matrix order, not merely positive as a quadratic
form on matrix space. Relative input bounds therefore give weighted quadratic
energy bounds without a lower eigenvalue bound on the positive coefficient.
-/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSSylvesterOrder
variable {n : Type*} [Fintype n] [DecidableEq n]
local instance : CStarAlgebra (Matrix n n ℂ) := {}

theorem posSemidef_of_sylvester_posSemidef {Q W : Matrix n n ℂ}
    (hQ : Q.PosDef) (hW : W.IsHermitian)
    (hB : (Q * W + W * Q).PosSemidef) : W.PosSemidef := by
  rw [hW.posSemidef_iff_eigenvalues_nonneg]
  intro i
  change 0 ≤ hW.eigenvalues i
  let v : n → ℂ := hW.eigenvectorBasis i
  have hv : v ≠ 0 := by
    intro hv
    apply hW.eigenvectorBasis.orthonormal.ne_zero i
    exact PiLp.ext (congrFun hv)
  have he : W *ᵥ v = hW.eigenvalues i • v := hW.mulVec_eigenvectorBasis i
  have hpos := hQ.re_dotProduct_pos hv
  have hnonneg := hB.re_dotProduct_nonneg v
  have hleft : star v ⬝ᵥ (W *ᵥ (Q *ᵥ v)) =
      (hW.eigenvalues i) • (star v ⬝ᵥ (Q *ᵥ v)) := by
    have hs : star v ᵥ* W = star (W *ᵥ v) := by rw [star_mulVec, hW.eq]
    rw [dotProduct_mulVec, hs, he, star_smul, star_trivial, smul_dotProduct]
  simp only [Matrix.add_mulVec, dotProduct_add] at hnonneg
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, he, Matrix.mulVec_smul,
    dotProduct_smul, hleft] at hnonneg
  change 0 ≤ ((hW.eigenvalues i) • (star v ⬝ᵥ Q *ᵥ v) +
    (hW.eigenvalues i) • (star v ⬝ᵥ Q *ᵥ v)).re at hnonneg
  simp only [Complex.add_re, Complex.real_smul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hnonneg
  change 0 < (star v ⬝ᵥ Q *ᵥ v).re at hpos
  nlinarith

/-- The proved Sylvester inverse preserves positive semidefiniteness. -/
theorem inverse_posSemidef (Q : Matrix n n ℂ) (hQ : Q.PosDef)
    {B : Matrix n n ℂ} (hB : B.PosSemidef) :
    ((sylvesterEquiv Q hQ).symm B).PosSemidef := by
  apply posSemidef_of_sylvester_posSemidef hQ
    (sylvester_inverse_isHermitian Q hQ hB.isHermitian)
  change (sylvester Q ((sylvesterEquiv Q hQ).symm B)).PosSemidef
  rwa [sylvester_inverse_solve]

/-- Matrix-order monotonicity of the actual Sylvester inverse. -/
theorem inverse_mono (Q : Matrix n n ℂ) (hQ : Q.PosDef)
    {A B : Matrix n n ℂ} (hAB : A ≤ B) :
    (sylvesterEquiv Q hQ).symm A ≤ (sylvesterEquiv Q hQ).symm B := by
  rw [← sub_nonneg]
  have h := inverse_posSemidef Q hQ (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hAB))
  simpa only [map_sub] using h.nonneg

/-- A relative right-hand-side bound controls the Sylvester solution without
any lower bound on the smallest eigenvalue of `Q`. -/
theorem solution_relative_bounds {Q W : Matrix n n ℂ} (hQ : Q.PosDef)
    (hW : W.IsHermitian) (δ : ℝ)
    (hlo : -(2 * δ) • (Q * Q) ≤ Q * W + W * Q)
    (hhi : Q * W + W * Q ≤ (2 * δ) • (Q * Q)) :
    -δ • Q ≤ W ∧ W ≤ δ • Q := by
  have hδ : (δ • Q).IsHermitian := by
    change (δ • Q)ᴴ = δ • Q
    simp only [Matrix.conjTranspose_smul, star_trivial, hQ.isHermitian.eq]
  constructor
  · have h := posSemidef_of_sylvester_posSemidef hQ (hW.add hδ) (show
        (Q * (W + δ • Q) + (W + δ • Q) * Q).PosSemidef from ?_)
    · have hn := h.nonneg
      rw [← neg_le_iff_add_nonneg'] at hn
      simpa only [neg_smul, neg_neg] using neg_le_neg hn
    · apply Matrix.nonneg_iff_posSemidef.mp
      have heq : Q * (W + δ • Q) + (W + δ • Q) * Q =
          (Q * W + W * Q) - (-(2 * δ) • (Q * Q)) := by
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
          Matrix.smul_mul, neg_smul, sub_neg_eq_add]
        module
      rw [heq]
      exact sub_nonneg.mpr hlo
  · have h := posSemidef_of_sylvester_posSemidef hQ (hδ.sub hW) (show
        (Q * (δ • Q - W) + (δ • Q - W) * Q).PosSemidef from ?_)
    · exact sub_nonneg.mp h.nonneg
    · apply Matrix.nonneg_iff_posSemidef.mp
      have heq : Q * (δ • Q - W) + (δ • Q - W) * Q =
          (2 * δ) • (Q * Q) - (Q * W + W * Q) := by
        simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]
        module
      rw [heq]
      exact sub_nonneg.mpr hhi

set_option maxHeartbeats 800000 in
/-- A relative order bound gives a weighted quadratic bound, again with no
condition number or smallest-eigenvalue parameter. -/
theorem weighted_square_le {Q W : Matrix n n ℂ} (hQ : Q.PosDef)
    (hW : W.IsHermitian) {δ : ℝ} (hδ : 0 ≤ δ)
    (hlo : -δ • Q ≤ W) (hhi : W ≤ δ • Q) :
    W * Q⁻¹ * W ≤ δ ^ 2 • Q := by
  let P := CFC.sqrt Q
  let R := P⁻¹
  have hP : P.PosDef := hQ.posDef_sqrt
  have hR : R.IsHermitian := hP.isHermitian.inv
  have hPR : P * R = 1 := Matrix.mul_nonsing_inv P (P.isUnit_iff_isUnit_det.mp hP.isUnit)
  have hRP : R * P = 1 := Matrix.nonsing_inv_mul P (P.isUnit_iff_isUnit_det.mp hP.isUnit)
  have hPP : P * P = Q := CFC.sqrt_mul_sqrt_self Q hQ.posSemidef.nonneg
  have hRQ : R * Q * R = 1 := by
    rw [← hPP, ← Matrix.mul_assoc, hRP, Matrix.one_mul, hPR]
  have hRR : R * R = Q⁻¹ := by
    symm
    apply Matrix.inv_eq_left_inv
    rw [← hPP]
    calc R * R * (P * P) = R * (R * P) * P := by noncomm_ring
      _ = 1 := by rw [hRP, Matrix.mul_one, hRP]
  let C := R * W * R
  have hC : C.IsHermitian := by
    simpa only [hR.eq] using Matrix.isHermitian_mul_mul_conjTranspose R hW
  have hClo : -δ • (1 : Matrix n n ℂ) ≤ C := by
    simpa only [Matrix.mul_smul, Matrix.smul_mul, hRQ] using
      KrausContraction.congruence_mono hlo R hR
  have hChi : C ≤ δ • (1 : Matrix n n ℂ) := by
    simpa only [Matrix.mul_smul, Matrix.smul_mul, hRQ] using
      KrausContraction.congruence_mono hhi R hR
  have hn := KrausContraction.norm_le_of_order_interval hC hδ hClo hChi
  have hCC : C * C ≤ δ ^ 2 • (1 : Matrix n n ℂ) := by
    have ht : C * C ≤ ‖C‖ ^ 2 • (1 : Matrix n n ℂ) := by
      simpa only [Matrix.star_eq_conjTranspose, hC.eq, Algebra.algebraMap_eq_smul_one] using
        (CStarAlgebra.star_mul_le_algebraMap_norm_sq (a := C))
    apply ht.trans
    apply smul_le_smul_of_nonneg_right _ (Matrix.PosSemidef.one (n := n)).nonneg
    nlinarith [norm_nonneg C]
  have h := KrausContraction.congruence_mono hCC P hP.isHermitian
  have hid : P * (C * C) * P = W * Q⁻¹ * W := by
    dsimp [C]
    calc P * (R * W * R * (R * W * R)) * P =
        (P * R) * W * (R * R) * W * (R * P) := by noncomm_ring
      _ = _ := by rw [hPR, hRP, hRR, Matrix.one_mul, Matrix.mul_one]
  simpa only [hid, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hPP] using h

/-- The relative Sylvester estimate in the trace energy that occurs in the
actual fidelity Hessian. -/
theorem solution_trace_energy_le {Q W : Matrix n n ℂ} (hQ : Q.PosDef)
    (hW : W.IsHermitian) {δ : ℝ} (hδ : 0 ≤ δ)
    (hlo : -(2 * δ) • (Q * Q) ≤ Q * W + W * Q)
    (hhi : Q * W + W * Q ≤ (2 * δ) • (Q * Q)) :
    realTrace (W * Q⁻¹ * W) ≤ δ ^ 2 * realTrace Q := by
  obtain ⟨hl, hu⟩ := solution_relative_bounds hQ hW δ hlo hhi
  have h := realTrace_mul_mono (Matrix.PosSemidef.one (n := n))
    (weighted_square_le hQ hW hδ hl hu)
  simpa only [Matrix.one_mul, realTrace_smul] using h

end MatrixSpencer.KSSylvesterOrder
