import MatrixSpencer.KSJacobiRayleigh
import MatrixSpencer.ComplexGram
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.IntegralRepresentation

/-!
# A certified trace-square-root report from the explicit real Jacobi run

The report only evaluates scalar square roots of the computed diagonal.
The positive matrix square root occurs in its specification and proof, not
in its algorithm. Singular PSD inputs require no lower eigenvalue bound.
Complexification below is only an analytic proof of real trace monotonicity;
the numerical run and report remain real.
-/

open Matrix
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section
namespace MatrixSpencer.KSJacobiTraceSqrt

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def traceSqrt (A : Matrix ι ι ℝ) : ℝ := realTrace (CFC.sqrt A)

theorem embedding_trace (A : Matrix ι ι ℝ) : realTrace (realMatrixEmbedding A) = realTrace A := by
  simp [realTrace, Matrix.trace, Matrix.diag]

theorem embedding_sqrt (A : Matrix ι ι ℝ) (hA : A.PosSemidef) :
    CFC.sqrt (realMatrixEmbedding A) = realMatrixEmbedding (CFC.sqrt A) := by
  apply CFC.sqrt_unique
  · rw [← map_mul, CFC.sqrt_mul_sqrt_self A hA.nonneg]
  · exact (realMatrixEmbedding_posSemidef _ (CFC.sqrt_nonneg A).posSemidef).nonneg

/-- Trace monotonicity of the real positive square root, including singular matrices. -/
theorem traceSqrt_mono {A B : Matrix ι ι ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hAB : A ≤ B) : traceSqrt A ≤ traceSqrt B := by
  letI : CStarAlgebra (Matrix ι ι ℂ) := {}
  have h := realTrace_nonneg (Matrix.le_iff.mp
    (CFC.sqrt_le_sqrt (realMatrixEmbedding A) (realMatrixEmbedding B) (realMatrixEmbedding_mono hAB)))
  rw [realTrace_sub, embedding_sqrt A hA, embedding_sqrt B hB, embedding_trace, embedding_trace] at h
  exact sub_nonneg.mp h

theorem sqrt_shift_square (A : Matrix ι ι ℝ) (hA : A.PosSemidef) {τ : ℝ} (hτ : 0 ≤ τ) :
    (CFC.sqrt A + Real.sqrt τ • (1 : Matrix ι ι ℝ)) *
        (CFC.sqrt A + Real.sqrt τ • (1 : Matrix ι ι ℝ)) - (A + τ • 1) =
      (2 * Real.sqrt τ) • CFC.sqrt A := by
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, Matrix.mul_one, smul_add, smul_smul, CFC.sqrt_mul_sqrt_self A hA.nonneg]
  have hs : Real.sqrt τ * Real.sqrt τ = τ := by nlinarith [Real.sq_sqrt hτ]
  rw [hs]
  module

/-- Adding a scalar shift raises trace square root by at most `d sqrt τ`. -/
theorem traceSqrt_shift_le (A : Matrix ι ι ℝ) (hA : A.PosSemidef) {τ : ℝ} (hτ : 0 ≤ τ) :
    traceSqrt (A + τ • 1) ≤ traceSqrt A + (Fintype.card ι : ℝ) * Real.sqrt τ := by
  let S := CFC.sqrt A + Real.sqrt τ • (1 : Matrix ι ι ℝ)
  have hS : S.PosSemidef := (CFC.sqrt_nonneg A).posSemidef.add
    (Matrix.PosSemidef.one.smul (Real.sqrt_nonneg τ))
  have hshift : (A + τ • 1).PosSemidef := hA.add (Matrix.PosSemidef.one.smul hτ)
  have hSS : (S * S).PosSemidef := by
    simpa only [hS.isHermitian.eq] using Matrix.posSemidef_conjTranspose_mul_self S
  have hle : A + τ • 1 ≤ S * S := by
    apply Matrix.le_iff.mpr
    rw [show S * S - (A + τ • 1) = (2 * Real.sqrt τ) • CFC.sqrt A from sqrt_shift_square A hA hτ]
    exact (CFC.sqrt_nonneg A).posSemidef.smul (by positivity)
  have ht := traceSqrt_mono hshift hSS hle
  change traceSqrt (A + τ • 1) ≤ realTrace (CFC.sqrt (S * S)) at ht
  rw [CFC.sqrt_mul_self S hS.nonneg] at ht
  change traceSqrt (A + τ • 1) ≤ realTrace (CFC.sqrt A + Real.sqrt τ • (1 : Matrix ι ι ℝ)) at ht
  rw [realTrace_add, realTrace_smul] at ht
  simpa [traceSqrt, realTrace, mul_comm] using ht

theorem traceSqrt_perturbation_of_order {A B : Matrix ι ι ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) {τ : ℝ} (hτ : 0 ≤ τ)
    (hAB : A ≤ B + τ • 1) (hBA : B ≤ A + τ • 1) :
    |traceSqrt A - traceSqrt B| ≤ (Fintype.card ι : ℝ) * Real.sqrt τ := by
  have hab := (traceSqrt_mono hA (hB.add (Matrix.PosSemidef.one.smul hτ)) hAB).trans
    (traceSqrt_shift_le B hB hτ)
  have hba := (traceSqrt_mono hB (hA.add (Matrix.PosSemidef.one.smul hτ)) hBA).trans
    (traceSqrt_shift_le A hA hτ)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem realRayleigh_le_norm_mul_sq (E : Matrix ι ι ℝ) (v : EuclideanSpace ℝ ι) :
    KSRayleighAccuracy.realRayleigh E v ≤
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) E‖ * ‖v‖ ^ 2 := by
  have hi := abs_real_inner_le_norm v (Matrix.toEuclideanCLM (𝕜 := ℝ) E v)
  have ho := (Matrix.toEuclideanCLM (𝕜 := ℝ) E).le_opNorm v
  have hp := mul_le_mul_of_nonneg_left ho (norm_nonneg v)
  have ha := le_abs_self (KSRayleighAccuracy.realRayleigh E v)
  unfold KSRayleighAccuracy.realRayleigh at ha ⊢
  nlinarith

/-- A real symmetric operator-norm cap is an actual Loewner cap. -/
theorem le_scalar_of_operatorNorm (E : Matrix ι ι ℝ) (hE : E.IsSymm) {τ : ℝ}
    (herr : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) E‖ ≤ τ) : E ≤ τ • (1 : Matrix ι ι ℝ) := by
  have hτ : 0 ≤ τ := (norm_nonneg _).trans herr
  have hEH : E.IsHermitian := by simpa only [Matrix.IsHermitian, Matrix.conjTranspose, star_trivial] using hE
  apply Matrix.le_iff.mpr
  refine ⟨(Matrix.PosSemidef.one.smul hτ).isHermitian.sub hEH, ?_⟩
  intro x
  have h := (realRayleigh_le_norm_mul_sq E (WithLp.toLp 2 x)).trans
    (mul_le_mul_of_nonneg_right herr (sq_nonneg _))
  have hnorm : ‖(WithLp.toLp 2 x : EuclideanSpace ℝ ι)‖ ^ 2 = x ⬝ᵥ x := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [PiLp.toLp_apply, Real.norm_eq_abs, sq_abs]
    simp only [dotProduct, pow_two]
  rw [KSRayleighAccuracy.realRayleigh_eq_quadratic, hnorm] at h
  simpa only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, star_trivial,
    dotProduct_sub, dotProduct_smul, smul_eq_mul] using sub_nonneg.mpr h

theorem traceSqrt_perturbation {A B : Matrix ι ι ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) {τ : ℝ}
    (herr : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (A - B)‖ ≤ τ) :
    |traceSqrt A - traceSqrt B| ≤ (Fintype.card ι : ℝ) * Real.sqrt τ := by
  have hsym (M : Matrix ι ι ℝ) (hM : M.PosSemidef) : M.IsSymm := by
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose, star_trivial] using hM.isHermitian
  have hAB := le_scalar_of_operatorNorm (A - B) ((hsym A hA).sub (hsym B hB)) herr
  have herr' : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (B - A)‖ ≤ τ := by
    simpa only [← neg_sub A B, map_neg, norm_neg] using herr
  have hBA := le_scalar_of_operatorNorm (B - A) ((hsym B hB).sub (hsym A hA)) herr'
  apply traceSqrt_perturbation_of_order hA hB ((norm_nonneg _).trans herr)
  · have h : A ≤ τ • 1 + B := (sub_le_iff_le_add).mp hAB
    simpa only [add_comm] using h
  · have h : B ≤ τ • 1 + A := (sub_le_iff_le_add).mp hBA
    simpa only [add_comm] using h

theorem sqrt_orthogonal_conjugation (A U : Matrix ι ι ℝ) (hA : A.PosSemidef)
    (hU : U * Uᵀ = 1) : CFC.sqrt (Uᵀ * A * U) = Uᵀ * CFC.sqrt A * U := by
  have hroot : (Uᵀ * CFC.sqrt A * U).PosSemidef := by
    simpa only [Matrix.conjTranspose, star_trivial] using
      (CFC.sqrt_nonneg A).posSemidef.conjTranspose_mul_mul_same U
  apply CFC.sqrt_unique _ hroot.nonneg
  calc
    _ = Uᵀ * (CFC.sqrt A * (U * Uᵀ) * CFC.sqrt A) * U := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hU, Matrix.mul_one, CFC.sqrt_mul_sqrt_self A hA.nonneg]

theorem traceSqrt_orthogonal_conjugation (A U : Matrix ι ι ℝ) (hA : A.PosSemidef)
    (hU : U * Uᵀ = 1) : traceSqrt (Uᵀ * A * U) = traceSqrt A := by
  rw [traceSqrt, sqrt_orthogonal_conjugation A U hA hU, realTrace_mul_cycle, hU, Matrix.one_mul]
  rfl

theorem sqrt_diagonal (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) :
    CFC.sqrt (Matrix.diagonal f) = Matrix.diagonal (fun i => Real.sqrt (f i)) := by
  apply CFC.sqrt_unique
  · rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact Real.mul_self_sqrt (hf i)
  · exact (Matrix.PosSemidef.diagonal (fun i => Real.sqrt_nonneg (f i))).nonneg

theorem traceSqrt_diagonalPart (A : Matrix ι ι ℝ) (hA : A.PosSemidef) :
    traceSqrt (KSJacobiRayleigh.diagonalPart A) = ∑ i, Real.sqrt (max 0 (A i i)) := by
  have hdiag (i : ι) : 0 ≤ A i i := by simpa using hA.2 (Pi.single i 1)
  simp only [traceSqrt, KSJacobiRayleigh.diagonalPart, sqrt_diagonal _ hdiag,
    realTrace, Matrix.trace_diagonal, RCLike.re_to_real, max_eq_right (hdiag _)]

variable {d : ℕ}

def tolerance (d : ℕ) (ν : ℝ) : ℝ := (ν / ((d : ℝ) + 1)) ^ 2

/-- The report executes Jacobi, clips each computed diagonal at zero, and sums scalar roots. -/
def report (A : Matrix (Fin d) (Fin d) ℝ) (ν : ℝ) : ℝ :=
  ∑ i, Real.sqrt (max 0 (KSJacobiRayleigh.finalMatrix A (tolerance d ν) i i))

theorem report_accuracy (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.PosSemidef)
    {ν : ℝ} (hν : 0 < ν) : |report A ν - traceSqrt A| ≤ ν := by
  have hsym : A.IsSymm := by
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose, star_trivial] using hA.isHermitian
  have ht : 0 < tolerance d ν := by unfold tolerance; positivity
  let B := KSJacobiRayleigh.finalMatrix A (tolerance d ν)
  let U := KSJacobiRayleigh.finalBasis A (tolerance d ν)
  have hU : U * Uᵀ = 1 := KSJacobiIteration.accumulatedBasis_mul_transpose A _
  have hB : B = Uᵀ * A * U := KSJacobiIteration.run_eq_conjugation A _
  have hBP : B.PosSemidef := by
    rw [hB]
    simpa only [Matrix.conjTranspose, star_trivial] using hA.conjTranspose_mul_mul_same U
  have hDP : (KSJacobiRayleigh.diagonalPart B).PosSemidef :=
    Matrix.PosSemidef.diagonal (fun i => by simpa using hBP.2 (Pi.single i 1))
  have herr : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (B - KSJacobiRayleigh.diagonalPart B)‖ ≤ tolerance d ν :=
    (KSJacobiRayleigh.residual_operatorNorm B).trans
      (KSJacobiIteration.run_offDiagonalFrobenius_accuracy A hsym ht)
  have herror := traceSqrt_perturbation hBP hDP herr
  rw [traceSqrt_diagonalPart B hBP, hB, traceSqrt_orthogonal_conjugation A U hA hU] at herror
  have hreport : report A ν = ∑ i, Real.sqrt (max 0 ((Uᵀ * A * U) i i)) := by
    change (∑ i, Real.sqrt (max 0 (B i i))) = _
    rw [hB]
  rw [Fintype.card_fin, ← hreport, abs_sub_comm] at herror
  have hs : Real.sqrt (tolerance d ν) = ν / ((d : ℝ) + 1) := by
    unfold tolerance
    exact Real.sqrt_sq (by positivity)
  rw [hs] at herror
  refine herror.trans ?_
  have hd : 0 < (d : ℝ) + 1 := by positivity
  have hmul : (d : ℝ) * (ν / ((d : ℝ) + 1)) = ((d : ℝ) * ν) / ((d : ℝ) + 1) := by ring
  rw [hmul]
  exact (div_le_iff₀ hd).mpr (by nlinarith)

end MatrixSpencer.KSJacobiTraceSqrt
