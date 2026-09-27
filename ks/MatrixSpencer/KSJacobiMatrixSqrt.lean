import MatrixSpencer.KSJacobiTraceSqrt
import MatrixSpencer.SignedLift

/-!
# Matrix square-root reports computed by the finite real Jacobi run

The report consists of the accumulated rotations and scalar square roots
of the computed diagonal. The positive matrix square root appears only
in the specification. No positive lower bound on the input is required.
-/

open Matrix
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section
namespace MatrixSpencer.KSJacobiMatrixSqrt

open KSJacobiTraceSqrt
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem embedding_reflects_posSemidef (A : Matrix ι ι ℝ)
    (hA : (realMatrixEmbedding A).PosSemidef) : A.PosSemidef := by
  refine ⟨?_, ?_⟩
  · ext i j
    have h := congrFun (congrFun hA.isHermitian i) j
    have hr := congrArg Complex.re h
    simpa [Matrix.conjTranspose_apply] using hr
  · intro x
    have h := hA.re_dotProduct_nonneg (fun i => (x i : ℂ))
    simpa [dotProduct, Matrix.mulVec, Complex.mul_re] using h

theorem embedding_reflects_le {A B : Matrix ι ι ℝ}
    (h : realMatrixEmbedding A ≤ realMatrixEmbedding B) : A ≤ B := by
  apply Matrix.le_iff.mpr
  apply embedding_reflects_posSemidef
  simpa only [map_sub] using Matrix.le_iff.mp h

theorem real_sqrt_mono {A B : Matrix ι ι ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hAB : A ≤ B) : CFC.sqrt A ≤ CFC.sqrt B := by
  letI : CStarAlgebra (Matrix ι ι ℂ) := {}
  apply embedding_reflects_le
  rw [← embedding_sqrt A hA, ← embedding_sqrt B hB]
  exact CFC.sqrt_le_sqrt _ _ (realMatrixEmbedding_mono hAB)

theorem sqrt_shift_le (A : Matrix ι ι ℝ) (hA : A.PosSemidef) {τ : ℝ} (hτ : 0 ≤ τ) :
    CFC.sqrt (A + τ • 1) ≤ CFC.sqrt A + Real.sqrt τ • (1 : Matrix ι ι ℝ) := by
  let S := CFC.sqrt A + Real.sqrt τ • (1 : Matrix ι ι ℝ)
  have hS : S.PosSemidef := (CFC.sqrt_nonneg A).posSemidef.add
    (Matrix.PosSemidef.one.smul (Real.sqrt_nonneg τ))
  have hSS : (S * S).PosSemidef := by
    simpa only [hS.isHermitian.eq] using Matrix.posSemidef_conjTranspose_mul_self S
  have hle : A + τ • 1 ≤ S * S := by
    apply Matrix.le_iff.mpr
    rw [show S * S - (A + τ • 1) = (2 * Real.sqrt τ) • CFC.sqrt A from sqrt_shift_square A hA hτ]
    exact (CFC.sqrt_nonneg A).posSemidef.smul (by positivity)
  have h := real_sqrt_mono (hA.add (Matrix.PosSemidef.one.smul hτ)) hSS hle
  rwa [CFC.sqrt_mul_self S hS.nonneg] at h

theorem real_hermitian_norm_le [Nonempty ι] {A : Matrix ι ι ℝ} (hA : A.IsHermitian)
    {r : ℝ} (hl : -(r • (1 : Matrix ι ι ℝ)) ≤ A) (hu : A ≤ r • (1 : Matrix ι ι ℝ)) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖ ≤ (Fintype.card ι : ℝ) * r := by
  letI : CStarAlgebra (Matrix ι ι ℂ) := {}
  have hEA : (realMatrixEmbedding A).IsHermitian := by
    ext i j
    have h := congrArg Complex.ofReal (congrFun (congrFun hA i) j)
    simpa [Matrix.conjTranspose_apply] using h
  have hscalar (s : ℝ) : realMatrixEmbedding (s • (1 : Matrix ι ι ℝ)) =
      s • (1 : Matrix ι ι ℂ) := by
    simpa only [Algebra.algebraMap_eq_smul_one] using realMatrixEmbedding_algebraMap (ι := ι) s
  have hlE := realMatrixEmbedding_mono hl
  have huE := realMatrixEmbedding_mono hu
  rw [map_neg, hscalar] at hlE
  rw [hscalar] at huE
  have hnorm := hermitian_norm_le_of_order hEA hlE huE
  have hr : 0 ≤ r := (norm_nonneg _).trans hnorm
  have hentry (i j : ι) : |A i j| ≤ r := by
    have hi := PiLp.norm_apply_le
      (Matrix.toEuclideanCLM (𝕜 := ℂ) (realMatrixEmbedding A) (EuclideanSpace.single j 1)) i
    have hj := (Matrix.toEuclideanCLM (𝕜 := ℂ) (realMatrixEmbedding A)).le_opNorm
      (EuclideanSpace.single j 1)
    have h := hi.trans hj
    have hcol : (Matrix.toEuclideanCLM (𝕜 := ℂ) (realMatrixEmbedding A)
        (EuclideanSpace.single j 1)) i = (realMatrixEmbedding A) i j := by
      change ((realMatrixEmbedding A) *ᵥ Pi.single j 1) i = _
      rw [Matrix.mulVec_single_one]
      rfl
    rw [hcol] at h
    have he : ‖(realMatrixEmbedding A) i j‖ ≤ ‖realMatrixEmbedding A‖ := by
      simpa [Matrix.ofLp_toEuclideanCLM, EuclideanSpace.ofLp_single,
        Matrix.mulVec_single_one, EuclideanSpace.norm_single] using h
    simpa only [realMatrixEmbedding_apply, Complex.norm_real, Real.norm_eq_abs] using he.trans hnorm
  apply (KSJacobiRayleigh.operatorNorm_le_frobenius A).trans
  apply (Real.sqrt_le_iff).mpr
  refine ⟨mul_nonneg (Nat.cast_nonneg _) hr, ?_⟩
  calc
    KSJacobiStep.frobeniusEnergy A ≤ ∑ _i : ι, ∑ _j : ι, r ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      nlinarith [sq_abs (A i j), hentry i j, abs_nonneg (A i j)]
    _ = ((Fintype.card ι : ℝ) * r) ^ 2 := by simp; ring

/-- A conservative operator Hölder bound follows from two Loewner bounds
and entrywise estimates. It remains valid at singular matrices. -/
theorem sqrt_operator_error [Nonempty ι] {A B : Matrix ι ι ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) {τ : ℝ}
    (herr : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (A - B)‖ ≤ τ) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt A - CFC.sqrt B)‖ ≤
      (Fintype.card ι : ℝ) * Real.sqrt τ := by
  have hτ : 0 ≤ τ := (norm_nonneg _).trans herr
  have hsym (M : Matrix ι ι ℝ) (hM : M.PosSemidef) : M.IsSymm := by
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose, star_trivial] using hM.isHermitian
  have hab := le_scalar_of_operatorNorm (A - B) ((hsym A hA).sub (hsym B hB)) herr
  have hba := le_scalar_of_operatorNorm (B - A) ((hsym B hB).sub (hsym A hA))
    (by simpa only [← neg_sub A B, map_neg, norm_neg] using herr)
  have h₁ : CFC.sqrt A ≤ CFC.sqrt B + Real.sqrt τ • (1 : Matrix ι ι ℝ) :=
    (real_sqrt_mono hA (hB.add (Matrix.PosSemidef.one.smul hτ))
      (by simpa only [add_comm] using (sub_le_iff_le_add).mp hab)).trans (sqrt_shift_le B hB hτ)
  have h₂ : CFC.sqrt B ≤ CFC.sqrt A + Real.sqrt τ • (1 : Matrix ι ι ℝ) :=
    (real_sqrt_mono hB (hA.add (Matrix.PosSemidef.one.smul hτ))
      (by simpa only [add_comm] using (sub_le_iff_le_add).mp hba)).trans (sqrt_shift_le A hA hτ)
  apply real_hermitian_norm_le
    ((CFC.sqrt_nonneg A).posSemidef.isHermitian.sub (CFC.sqrt_nonneg B).posSemidef.isHermitian)
  · exact neg_le_sub_iff_le_add.mpr h₂
  · exact sub_le_iff_le_add.mpr (by simpa only [add_comm] using h₁)

theorem orthogonal_conjugation_operatorNorm_le (E U : Matrix ι ι ℝ)
    (hU : Uᵀ * U = 1) (hU' : U * Uᵀ = 1) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (U * E * Uᵀ)‖ ≤
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) E‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro v
  simp only [map_mul, ContinuousLinearMap.mul_apply]
  rw [KSJacobiRayleigh.orthogonal_preserves_norm U hU]
  calc
    _ ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) E‖ *
        ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Uᵀ v‖ :=
      (Matrix.toEuclideanCLM (𝕜 := ℝ) E).le_opNorm _
    _ = _ := by
      rw [KSJacobiRayleigh.orthogonal_preserves_norm Uᵀ
        (by simpa only [Matrix.transpose_transpose] using hU')]

variable {d : ℕ}

def diagonalReport (A : Matrix (Fin d) (Fin d) ℝ) (ν : ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.diagonal (fun i => max 0 (KSJacobiRayleigh.finalMatrix A (tolerance d ν) i i))

/-- The returned matrix uses only the computed basis, scalar roots, and
matrix multiplication. -/
def report (A : Matrix (Fin d) (Fin d) ℝ) (ν : ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  let U := KSJacobiRayleigh.finalBasis A (tolerance d ν)
  U * Matrix.diagonal (fun i => Real.sqrt (max 0
    (KSJacobiRayleigh.finalMatrix A (tolerance d ν) i i))) * Uᵀ

def surrogate (A : Matrix (Fin d) (Fin d) ℝ) (ν : ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  let U := KSJacobiRayleigh.finalBasis A (tolerance d ν)
  U * diagonalReport A ν * Uᵀ

theorem diagonalReport_posSemidef (A : Matrix (Fin d) (Fin d) ℝ) (ν : ℝ) :
    (diagonalReport A ν).PosSemidef := Matrix.PosSemidef.diagonal (fun _ => le_max_left _ _)

theorem report_posSemidef (A : Matrix (Fin d) (Fin d) ℝ) (ν : ℝ) :
    (report A ν).PosSemidef := by
  have h := (Matrix.PosSemidef.diagonal (fun i : Fin d => Real.sqrt_nonneg
    (max 0 (KSJacobiRayleigh.finalMatrix A (tolerance d ν) i i)))).mul_mul_conjTranspose_same
      (KSJacobiRayleigh.finalBasis A (tolerance d ν))
  simpa only [report, Matrix.conjTranspose, star_trivial] using h

theorem surrogate_posSemidef (A : Matrix (Fin d) (Fin d) ℝ) (ν : ℝ) :
    (surrogate A ν).PosSemidef := by
  simpa only [surrogate, Matrix.conjTranspose, star_trivial] using
    (diagonalReport_posSemidef A ν).mul_mul_conjTranspose_same
      (KSJacobiRayleigh.finalBasis A (tolerance d ν))

theorem report_eq_sqrt_surrogate (A : Matrix (Fin d) (Fin d) ℝ) (ν : ℝ) :
    report A ν = CFC.sqrt (surrogate A ν) := by
  let U := KSJacobiRayleigh.finalBasis A (tolerance d ν)
  have hU : Uᵀ * U = 1 := KSJacobiIteration.accumulatedBasis_transpose_mul A _
  have hs := sqrt_orthogonal_conjugation (diagonalReport A ν) Uᵀ
    (diagonalReport_posSemidef A ν) (by simpa only [Matrix.transpose_transpose] using hU)
  simp only [Matrix.transpose_transpose] at hs
  rw [diagonalReport, sqrt_diagonal _ (fun _ => le_max_left _ _)] at hs
  exact hs.symm

theorem surrogate_error (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.PosSemidef)
    {ν : ℝ} (hν : 0 < ν) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (A - surrogate A ν)‖ ≤ tolerance d ν := by
  have hsym : A.IsSymm := by
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose, star_trivial] using hA.isHermitian
  have ht : 0 < tolerance d ν := by unfold tolerance; positivity
  let B := KSJacobiRayleigh.finalMatrix A (tolerance d ν)
  let U := KSJacobiRayleigh.finalBasis A (tolerance d ν)
  have hU : Uᵀ * U = 1 := KSJacobiIteration.accumulatedBasis_transpose_mul A _
  have hU' : U * Uᵀ = 1 := KSJacobiIteration.accumulatedBasis_mul_transpose A _
  have hB : B = Uᵀ * A * U := KSJacobiIteration.run_eq_conjugation A _
  have hBP : B.PosSemidef := by
    rw [hB]
    simpa only [Matrix.conjTranspose, star_trivial] using hA.conjTranspose_mul_mul_same U
  have hdiag (i : Fin d) : 0 ≤ B i i := by simpa using hBP.2 (Pi.single i 1)
  have hD : diagonalReport A ν = KSJacobiRayleigh.diagonalPart B := by
    change Matrix.diagonal (fun i => max 0 (B i i)) = Matrix.diagonal (fun i => B i i)
    congr 1
    funext i
    exact max_eq_right (hdiag i)
  have he : A - surrogate A ν = U * (B - KSJacobiRayleigh.diagonalPart B) * Uᵀ := by
    unfold surrogate
    change A - U * diagonalReport A ν * Uᵀ = _
    rw [hD, Matrix.mul_sub, Matrix.sub_mul, hB]
    simp only [Matrix.mul_assoc, ← Matrix.mul_assoc U Uᵀ, hU', Matrix.one_mul,
      Matrix.mul_one]
  rw [he]
  exact (orthogonal_conjugation_operatorNorm_le _ U hU hU').trans
    ((KSJacobiRayleigh.residual_operatorNorm B).trans
      (KSJacobiIteration.run_offDiagonalFrobenius_accuracy A hsym ht))

/-- Complete numerical matrix-root accuracy, including singular and empty
inputs. The tolerance is chosen explicitly from `ν` and the dimension. -/
theorem report_accuracy (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.PosSemidef)
    {ν : ℝ} (hν : 0 < ν) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (report A ν - CFC.sqrt A)‖ ≤ ν := by
  by_cases hd : 0 < d
  · letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    have he := sqrt_operator_error hA (surrogate_posSemidef A ν) (surrogate_error A hA hν)
    rw [← report_eq_sqrt_surrogate, Fintype.card_fin] at he
    have hn : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (report A ν - CFC.sqrt A)‖ =
        ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt A - report A ν)‖ := by
      rw [← neg_sub (CFC.sqrt A) (report A ν), map_neg, norm_neg]
    rw [hn]
    have hs : Real.sqrt (tolerance d ν) = ν / ((d : ℝ) + 1) := by
      exact Real.sqrt_sq (by positivity)
    rw [hs] at he
    apply he.trans
    have hden : 0 < (d : ℝ) + 1 := by positivity
    rw [← mul_div_assoc]
    exact (div_le_iff₀ hden).mpr (by nlinarith)
  · have hz : d = 0 := by omega
    subst d
    have he : report A ν - CFC.sqrt A = 0 := Subsingleton.elim _ _
    simpa only [he, map_zero, norm_zero] using hν.le

end MatrixSpencer.KSJacobiMatrixSqrt
