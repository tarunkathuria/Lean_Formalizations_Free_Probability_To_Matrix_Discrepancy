import MatrixSpencer.KSJacobiNorm
import MatrixSpencer.KSComplexTraceSqrt

/-!
# A finite upper operator-norm report for complex Hermitian matrices

Realification preserves the operator norm exactly. The routine therefore
realifies the entries, performs the actual finite real Jacobi norm routine,
and returns its certified upper report. Complex spectral parameters and
matrix-norm oracles do not occur in the numerical definition.
-/

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSComplexNorm

open KSComplexTraceSqrt
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def realVector (v : EuclideanSpace ℂ ι) : EuclideanSpace ℝ (ι ⊕ ι) :=
  WithLp.toLp 2 (Sum.elim (fun i => (v i).re) (fun i => (v i).im))

omit [DecidableEq ι] in
theorem realVector_norm (v : EuclideanSpace ℂ ι) : ‖realVector v‖ = ‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [PiLp.norm_sq_eq_of_L2, realVector, PiLp.toLp_apply,
    Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Real.norm_eq_abs, sq_abs,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

omit [Fintype ι] [DecidableEq ι] in
theorem realVector_surjective : Function.Surjective (realVector (ι := ι)) := by
  intro w
  refine ⟨WithLp.toLp 2 (fun i => (⟨w (.inl i), w (.inr i)⟩ : ℂ)), ?_⟩
  ext (i | i) <;> rfl

theorem realVector_action (A : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι) :
    realVector (Matrix.toEuclideanCLM (𝕜 := ℂ) A v) =
      Matrix.toEuclideanCLM (𝕜 := ℝ) (realification A) (realVector v) := by
  ext (i | i)
  · change ((A *ᵥ WithLp.ofLp v) i).re =
      (realification A *ᵥ WithLp.ofLp (realVector v)) (.inl i)
    simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, realVector,
      Complex.mul_re, sub_eq_add_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  · change ((A *ᵥ WithLp.ofLp v) i).im =
      (realification A *ᵥ WithLp.ofLp (realVector v)) (.inr i)
    simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, realVector,
      Complex.mul_im, Finset.sum_add_distrib, add_comm]

/-- The scalar field changes from complex to real, but the operator norm
does not: every real vector in the two blocks represents one complex vector. -/
theorem realification_norm (A : Matrix ι ι ℂ) : ‖realification A‖ = ‖A‖ := by
  change ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (realification A)‖ =
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro w
    obtain ⟨v, rfl⟩ := realVector_surjective w
    rw [← realVector_action, realVector_norm, realVector_norm]
    exact (Matrix.toEuclideanCLM (𝕜 := ℂ) A).le_opNorm v
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro v
    have h := (Matrix.toEuclideanCLM (𝕜 := ℝ) (realification A)).le_opNorm (realVector v)
    rw [← realVector_action, realVector_norm, realVector_norm] at h
    exact h

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

def reindexVector (e : κ ≃ ι) (v : EuclideanSpace ℝ ι) : EuclideanSpace ℝ κ :=
  WithLp.toLp 2 (fun i => v (e i))

omit [DecidableEq ι] [DecidableEq κ] in
theorem reindexVector_norm (e : κ ≃ ι) (v : EuclideanSpace ℝ ι) :
    ‖reindexVector e v‖ = ‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [PiLp.norm_sq_eq_of_L2, reindexVector, PiLp.toLp_apply]
  exact e.sum_comp (fun i => ‖v i‖ ^ 2)

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
theorem reindexVector_surjective (e : κ ≃ ι) : Function.Surjective (reindexVector e) := by
  intro w
  refine ⟨WithLp.toLp 2 (fun i => w (e.symm i)), ?_⟩
  ext i
  change w (e.symm (e i)) = w i
  exact congrArg w (e.symm_apply_apply i)

theorem reindexVector_action (e : κ ≃ ι) (A : Matrix ι ι ℝ) (v : EuclideanSpace ℝ ι) :
    reindexVector e (Matrix.toEuclideanCLM (𝕜 := ℝ) A v) =
      Matrix.toEuclideanCLM (𝕜 := ℝ) (A.submatrix e e) (reindexVector e v) := by
  ext i
  change (∑ j, A (e i) j * v j) = ∑ j, A (e i) (e j) * v (e j)
  exact (e.sum_comp (fun j => A (e i) j * v j)).symm

theorem submatrix_equiv_norm (e : κ ≃ ι) (A : Matrix ι ι ℝ) :
    ‖A.submatrix e e‖ = ‖A‖ := by
  change ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (A.submatrix e e)‖ =
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro w
    obtain ⟨v, rfl⟩ := reindexVector_surjective e w
    rw [← reindexVector_action, reindexVector_norm, reindexVector_norm]
    exact (Matrix.toEuclideanCLM (𝕜 := ℝ) A).le_opNorm v
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro v
    have h := (Matrix.toEuclideanCLM (𝕜 := ℝ) (A.submatrix e e)).le_opNorm (reindexVector e v)
    rw [← reindexVector_action, reindexVector_norm, reindexVector_norm] at h
    exact h

variable {d : ℕ}

theorem realificationFin_norm (A : Matrix (Fin d) (Fin d) ℂ) :
    ‖realificationFin A‖ = ‖A‖ := by
  rw [realificationFin, submatrix_equiv_norm, realification_norm]

theorem realificationFin_symmetric (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) :
    (realificationFin A).IsSymm := by
  have hr : (realification A).IsSymm := by
    change (realification A)ᵀ = realification A
    rw [← realification_conjTranspose, hA.eq]
  exact hr.submatrix _

/-- The actual report is evaluated by real arithmetic on `2d` coordinates. -/
def report (A : Matrix (Fin d) (Fin d) ℂ) (ν : ℝ) : ℝ :=
  KSJacobiNorm.report (realificationFin A) ν

theorem report_accuracy (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian)
    {ν : ℝ} (hν : 0 < ν) : ‖A‖ ≤ report A ν ∧ report A ν ≤ ‖A‖ + ν := by
  have h := KSJacobiNorm.report_accuracy (realificationFin A)
    (realificationFin_symmetric A hA) hν
  rwa [realificationFin_norm] at h

/-- Acceptance by the computed upper report certifies the true norm. -/
theorem accepted_norm_le (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian)
    {ν a : ℝ} (hν : 0 < ν) (haccept : report A ν ≤ a) : ‖A‖ ≤ a :=
  (report_accuracy A hA hν).1.trans haccept

/-- A true-norm good event is detected whenever the allowance covers the
specified numerical tolerance. There is no exact norm test in the routine. -/
theorem good_norm_accepted (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian)
    {ν a b : ℝ} (hν : 0 < ν) (hgood : ‖A‖ ≤ a) (hallow : a + ν ≤ b) :
    report A ν ≤ b :=
  ((report_accuracy A hA hν).2.trans (add_le_add_right hgood ν)).trans hallow

/-- A single real comparison of the computed upper report. -/
def accepts (A : Matrix (Fin d) (Fin d) ℂ) (ν a : ℝ) : Bool :=
  decide (report A ν ≤ a)

theorem accepts_sound (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian)
    {ν a : ℝ} (hν : 0 < ν) (haccept : accepts A ν a = true) : ‖A‖ ≤ a :=
  accepted_norm_le A hA hν (of_decide_eq_true haccept)

theorem accepts_complete (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian)
    {ν a b : ℝ} (hν : 0 < ν) (hgood : ‖A‖ ≤ a) (hallow : a + ν ≤ b) :
    accepts A ν b = true :=
  decide_eq_true (good_norm_accepted A hA hν hgood hallow)

/-- The `7 K δ` good event from the finite-walk theorem passes the actual
`9 K δ` acceptance comparison, at tolerance `2 K δ`. -/
theorem seven_accepted_at_nine (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian)
    {K δ : ℝ} (hK : 0 < K) (hδ : 0 < δ) (hgood : ‖A‖ ≤ 7 * K * δ) :
    accepts A (2 * K * δ) (9 * K * δ) = true :=
  accepts_complete A hA (by positivity) hgood (by nlinarith)

end MatrixSpencer.KSComplexNorm
