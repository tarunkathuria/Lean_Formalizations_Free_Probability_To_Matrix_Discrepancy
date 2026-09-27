import MatrixSpencer.CovarianceSampler

/-!
Numerical error propagation for an approximate minimum-Rayleigh vector.
All norms of matrices below are explicitly Euclidean operator norms.
The quadratic form is used only on unit vectors. `leastRayleigh` is its
infimum over the unit sphere, so there is no assumed minimizing vector or
eigenvalue gap. For symmetric matrices this is the variational formulation
of the least eigenvalue. This file does not construct the reported matrix
or the approximate minimizing vector, and does not verify a Jacobi routine.
-/

open scoped BigOperators
open Matrix
noncomputable section
namespace MatrixSpencer.KSRayleighAccuracy

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def realRayleigh (K : Matrix ι ι ℝ) (v : EuclideanSpace ℝ ι) : ℝ :=
  inner ℝ v (Matrix.toEuclideanCLM (𝕜 := ℝ) K v)

theorem realRayleigh_eq_quadratic (K : Matrix ι ι ℝ) (v : EuclideanSpace ℝ ι) :
    realRayleigh K v = WithLp.ofLp v ⬝ᵥ (K *ᵥ WithLp.ofLp v) := by
  simp only [realRayleigh, PiLp.inner_apply, RCLike.inner_apply']
  rfl

theorem realRayleigh_abs_le_norm (K : Matrix ι ι ℝ)
    (v : EuclideanSpace ℝ ι) (hv : ‖v‖ = 1) :
    |realRayleigh K v| ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) K‖ := by
  have hinner := abs_real_inner_le_norm v (Matrix.toEuclideanCLM (𝕜 := ℝ) K v)
  have hop := (Matrix.toEuclideanCLM (𝕜 := ℝ) K).le_opNorm v
  simpa only [realRayleigh, hv, one_mul, mul_one] using hinner.trans
    (mul_le_mul_of_nonneg_left hop (norm_nonneg v))

theorem realRayleigh_sub (K Khat : Matrix ι ι ℝ) (v : EuclideanSpace ℝ ι) :
    realRayleigh K v - realRayleigh Khat v = realRayleigh (K - Khat) v := by
  simp only [realRayleigh, map_sub, ContinuousLinearMap.sub_apply, inner_sub_right]

/-- Operator-norm error controls every unit-vector quadratic-form error. -/
theorem realRayleigh_error (K Khat : Matrix ι ι ℝ) {κ : ℝ}
    (herr : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (K - Khat)‖ ≤ κ)
    (v : EuclideanSpace ℝ ι) (hv : ‖v‖ = 1) :
    |realRayleigh K v - realRayleigh Khat v| ≤ κ := by
  rw [realRayleigh_sub]
  exact (realRayleigh_abs_le_norm (K - Khat) v hv).trans herr

/-- A compositional version that compares the reported vector with every unit
competitor. The three errors are two matrix evaluations and one minimization. -/
theorem approximate_minimizer_comparison (K Khat : Matrix ι ι ℝ) {κ : ℝ}
    (herr : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (K - Khat)‖ ≤ κ)
    (v : EuclideanSpace ℝ ι) (hv : ‖v‖ = 1)
    (happrox : ∀ w : EuclideanSpace ℝ ι, ‖w‖ = 1 →
      realRayleigh Khat v ≤ realRayleigh Khat w + κ)
    (w : EuclideanSpace ℝ ι) (hw : ‖w‖ = 1) :
    realRayleigh K v ≤ realRayleigh K w + 3 * κ := by
  have hev := abs_le.mp (realRayleigh_error K Khat herr v hv)
  have hew := abs_le.mp (realRayleigh_error K Khat herr w hw)
  have ha := happrox w hw
  linarith

/-- A supplied actual nonpositive direction of K gives the required `3κ` bound. -/
theorem approximate_minimizer_of_nonpositive_witness
    (K Khat : Matrix ι ι ℝ) {κ : ℝ}
    (herr : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (K - Khat)‖ ≤ κ)
    (v : EuclideanSpace ℝ ι) (hv : ‖v‖ = 1)
    (happrox : ∀ w : EuclideanSpace ℝ ι, ‖w‖ = 1 →
      realRayleigh Khat v ≤ realRayleigh Khat w + κ)
    (w : EuclideanSpace ℝ ι) (hw : ‖w‖ = 1) (hneg : realRayleigh K w ≤ 0) :
    realRayleigh K v ≤ 3 * κ := by
  have h := approximate_minimizer_comparison K Khat herr v hv happrox w hw
  linarith

def unitRayleighValues (K : Matrix ι ι ℝ) : Set ℝ :=
  {t | ∃ v : EuclideanSpace ℝ ι, ‖v‖ = 1 ∧ t = realRayleigh K v}

def leastRayleigh (K : Matrix ι ι ℝ) : ℝ := sInf (unitRayleighValues K)

theorem unitRayleighValues_bddBelow (K : Matrix ι ι ℝ) :
    BddBelow (unitRayleighValues K) := by
  refine ⟨-‖Matrix.toEuclideanCLM (𝕜 := ℝ) K‖, ?_⟩
  rintro t ⟨v, hv, rfl⟩
  exact (abs_le.mp (realRayleigh_abs_le_norm K v hv)).1

theorem leastRayleigh_le (K : Matrix ι ι ℝ)
    (v : EuclideanSpace ℝ ι) (hv : ‖v‖ = 1) :
    leastRayleigh K ≤ realRayleigh K v :=
  csInf_le (unitRayleighValues_bddBelow K) ⟨v, hv, rfl⟩

/-- The minimum-Rayleigh value itself, rather than an assumed exact minimizer,
suffices to control the comparison with every unit vector. -/
theorem approximate_minimizer_comparison_of_infimum
    (Khat : Matrix ι ι ℝ) {κ : ℝ} (v : EuclideanSpace ℝ ι)
    (happrox : realRayleigh Khat v ≤ leastRayleigh Khat + κ) :
    ∀ w : EuclideanSpace ℝ ι, ‖w‖ = 1 →
      realRayleigh Khat v ≤ realRayleigh Khat w + κ := by
  intro w hw
  exact happrox.trans (add_le_add_right (leastRayleigh_le Khat w hw) κ)

/-- The full variational `lambda_min(K) + 3κ` guarantee. It needs no spectral gap,
and even symmetry is unnecessary for this quadratic-form perturbation argument. -/
theorem approximate_minimum_Rayleigh_accuracy
    (K Khat : Matrix ι ι ℝ) {κ : ℝ}
    (herr : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (K - Khat)‖ ≤ κ)
    (v : EuclideanSpace ℝ ι) (hv : ‖v‖ = 1)
    (happrox : realRayleigh Khat v ≤ leastRayleigh Khat + κ) :
    realRayleigh K v ≤ leastRayleigh K + 3 * κ := by
  have ha := approximate_minimizer_comparison_of_infimum Khat v happrox
  apply (sub_le_iff_le_add).mp
  apply le_csInf (show (unitRayleighValues K).Nonempty from ⟨_, v, hv, rfl⟩)
  rintro t ⟨w, hw, rfl⟩
  have h := approximate_minimizer_comparison K Khat herr v hv ha w hw
  linarith

theorem approximate_minimum_Rayleigh_accuracy_of_nonpositive
    (K Khat : Matrix ι ι ℝ) {κ : ℝ}
    (herr : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (K - Khat)‖ ≤ κ)
    (v : EuclideanSpace ℝ ι) (hv : ‖v‖ = 1)
    (happrox : realRayleigh Khat v ≤ leastRayleigh Khat + κ)
    (hneg : leastRayleigh K ≤ 0) :
    realRayleigh K v ≤ 3 * κ := by
  have h := approximate_minimum_Rayleigh_accuracy K Khat herr v hv happrox
  linarith

#print axioms approximate_minimum_Rayleigh_accuracy
#print axioms approximate_minimizer_of_nonpositive_witness

end MatrixSpencer.KSRayleighAccuracy
