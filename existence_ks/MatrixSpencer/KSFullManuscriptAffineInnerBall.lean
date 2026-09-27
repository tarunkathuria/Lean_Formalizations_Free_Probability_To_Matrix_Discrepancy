import MatrixSpencer.KSFullManuscriptAffineData
import MatrixSpencer.KSNumericalFidelity

/-!
# An arithmetic inner radius for an affine PSD pencil

The Lipschitz budget is computed from squared sums of the actual coefficient
entries. A supplied positive margin at the constant matrix then gives the
explicit coordinate radius `σ/(2 C)`. The KS application discharges the
constant margin at its stated strictly feasible point.
-/

open Matrix
open scoped BigOperators InnerProductSpace MatrixOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSFullManuscriptAffineInnerBall

open KSFullManuscriptAffinePSD KSRayleighAccuracy
variable {ℓ d : ℕ}

def coefficientBudget (D : Data ℓ d) : ℝ :=
  1 + ∑ i, KSNumericalFidelity.matrixBound (D.coefficient i)

def radius (D : Data ℓ d) (σ : ℝ) : ℝ := σ / (2 * coefficientBudget D)

theorem coefficientBudget_pos (D : Data ℓ d) : 0 < coefficientBudget D := by
  have h := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) =>
    (KSNumericalFidelity.matrixBound_pos (D.coefficient i)).le)
  unfold coefficientBudget
  linarith

def delta (D : Data ℓ d) (x : Space ℓ) : Matrix (Fin d) (Fin d) ℝ := ∑ i, x i • D.coefficient i

theorem delta_symmetric (D : Data ℓ d) (x : Space ℓ) : (delta D x).IsSymm := by
  unfold delta Matrix.IsSymm
  rw [Matrix.transpose_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact (D.coefficient_symmetric i).smul (x i)

theorem delta_norm_le (D : Data ℓ d) (x : Space ℓ) : ‖delta D x‖ ≤ coefficientBudget D * ‖x‖ := by
  calc
    ‖delta D x‖ ≤ ∑ i, ‖x i • D.coefficient i‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖x‖ * KSNumericalFidelity.matrixBound (D.coefficient i) := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul]
      exact mul_le_mul (PiLp.norm_apply_le x i) (KSNumericalFidelity.norm_le_matrixBound _)
        (norm_nonneg _) (norm_nonneg _)
    _ ≤ coefficientBudget D * ‖x‖ := by
      rw [← Finset.mul_sum]
      unfold coefficientBudget
      nlinarith [norm_nonneg x]

theorem realRayleigh_abs_le (A : Matrix (Fin d) (Fin d) ℝ) (v : EuclideanSpace ℝ (Fin d)) :
    |realRayleigh A v| ≤ ‖A‖ * ‖v‖ ^ 2 := by
  have hi := abs_real_inner_le_norm v (Matrix.toEuclideanCLM (𝕜 := ℝ) A v)
  have ho := (Matrix.toEuclideanCLM (𝕜 := ℝ) A).le_opNorm v
  calc
    |realRayleigh A v| ≤ ‖v‖ * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A v‖ := hi
    _ ≤ ‖v‖ * (‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖ * ‖v‖) :=
      mul_le_mul_of_nonneg_left ho (norm_nonneg _)
    _ = _ := by
      change ‖v‖ * (‖A‖ * ‖v‖) = ‖A‖ * ‖v‖ ^ 2
      ring

/-- An operator-norm bound protects positivity under a symmetric perturbation. -/
theorem scalar_add_posSemidef (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.IsSymm)
    {σ : ℝ} (hbound : ‖A‖ ≤ σ) : (σ • 1 + A).PosSemidef := by
  have hsymm : (σ • (1 : Matrix (Fin d) (Fin d) ℝ) + A).IsSymm :=
    (Matrix.isSymm_one.smul σ).add hA
  refine ⟨?_, fun v => ?_⟩
  · simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hsymm
  · let w : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 v
    have ha := (abs_le.mp (realRayleigh_abs_le A w)).1
    have hn := mul_le_mul_of_nonneg_right hbound (sq_nonneg ‖w‖)
    have he : realRayleigh (σ • 1 + A) w = σ * ‖w‖ ^ 2 + realRayleigh A w := by
      simp only [realRayleigh, map_add, map_smul, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.smul_apply, inner_add_right, inner_smul_right]
      rw [show ⟪w, (Matrix.toEuclideanCLM (𝕜 := ℝ) 1) w⟫_ℝ = ‖w‖ ^ 2 from KSJacobiRayleigh.realRayleigh_one w]
    have hh : 0 ≤ realRayleigh (σ • 1 + A) w := by rw [he]; linarith
    simpa only [realRayleigh_eq_quadratic, w, WithLp.ofLp_toLp, star_trivial] using hh

theorem radius_pos (D : Data ℓ d) {σ : ℝ} (hσ : 0 < σ) : 0 < radius D σ := by
  unfold radius
  exact div_pos hσ (mul_pos (by norm_num) (coefficientBudget_pos D))

/-- The inner ball is proved from the actual coefficient budget and the
constant matrix margin, with no least-eigenvalue or radius oracle. -/
theorem ball_subset_target (D : Data ℓ d) {σ : ℝ} (hσ : 0 < σ)
    (hmargin : σ • (1 : Matrix (Fin d) (Fin d) ℝ) ≤ D.constant) :
    Metric.closedBall (0 : Space ℓ) (radius D σ) ⊆ target D := by
  intro x hx
  have hn : ‖x‖ ≤ radius D σ := by simpa using hx
  have hc := coefficientBudget_pos D
  have hdelta : ‖delta D x‖ ≤ σ := by
    calc
      ‖delta D x‖ ≤ coefficientBudget D * ‖x‖ := delta_norm_le D x
      _ ≤ coefficientBudget D * radius D σ := mul_le_mul_of_nonneg_left hn hc.le
      _ = σ / 2 := by unfold radius; field_simp
      _ ≤ σ := by linarith
  have hbase : (D.constant - σ • 1).PosSemidef := (sub_nonneg.mpr hmargin).posSemidef
  have hadd := scalar_add_posSemidef (delta D x) (delta_symmetric D x) hdelta
  have hh := hbase.add hadd
  have he : D.constant - σ • 1 + (σ • 1 + delta D x) = matrixAt D x := by
    unfold matrixAt delta
    abel
  rw [he] at hh
  exact hh

end MatrixSpencer.KSFullManuscriptAffineInnerBall
