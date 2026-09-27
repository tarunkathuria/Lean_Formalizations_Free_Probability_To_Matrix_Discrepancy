import RadialKS.DeterministicRun
import SeamlessKS.WalkGeometry
import SeamlessKS.RuntimeBudgets
import MatrixSpencer.KSRuntimePolynomialRepresentation

/-! Initial spectral budget and deterministic horizon for the radial walk.
Only the common zero-state preparation is taken from Walk. No claim about
the old walk's transitions or output is used. -/
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace RadialKS.InitialBudget
open MatrixSpencer SeamlessKS SeamlessKS.State SeamlessKS.StatePotential
open SeamlessKS.Parameters RadialKS.Progress RadialKS.DeterministicRun
variable {N d : ℕ}

theorem beta_mul_labels (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : ∑ i, KSRankOne.atom (v i) = 1) :
    beta v * (N : ℝ) = Input.delta v / 100 := by
  have hn : (N : ℝ) ≠ 0 := (Nat.cast_pos.mpr (Input.labels_pos v hd hp)).ne'
  unfold beta
  field_simp

theorem beta_le_delta_div_hundred (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : ∑ i, KSRankOne.atom (v i) = 1) : beta v ≤ Input.delta v / 100 := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast Input.labels_pos v hd hp
  have hb := (beta_pos v hd hp).le
  have he := beta_mul_labels v hd hp
  nlinarith

theorem initial_potential (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : ∑ i, KSRankOne.atom (v i) = 1) :
    potential v (Input.theta v) (zeta N) (Walk.initial v hd hp).toCubeState ≤
      34 * Input.delta v := by
  have h := Input.smooth_initial_potential_le v hd hp
    (zeta_pos (Input.labels_pos v hd hp)).le
  simpa only [potential, debit, StatePotential.signedSum, WalkGeometry.initial_coeff_zero,
    Pi.zero_apply, zero_smul, Finset.sum_const_zero, SourceTransport.smoothWeights] using h

theorem initial_deficit (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : ∑ i, KSRankOne.atom (v i) = 1) :
    RadialKS.Progress.deficit (Walk.initial v hd hp).coeff = N := by
  simp only [RadialKS.Progress.deficit, energy, WalkGeometry.initial_coeff_zero,
    Pi.zero_apply, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero, sub_zero]

/-- The exact initial allowance is at most 34.02 times the square root of
the maximum atom size. The reserve is an analytic rounding allowance. -/
theorem initial_budget_le (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : ∑ i, KSRankOne.atom (v i) = 1) :
    budget v (Input.theta v) (zeta N) (beta v) (Walk.initial v hd hp).toCubeState ≤
      (1701 / 50 : ℝ) * Input.delta v := by
  have hf := initial_potential v hd hp
  have hr := (WalkGeometry.reserve_le_beta v hd hp (Walk.initial v hd hp).toCubeState).trans
    (beta_le_delta_div_hundred v hd hp)
  have hb := beta_mul_labels v hd hp
  unfold budget account
  rw [initial_deficit]
  linarith

theorem initial_budget_lt (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : ∑ i, KSRankOne.atom (v i) = 1) :
    budget v (Input.theta v) (zeta N) (beta v) (Walk.initial v hd hp).toCubeState <
      35 * Input.delta v := by
  have hb := initial_budget_le v hd hp
  have hδ := Input.delta_pos v hd hp
  nlinarith

/-- The already specified finite horizon exceeds the radial energy budget;
the new termination argument uses deterministic squared-norm progress. -/
theorem horizon_strict (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : ∑ i, KSRankOne.atom (v i) = 1) :
    (N : ℝ) < (horizon v : ℝ) * movementStep v ^ 2 := by
  have h := horizon_budget v hd hp
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr (Input.labels_pos v hd hp)
  nlinarith

theorem horizon_bounded (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : ∑ i, KSRankOne.atom (v i) = 1) : horizon v ≤ RuntimeBudgets.horizonCap N d := by
  have h := horizon_le_polynomial v hd hp
  rw [← RuntimeBudgets.cast_horizonCap] at h
  exact_mod_cast h

theorem horizonCap_polynomial :
    KSRuntimePolynomialRepresentation.Represented
      (fun N d _r => RuntimeBudgets.horizonCap N d) := by
  simp only [RuntimeBudgets.horizonCap, RuntimeBudgets.movementInverseSquareCap,
    RuntimeBudgets.derivativeCap, RuntimeBudgets.jointDerivativeCap,
    RuntimeBudgets.radiusInverseCap]
  ks_poly_cert

end RadialKS.InitialBudget
