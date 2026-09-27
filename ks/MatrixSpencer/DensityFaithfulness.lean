import MatrixSpencer.DensityPotential
import Mathlib.Tactic.Module

/-!
# Faithfulness of the actual density optimizer

A singular density has a trace-one orthogonal kernel projection. Moving a small
amount of mass into that direction increases the trace square root at square-root
scale, while the remaining objective terms lose at most a linear amount.
-/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

namespace MatrixSpencer

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A singular positive matrix has a zero eigenvalue. -/
theorem exists_zero_eigenvalue_of_not_posDef {S : Matrix n n ℂ}
    (hS : S.PosSemidef) (hn : ¬ S.PosDef) :
    ∃ i, hS.isHermitian.eigenvalues i = 0 := by
  rw [hS.isHermitian.posDef_iff_eigenvalues_pos] at hn
  push_neg at hn
  obtain ⟨i, hi⟩ := hn
  exact ⟨i, le_antisymm hi (hS.eigenvalues_nonneg i)⟩

/-- An explicit one-dimensional projection in the kernel, constructed in an eigenbasis. -/
theorem exists_kernel_density_projection {S : Matrix n n ℂ}
    (hS : S.PosSemidef) (hn : ¬ S.PosDef) :
    ∃ U : Matrix n n ℂ, U.PosSemidef ∧ realTrace U = 1 ∧ U * U = U ∧
      CFC.sqrt S * U = 0 ∧ U * CFC.sqrt S = 0 := by
  classical
  obtain ⟨i, hi⟩ := exists_zero_eigenvalue_of_not_posDef hS hn
  let V : Matrix n n ℂ := hS.isHermitian.eigenvectorUnitary
  let E : Matrix n n ℂ := Matrix.diagonal (Pi.single i (1 : ℂ))
  let U : Matrix n n ℂ := V * E * Vᴴ
  have hV : Vᴴ * V = 1 := unitary.coe_star_mul_self hS.isHermitian.eigenvectorUnitary
  have hE : E.PosSemidef := by
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro j
    simp only [Pi.single_apply]
    split_ifs <;> positivity
  have hU : U.PosSemidef := hE.mul_mul_conjTranspose_same V
  have hEE : E * E = E := by
    rw [show E = Matrix.diagonal (Pi.single i (1 : ℂ)) from rfl,
      Matrix.diagonal_mul_diagonal]
    congr 1
    ext j
    simp only [Pi.single_apply]
    split_ifs <;> simp
  have hUU : U * U = U := by
    change (V * E * Vᴴ) * (V * E * Vᴴ) = V * E * Vᴴ
    calc
      _ = V * E * (Vᴴ * V) * E * Vᴴ := by simp only [Matrix.mul_assoc]
      _ = V * E * Vᴴ := by rw [hV, Matrix.mul_one, Matrix.mul_assoc V E E, hEE]
  have htrace : realTrace U = 1 := by
    change realTrace (V * E * Vᴴ) = 1
    rw [realTrace_mul_cycle, hV, Matrix.one_mul]
    simp [realTrace, E]
  have hdiag : Matrix.diagonal (RCLike.ofReal ∘ hS.isHermitian.eigenvalues) * E = 0 := by
    rw [show E = Matrix.diagonal (Pi.single i (1 : ℂ)) from rfl,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_zero]
    congr 1
    ext j
    by_cases hj : j = i
    · simp [hj, hi]
    · simp [hj]
  have hSU : S * U = 0 := by
    conv_lhs => lhs; rw [hS.isHermitian.spectral_theorem]
    change (V * Matrix.diagonal (RCLike.ofReal ∘ hS.isHermitian.eigenvalues) * Vᴴ) *
      (V * E * Vᴴ) = 0
    calc
      _ = V * Matrix.diagonal (RCLike.ofReal ∘ hS.isHermitian.eigenvalues) *
          (Vᴴ * V) * E * Vᴴ := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hV, Matrix.mul_one, Matrix.mul_assoc V _ E,
        hdiag, Matrix.mul_zero, Matrix.zero_mul]
  have hroot : (CFC.sqrt S).IsHermitian := (CFC.sqrt_nonneg S).posSemidef.isHermitian
  have hrootU : CFC.sqrt S * U = 0 := by
    apply (realTrace_conjTranspose_mul_self_eq_zero_iff (CFC.sqrt S * U)).mp
    rw [Matrix.conjTranspose_mul, hroot.eq, hU.isHermitian.eq]
    calc
      _ = realTrace (U * (CFC.sqrt S * CFC.sqrt S) * U) := by
        simp only [Matrix.mul_assoc]
      _ = 0 := by rw [CFC.sqrt_mul_sqrt_self S hS.nonneg, Matrix.mul_assoc,
        hSU, Matrix.mul_zero, realTrace_zero]
  have hUroot : U * CFC.sqrt S = 0 := by
    have h := congrArg Matrix.conjTranspose hrootU
    simpa only [Matrix.conjTranspose_mul, hroot.eq, hU.isHermitian.eq,
      Matrix.conjTranspose_zero] using h
  exact ⟨U, hU, htrace, hUU, hrootU, hUroot⟩

/-- Positive square roots add exactly for this orthogonal projection perturbation. -/
theorem sqrt_orthogonal_projection_mix {S U : Matrix n n ℂ}
    (hS : S.PosSemidef) (hU : U.PosSemidef) (hUU : U * U = U)
    (hrootU : CFC.sqrt S * U = 0) (hUroot : U * CFC.sqrt S = 0)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    CFC.sqrt (a • S + b • U) = Real.sqrt a • CFC.sqrt S + Real.sqrt b • U := by
  apply CFC.sqrt_unique
  · simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
      hrootU, hUroot, hUU, CFC.sqrt_mul_sqrt_self S hS.nonneg,
      smul_zero, zero_add, add_zero, smul_smul, Real.mul_self_sqrt ha, Real.mul_self_sqrt hb]
  · exact add_nonneg (smul_nonneg (Real.sqrt_nonneg a) (CFC.sqrt_nonneg S))
      (smul_nonneg (Real.sqrt_nonneg b) hU.nonneg)

/-- The square-root gain has its exact scalar form even when the base density is singular. -/
theorem trace_sqrt_orthogonal_projection_mix {S U : Matrix n n ℂ}
    (hS : S.PosSemidef) (hU : U.PosSemidef) (htrace : realTrace U = 1)
    (hUU : U * U = U) (hrootU : CFC.sqrt S * U = 0) (hUroot : U * CFC.sqrt S = 0)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    realTrace (CFC.sqrt (a • S + b • U)) =
      Real.sqrt a * realTrace (CFC.sqrt S) + Real.sqrt b := by
  rw [sqrt_orthogonal_projection_mix hS hU hUU hrootU hUroot ha hb,
    realTrace_add, realTrace_smul, realTrace_smul, htrace, mul_one]

variable {ι : Type*} [Fintype ι]

/-- The complete objective loses only linearly outside the kernel square-root gain. -/
theorem densityObjective_kernel_perturbation_lower
    (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ) {θ r : ℝ} (hθ : 0 ≤ θ)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) {S U : Matrix n n ℂ}
    (hS : S.PosSemidef) (hU : U.PosSemidef) (htrace : realTrace U = 1)
    (hUU : U * U = U) (hrootU : CFC.sqrt S * U = 0) (hUroot : U * CFC.sqrt S = 0) :
    (1 - r ^ 2) * densityObjective H B θ S + r ^ 2 * realTrace (H * U) + 2 * θ * r ≤
      densityObjective H B θ ((1 - r ^ 2) • S + r ^ 2 • U) := by
  have ha : 0 ≤ 1 - r ^ 2 := by nlinarith
  have hab : (1 - r ^ 2) + r ^ 2 = 1 := by ring
  have hsqrt : 1 - r ^ 2 ≤ Real.sqrt (1 - r ^ 2) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith [mul_nonneg (sq_nonneg r) ha]
  have hroot : (1 - r ^ 2) * realTrace (CFC.sqrt S) + r ≤
      realTrace (CFC.sqrt ((1 - r ^ 2) • S + r ^ 2 • U)) := by
    rw [trace_sqrt_orthogonal_projection_mix hS hU htrace hUU hrootU hUroot ha
      (sq_nonneg r), Real.sqrt_sq hr]
    exact add_le_add_right
      (mul_le_mul_of_nonneg_right hsqrt (realTrace_nonneg (CFC.sqrt_nonneg S).posSemidef)) r
  have hf := fidelity_concave hS hU (krausChannel_posSemidef B hS)
    (krausChannel_posSemidef B hU) ha (sq_nonneg r) hab
  have hfU := mul_nonneg (sq_nonneg r) (fidelity_nonneg U (krausChannel B U))
  have ht := mul_le_mul_of_nonneg_left hroot (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hθ)
  simp only [densityObjective, krausChannel_weighted_add, Matrix.mul_add,
    Matrix.mul_smul, realTrace_add, realTrace_smul]
  nlinarith

/-- Every actual maximizing density is positive definite when the Tsallis scale is positive. -/
theorem density_maximizer_posDef
    (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ) {θ : ℝ} (hθ : 0 < θ)
    {S : Matrix n n ℂ} (hS : S ∈ densitySet)
    (hmax : ∀ T ∈ densitySet, densityObjective H B θ T ≤ densityObjective H B θ S) :
    S.PosDef := by
  by_contra hn
  obtain ⟨U, hU, htrace, hUU, hrootU, hUroot⟩ :=
    exists_kernel_density_projection hS.1 hn
  let K := |realTrace (H * U) - densityObjective H B θ S|
  have hK : 0 ≤ K := abs_nonneg _
  have hK1 : 0 < K + 1 := by linarith
  have hsmall : 0 < min 1 (θ / (K + 1)) :=
    lt_min (by norm_num) (div_pos hθ hK1)
  obtain ⟨r, hr, hrsmall⟩ := exists_between hsmall
  have hr1 : r < 1 := (lt_min_iff.mp hrsmall).1
  have hrK1 : r * (K + 1) < θ :=
    (lt_div_iff₀ hK1).mp (lt_min_iff.mp hrsmall).2
  have hrK : K * r < θ := by nlinarith
  have hgain : 0 < 2 * θ * r - r ^ 2 * K := by
    nlinarith [mul_pos hr (sub_pos.mpr hrK), mul_pos hθ hr]
  have ha : 0 ≤ 1 - r ^ 2 := by nlinarith
  have hmix : (1 - r ^ 2) • S + r ^ 2 • U ∈ densitySet :=
    densitySet_convex hS ⟨hU, htrace⟩ ha (sq_nonneg r) (by ring)
  have hlower := densityObjective_kernel_perturbation_lower H B hθ.le hr.le hr1.le
    hS.1 hU htrace hUU hrootU hUroot
  have hupper := hmax ((1 - r ^ 2) • S + r ^ 2 • U) hmix
  have herr : -K ≤ realTrace (H * U) - densityObjective H B θ S := neg_abs_le _
  have herr' := mul_le_mul_of_nonneg_left herr (sq_nonneg r)
  nlinarith

/-- The optimizer selected from proved compact attainment is genuinely faithful. -/
theorem densityOptimizer_posDef [Nonempty n]
    (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ) {θ : ℝ} (hθ : 0 < θ) :
    (densityOptimizer H B θ).PosDef :=
  density_maximizer_posDef H B hθ (densityOptimizer_mem H B θ)
    (densityOptimizer_isMaxOn H B θ)

end MatrixSpencer
