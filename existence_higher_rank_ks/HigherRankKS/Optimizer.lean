import HigherRankKS.Potential
import HigherRankKS.CarrierConcavity
import MatrixSpencer.DensityFaithfulness

/-!
# Concavity and faithfulness of the actual nonlinear density optimizer

The source inequalities are derived from the concrete carrier, then combined
with joint fidelity concavity and its monotonicity in the source argument.
-/

open Matrix MatrixSpencer Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

noncomputable section
namespace HigherRankKS

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
local instance optimizerCStar {k : Type*} [Fintype k] [DecidableEq k] :
    CStarAlgebra (Matrix k k ℂ) := {}

omit [Fintype n] [DecidableEq n] in
theorem marginal_weighted_add (S T : Matrix (n ⊕ n) (n ⊕ n) ℂ) (a b : ℝ) :
    marginal (a • S + b • T) = a • marginal S + b • marginal T := by
  ext i j
  change a • S (Sum.inl i) (Sum.inl j) + b • T (Sum.inl i) (Sum.inl j) +
      (a • S (Sum.inr i) (Sum.inr j) + b • T (Sum.inr i) (Sum.inr j)) =
    a • (S (Sum.inl i) (Sum.inl j) + S (Sum.inr i) (Sum.inr j)) +
      b • (T (Sum.inl i) (Sum.inl j) + T (Sum.inr i) (Sum.inr j))
  module

theorem carrier_weighted_add (A : Matrix n n ℂ)
    (S T : Matrix (n ⊕ n) (n ⊕ n) ℂ) (a b : ℝ) :
    carrier A (a • S + b • T) = a • carrier A S + b • carrier A T := by
  simp only [carrier, marginal_weighted_add, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_smul, Matrix.smul_mul]

/-- Positive output congruence preserves the carrier's Loewner concavity. -/
theorem sourceBlock_weighted_add_le (A : Matrix n n ℂ)
    {β : ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    {S T : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hS : S.PosSemidef) (hT : T.PosSemidef)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a • sourceBlock β A S + b • sourceBlock β A T ≤ sourceBlock β A (a • S + b • T) := by
  have h := carrierPower_weighted_add_le hβ hβ1
    (carrier_posSemidef A hS) (carrier_posSemidef A hT) ha hb
  have hd := (Matrix.le_iff.mp h).conjTranspose_mul_mul_same (CFC.sqrt A)
  apply Matrix.le_iff.mpr
  simpa only [(CFC.sqrt_nonneg A).posSemidef.isHermitian.eq,
    sourceBlock, carrier_weighted_add, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul] using hd

theorem sourceTerm_weighted_add_le (A : Matrix n n ℂ)
    {β : ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    {S T : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hS : S.PosSemidef) (hT : T.PosSemidef)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a • sourceTerm β A S + b • sourceTerm β A T ≤ sourceTerm β A (a • S + b • T) := by
  have hd := Matrix.le_iff.mp (sourceBlock_weighted_add_le A hβ hβ1 hS hT ha hb)
  have h := posSemidef_fromBlocks_diagonal hd hd
  apply Matrix.le_iff.mpr
  convert h using 1
  ext i j
  cases i <;> cases j <;> simp [sourceTerm]

/-- The concrete higher-rank source is operator concave in its full density input. -/
theorem source_weighted_add_le (A : ι → Matrix n n ℂ)
    {β : ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    {c : ι → ℝ} (hc : ∀ i, 0 ≤ c i)
    {S T : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hS : S.PosSemidef) (hT : T.PosSemidef)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a • source A β c S + b • source A β c T ≤ source A β c (a • S + b • T) := by
  simp only [source, Finset.smul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _hi
  have h := smul_le_smul_of_nonneg_left
    (sourceTerm_weighted_add_le (A i) hβ hβ1 hS hT ha hb) (hc i)
  simpa only [smul_add, smul_comm (c i) a, smul_comm (c i) b] using h

/-- Fidelity with the actual nonlinear source is concave on the PSD cone. -/
theorem fidelity_source_concave (A : ι → Matrix n n ℂ)
    {β : ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    {c : ι → ℝ} (hc : ∀ i, 0 ≤ c i)
    {S T : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hS : S.PosSemidef) (hT : T.PosSemidef)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a * fidelity S (source A β c S) + b * fidelity T (source A β c T) ≤
      fidelity (a • S + b • T) (source A β c (a • S + b • T)) := by
  have hΩS := source_posSemidef A β hc hS
  have hΩT := source_posSemidef A β hc hT
  have hm := posSemidef_weighted_add hS hT ha hb
  exact (fidelity_concave hS hT hΩS hΩT ha hb hab).trans
    (fidelity_mono hm hm (posSemidef_weighted_add hΩS hΩT ha hb)
      (source_posSemidef A β hc hm) le_rfl
      (source_weighted_add_le A hβ hβ1 hc hS hT ha hb))

theorem concaveOn_objective (H : Matrix (n ⊕ n) (n ⊕ n) ℂ)
    (A : ι → Matrix n n ℂ) {β : ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    {c : ι → ℝ} (hc : ∀ i, 0 ≤ c i) {θ : ℝ} (hθ : 0 ≤ θ) :
    ConcaveOn ℝ densitySet (objective H A β c θ) := by
  refine ⟨densitySet_convex, ?_⟩
  intro S hS T hT a b ha hb hab
  have hf := fidelity_source_concave A hβ hβ1 hc hS.1 hT.1 ha hb hab
  have hr := mul_le_mul_of_nonneg_left (trace_sqrt_concave hS.1 hT.1 ha hb hab)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hθ)
  simp only [objective, Matrix.mul_add, Matrix.mul_smul, realTrace_add,
    realTrace_smul, smul_eq_mul]
  nlinarith

/-- The positive root regularizer makes the concrete objective strictly concave. -/
theorem strictConcaveOn_objective (H : Matrix (n ⊕ n) (n ⊕ n) ℂ)
    (A : ι → Matrix n n ℂ) {β : ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    {c : ι → ℝ} (hc : ∀ i, 0 ≤ c i) {θ : ℝ} (hθ : 0 < θ) :
    StrictConcaveOn ℝ densitySet (objective H A β c θ) := by
  refine ⟨densitySet_convex, ?_⟩
  intro S hS T hT hne a b ha hb hab
  have hf := fidelity_source_concave A hβ hβ1 hc hS.1 hT.1 ha.le hb.le hab
  have hr := mul_lt_mul_of_pos_left (trace_sqrt_strict_concave hS.1 hT.1 hne ha hb hab)
    (mul_pos (by norm_num : (0 : ℝ) < 2) hθ)
  simp only [objective, Matrix.mul_add, Matrix.mul_smul, realTrace_add,
    realTrace_smul, smul_eq_mul]
  nlinarith

/-- There is exactly one maximizer of the actual nonlinear density objective. -/
theorem existsUnique_optimizer [Nonempty n]
    (H : Matrix (n ⊕ n) (n ⊕ n) ℂ) (A : ι → Matrix n n ℂ)
    {β : ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    {c : ι → ℝ} (hc : ∀ i, 0 ≤ c i) {θ : ℝ} (hθ : 0 < θ) :
    ∃! S : Matrix (n ⊕ n) (n ⊕ n) ℂ, S ∈ densitySet ∧
      ∀ T ∈ densitySet, objective H A β c θ T ≤ objective H A β c θ S := by
  obtain ⟨S, hS, hmax⟩ := exists_optimizer H A hβ.le hβ1.le hc θ
  refine ⟨S, ⟨hS, hmax⟩, ?_⟩
  intro T hT
  exact (strictConcaveOn_objective H A hβ hβ1 hc hθ).eq_of_isMaxOn hT.2 hmax hT.1 hS

/-- A kernel perturbation gains at root scale while the remaining terms
of the actual objective lose at most at linear scale. -/
theorem objective_kernel_perturbation_lower
    (H : Matrix (n ⊕ n) (n ⊕ n) ℂ) (A : ι → Matrix n n ℂ)
    {β : ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    {c : ι → ℝ} (hc : ∀ i, 0 ≤ c i) {θ r : ℝ} (hθ : 0 ≤ θ)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) {S U : Matrix (n ⊕ n) (n ⊕ n) ℂ}
    (hS : S.PosSemidef) (hU : U.PosSemidef) (htrace : realTrace U = 1)
    (hUU : U * U = U) (hrootU : CFC.sqrt S * U = 0) (hUroot : U * CFC.sqrt S = 0) :
    (1 - r ^ 2) * objective H A β c θ S + r ^ 2 * realTrace (H * U) + 2 * θ * r ≤
      objective H A β c θ ((1 - r ^ 2) • S + r ^ 2 • U) := by
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
  have hf := fidelity_source_concave A hβ hβ1 hc hS hU ha (sq_nonneg r) hab
  have hfU := mul_nonneg (sq_nonneg r) (fidelity_nonneg U (source A β c U))
  have ht := mul_le_mul_of_nonneg_left hroot (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hθ)
  simp only [objective, Matrix.mul_add, Matrix.mul_smul, realTrace_add, realTrace_smul]
  nlinarith

/-- Every maximizer of the concrete nonlinear objective is positive definite. -/
theorem maximizer_posDef
    (H : Matrix (n ⊕ n) (n ⊕ n) ℂ) (A : ι → Matrix n n ℂ)
    {β : ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    {c : ι → ℝ} (hc : ∀ i, 0 ≤ c i) {θ : ℝ} (hθ : 0 < θ)
    {S : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hS : S ∈ densitySet)
    (hmax : ∀ T ∈ densitySet, objective H A β c θ T ≤ objective H A β c θ S) :
    S.PosDef := by
  by_contra hn
  obtain ⟨U, hU, htrace, hUU, hrootU, hUroot⟩ :=
    exists_kernel_density_projection hS.1 hn
  let K := |realTrace (H * U) - objective H A β c θ S|
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
  have hmix : (1 - r ^ 2) • S + r ^ 2 • U ∈ densitySet :=
    densitySet_convex hS ⟨hU, htrace⟩ (by nlinarith) (sq_nonneg r) (by ring)
  have hlower := objective_kernel_perturbation_lower H A hβ hβ1 hc hθ.le hr.le hr1.le
    hS.1 hU htrace hUU hrootU hUroot
  have hupper := hmax ((1 - r ^ 2) • S + r ^ 2 • U) hmix
  have herr : -K ≤ realTrace (H * U) - objective H A β c θ S := neg_abs_le _
  have herr' := mul_le_mul_of_nonneg_left herr (sq_nonneg r)
  nlinarith

/-- The attained nonlinear optimum has one and only one faithful density. -/
theorem existsUnique_faithful_optimizer [Nonempty n]
    (H : Matrix (n ⊕ n) (n ⊕ n) ℂ) (A : ι → Matrix n n ℂ)
    {β : ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    {c : ι → ℝ} (hc : ∀ i, 0 ≤ c i) {θ : ℝ} (hθ : 0 < θ) :
    ∃! S : Matrix (n ⊕ n) (n ⊕ n) ℂ, S ∈ densitySet ∧ S.PosDef ∧
      ∀ T ∈ densitySet, objective H A β c θ T ≤ objective H A β c θ S := by
  obtain ⟨S, hS, huniq⟩ := existsUnique_optimizer H A hβ hβ1 hc hθ
  refine ⟨S, ⟨hS.1, maximizer_posDef H A hβ hβ1 hc hθ hS.1 hS.2, hS.2⟩, ?_⟩
  intro T hT
  exact huniq T ⟨hT.1, hT.2.2⟩

end HigherRankKS
