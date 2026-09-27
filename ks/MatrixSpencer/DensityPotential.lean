import MatrixSpencer.FidelityContinuity
import MatrixSpencer.TraceSqrtConcavity
import Mathlib.Topology.Order.Compact

/-!
# The actual density potential and its attained maximum

The source is a concrete Kraus channel, so its positivity and continuity are
proved here. No optimizer-existence oracle is a hypothesis.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix

noncomputable section

namespace MatrixSpencer

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
theorem krausChannel_posSemidef (B : ι → Matrix n n ℂ) {S : Matrix n n ℂ}
    (hS : S.PosSemidef) : (krausChannel B S).PosSemidef := by
  apply Matrix.nonneg_iff_posSemidef.mp
  exact Finset.sum_nonneg fun i _ => (hS.mul_mul_conjTranspose_same (B i)).nonneg

omit [DecidableEq n] in
theorem continuous_krausChannel (B : ι → Matrix n n ℂ) : Continuous (krausChannel B) := by
  unfold krausChannel
  fun_prop

omit [DecidableEq n] in
theorem krausChannel_weighted_add (B : ι → Matrix n n ℂ) (S T : Matrix n n ℂ) (a b : ℝ) :
    krausChannel B (a • S + b • T) = a • krausChannel B S + b • krausChannel B T := by
  simp only [krausChannel, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
    Matrix.smul_mul, Finset.sum_add_distrib, Finset.smul_sum]

/-- The original p=2 objective, maximized over trace-one positive matrices. -/
def densityObjective (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ) (θ : ℝ)
    (S : Matrix n n ℂ) : ℝ :=
  realTrace (H * S) + 2 * fidelity S (krausChannel B S) + 2 * θ * realTrace (CFC.sqrt S)

theorem continuousOn_densityObjective (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ) (θ : ℝ) :
    ContinuousOn (densityObjective H B θ) densitySet := by
  apply continuousOn_iff_continuous_restrict.mpr
  have hs : Continuous (fun S : (densitySet : Set (Matrix n n ℂ)) => (S : Matrix n n ℂ)) :=
    continuous_subtype_val
  have hsource := (continuous_krausChannel B).comp hs
  have hf := continuous_fidelity_of_psd hs hsource (fun S => S.property.1)
    (fun S => krausChannel_posSemidef B S.property.1)
  have hroot := continuous_matrix_sqrt_of_psd hs (fun S => S.property.1)
  exact ((continuous_realTrace.comp (continuous_const.mul hs)).add
    (continuous_const.mul hf)).add (continuous_const.mul (continuous_realTrace.comp hroot))

/-- Existence of an actual maximizing density, allowing singular sources and arbitrary Kraus data. -/
theorem exists_densityOptimizer [Nonempty n]
    (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ) (θ : ℝ) :
    ∃ S ∈ densitySet, ∀ T ∈ densitySet, densityObjective H B θ T ≤ densityObjective H B θ S := by
  exact isCompact_densitySet.exists_isMaxOn densitySet_nonempty (continuousOn_densityObjective H B θ)

/-- The density potential is the supremum of the actual objective values. -/
def densityPotential (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ) (θ : ℝ) : ℝ :=
  sSup (densityObjective H B θ '' densitySet)

theorem densityPotential_eq_of_maximizer
    (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ) (θ : ℝ) {S : Matrix n n ℂ}
    (hS : S ∈ densitySet)
    (hmax : ∀ T ∈ densitySet, densityObjective H B θ T ≤ densityObjective H B θ S) :
    densityPotential H B θ = densityObjective H B θ S := by
  have hgreatest : IsGreatest (densityObjective H B θ '' densitySet) (densityObjective H B θ S) := by
    refine ⟨⟨S, hS, rfl⟩, ?_⟩
    rintro z ⟨T, hT, rfl⟩
    exact hmax T hT
  exact hgreatest.csSup_eq

/-- The potential supremum is attained; this is not an assumption on input matrices. -/
theorem exists_densityPotential_eq [Nonempty n]
    (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ) (θ : ℝ) :
    ∃ S ∈ densitySet, densityPotential H B θ = densityObjective H B θ S := by
  obtain ⟨S, hS, hmax⟩ := exists_densityOptimizer H B θ
  exact ⟨S, hS, densityPotential_eq_of_maximizer H B θ hS hmax⟩

theorem densityObjective_le_potential [Nonempty n]
    (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ) (θ : ℝ) {S : Matrix n n ℂ}
    (hS : S ∈ densitySet) : densityObjective H B θ S ≤ densityPotential H B θ := by
  obtain ⟨T, hT, hmax⟩ := exists_densityOptimizer H B θ
  rw [densityPotential_eq_of_maximizer H B θ hT hmax]
  exact hmax S hS

theorem densityObjective_center_difference
    (H H' S : Matrix n n ℂ) (B : ι → Matrix n n ℂ) (θ : ℝ) :
    densityObjective H' B θ S = densityObjective H B θ S + realTrace ((H' - H) * S) := by
  simp only [densityObjective, Matrix.sub_mul, realTrace_sub]
  ring

/-- Every actual maximizing density supplies a global affine supporting plane. -/
theorem densityPotential_supporting_plane [Nonempty n]
    (H H' : Matrix n n ℂ) (B : ι → Matrix n n ℂ) (θ : ℝ) {S : Matrix n n ℂ}
    (hS : S ∈ densitySet)
    (hmax : ∀ T ∈ densitySet, densityObjective H B θ T ≤ densityObjective H B θ S) :
    densityPotential H B θ + realTrace ((H' - H) * S) ≤ densityPotential H' B θ := by
  rw [densityPotential_eq_of_maximizer H B θ hS hmax,
    ← densityObjective_center_difference]
  exact densityObjective_le_potential H' B θ hS

/-- The globally anchored potential used in the finite epoch is nonnegative. -/
theorem densityPotential_anchored_nonneg [Nonempty n]
    (H H' : Matrix n n ℂ) (B : ι → Matrix n n ℂ) (θ : ℝ) {S : Matrix n n ℂ}
    (hS : S ∈ densitySet)
    (hmax : ∀ T ∈ densitySet, densityObjective H B θ T ≤ densityObjective H B θ S) :
    0 ≤ densityPotential H' B θ - densityPotential H B θ - realTrace ((H' - H) * S) := by
  have h := densityPotential_supporting_plane H H' B θ hS hmax
  linarith

/-- The positive square-root regularizer makes the actual objective strictly concave. -/
theorem strictConcaveOn_densityObjective
    (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ) {θ : ℝ} (hθ : 0 < θ) :
    StrictConcaveOn ℝ densitySet (densityObjective H B θ) := by
  refine ⟨densitySet_convex, ?_⟩
  intro S hS T hT hne a b ha hb hab
  have hf := fidelity_concave hS.1 hT.1 (krausChannel_posSemidef B hS.1)
    (krausChannel_posSemidef B hT.1) ha.le hb.le hab
  have hr := mul_lt_mul_of_pos_left (trace_sqrt_strict_concave hS.1 hT.1 hne ha hb hab)
    (mul_pos (by norm_num : (0 : ℝ) < 2) hθ)
  simp only [densityObjective, krausChannel_weighted_add, Matrix.mul_add,
    Matrix.mul_smul, realTrace_add, realTrace_smul, smul_eq_mul]
  nlinarith

/-- There is exactly one maximizing density when the Tsallis scale is positive. -/
theorem existsUnique_densityOptimizer [Nonempty n]
    (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ) {θ : ℝ} (hθ : 0 < θ) :
    ∃! S : Matrix n n ℂ, S ∈ densitySet ∧
      ∀ T ∈ densitySet, densityObjective H B θ T ≤ densityObjective H B θ S := by
  obtain ⟨S, hS, hmax⟩ := exists_densityOptimizer H B θ
  refine ⟨S, ⟨hS, hmax⟩, ?_⟩
  intro T hT
  exact (strictConcaveOn_densityObjective H B hθ).eq_of_isMaxOn hT.2 hmax hT.1 hS

/-- A maximizing density chosen from the proved existence theorem. -/
def densityOptimizer [Nonempty n]
    (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ) (θ : ℝ) : Matrix n n ℂ :=
  (exists_densityOptimizer H B θ).choose

theorem densityOptimizer_mem [Nonempty n]
    (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ) (θ : ℝ) :
    densityOptimizer H B θ ∈ densitySet :=
  (exists_densityOptimizer H B θ).choose_spec.1

theorem densityOptimizer_isMaxOn [Nonempty n]
    (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ) (θ : ℝ) :
    ∀ T ∈ densitySet, densityObjective H B θ T ≤
      densityObjective H B θ (densityOptimizer H B θ) :=
  (exists_densityOptimizer H B θ).choose_spec.2

end MatrixSpencer
