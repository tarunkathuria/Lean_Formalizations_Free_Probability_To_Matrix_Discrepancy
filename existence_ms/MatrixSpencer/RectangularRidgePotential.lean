import MatrixSpencer.DyadicOwnerFunctions

/-!
# A square-root ridge for the rectangular Tsallis potential

The small additional concave regularizer is part of the actual objective.
These lemmas establish its exact potential, attainment, faithful optimizer,
and additive comparison with the original potential. They do not yet assert
an algorithm or a runtime bound. Compactness below is used only for optimizer
attainment, not to choose numerical tolerances or a step size.
-/

open Matrix Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.RectangularRidgePotential
variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι]
local instance : CStarAlgebra (Matrix n n ℂ) := {}

def objective (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (m : ℕ) (θ κ : ℝ) (S : Matrix n n ℂ) : ℝ :=
  dyadicDensityObjective H B m θ S + 2 * κ * realTrace (CFC.sqrt S)

def potential (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (m : ℕ) (θ κ : ℝ) : ℝ :=
  sSup (objective H B m θ κ '' densitySet)

theorem continuousOn_objective (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (m : ℕ) (θ κ : ℝ) : ContinuousOn (objective H B m θ κ) densitySet := by
  apply continuousOn_iff_continuous_restrict.mpr
  have hs : Continuous (fun S : (densitySet : Set (Matrix n n ℂ)) =>
      (S : Matrix n n ℂ)) := continuous_subtype_val
  have hd := continuousOn_iff_continuous_restrict.mp
    (continuousOn_dyadicDensityObjective H B m θ)
  have hr := continuous_matrix_sqrt_of_psd hs (fun S => S.property.1)
  exact hd.add (continuous_const.mul (continuous_realTrace.comp hr))

theorem exists_maximizer [Nonempty n] (H : Matrix n n ℂ)
    (B : ι → Matrix n n ℂ) (m : ℕ) (θ κ : ℝ) :
    ∃ S ∈ densitySet, ∀ T ∈ densitySet,
      objective H B m θ κ T ≤ objective H B m θ κ S :=
  isCompact_densitySet.exists_isMaxOn densitySet_nonempty
    (continuousOn_objective H B m θ κ)

def optimizer [Nonempty n] (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (m : ℕ) (θ κ : ℝ) : Matrix n n ℂ :=
  (exists_maximizer H B m θ κ).choose

theorem optimizer_mem [Nonempty n] (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (m : ℕ) (θ κ : ℝ) : optimizer H B m θ κ ∈ densitySet :=
  (exists_maximizer H B m θ κ).choose_spec.1

theorem optimizer_max [Nonempty n] (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (m : ℕ) (θ κ : ℝ) : ∀ T ∈ densitySet,
      objective H B m θ κ T ≤ objective H B m θ κ (optimizer H B m θ κ) :=
  (exists_maximizer H B m θ κ).choose_spec.2

theorem potential_eq_of_maximizer (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (m : ℕ) (θ κ : ℝ) {S : Matrix n n ℂ} (hs : S ∈ densitySet)
    (hmax : ∀ T ∈ densitySet, objective H B m θ κ T ≤ objective H B m θ κ S) :
    potential H B m θ κ = objective H B m θ κ S := by
  have hg : IsGreatest (objective H B m θ κ '' densitySet) (objective H B m θ κ S) := by
    refine ⟨⟨S, hs, rfl⟩, ?_⟩
    rintro z ⟨T, hT, rfl⟩
    exact hmax T hT
  exact hg.csSup_eq

theorem potential_eq_optimizer [Nonempty n] (H : Matrix n n ℂ)
    (B : ι → Matrix n n ℂ) (m : ℕ) (θ κ : ℝ) :
    potential H B m θ κ = objective H B m θ κ (optimizer H B m θ κ) :=
  potential_eq_of_maximizer H B m θ κ (optimizer_mem H B m θ κ)
    (optimizer_max H B m θ κ)

theorem objective_le_potential [Nonempty n] (H : Matrix n n ℂ)
    (B : ι → Matrix n n ℂ) (m : ℕ) (θ κ : ℝ) {S : Matrix n n ℂ}
    (hS : S ∈ densitySet) : objective H B m θ κ S ≤ potential H B m θ κ := by
  rw [potential_eq_optimizer]
  exact optimizer_max H B m θ κ S hS

theorem trace_sqrt_le_sqrt_card {S : Matrix n n ℂ} (hS : S ∈ densitySet) :
    realTrace (CFC.sqrt S) ≤ Real.sqrt (Fintype.card n : ℝ) :=
  Real.le_sqrt_of_sq_le (density_trace_sqrt_sq_le_card hS)

theorem objective_bounds (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (m : ℕ) (θ : ℝ) {κ : ℝ} (hκ : 0 ≤ κ) {S : Matrix n n ℂ}
    (hS : S ∈ densitySet) :
    dyadicDensityObjective H B m θ S ≤ objective H B m θ κ S ∧
    objective H B m θ κ S ≤
      dyadicDensityObjective H B m θ S + 2 * κ * Real.sqrt (Fintype.card n : ℝ) := by
  have hn := realTrace_nonneg (CFC.sqrt_nonneg S).posSemidef
  have hh := mul_le_mul_of_nonneg_left (trace_sqrt_le_sqrt_card hS)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hκ)
  dsimp [objective]
  constructor <;> nlinarith

/-- The ridge adds at most its explicit trace budget to the actual potential. -/
theorem potential_bounds [Nonempty n] (H : Matrix n n ℂ)
    (B : ι → Matrix n n ℂ) (m : ℕ) (θ : ℝ) {κ : ℝ} (hκ : 0 ≤ κ) :
    dyadicDensityPotential H B m θ ≤ potential H B m θ κ ∧
    potential H B m θ κ ≤
      dyadicDensityPotential H B m θ + 2 * κ * Real.sqrt (Fintype.card n : ℝ) := by
  constructor
  · rw [dyadicDensityPotential_eq_optimizer]
    exact ((objective_bounds H B m θ hκ (dyadicDensityOptimizer_mem H B m θ)).1).trans
      (objective_le_potential H B m θ κ (dyadicDensityOptimizer_mem H B m θ))
  · rw [potential_eq_optimizer]
    exact ((objective_bounds H B m θ hκ (optimizer_mem H B m θ κ)).2).trans
      (add_le_add_right (dyadicDensityObjective_le_potential H B m θ
        (optimizer_mem H B m θ κ)) _)

theorem kernel_perturbation_lower (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    {m : ℕ} (hm : 1 ≤ m) {θ κ : ℝ} (hθ : 0 ≤ θ) (hκ : 0 ≤ κ)
    {S U : Matrix n n ℂ} (hS : S.PosSemidef) (hU : U.PosSemidef)
    (htrace : realTrace U = 1) (hUU : U * U = U) (hSU : S * U = 0) (hUS : U * S = 0)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    (1 - r ^ (2 ^ m)) * objective H B m θ κ S + r ^ (2 ^ m) * realTrace (H * U) +
      DyadicBoundaryGain.scale m θ * r ^ (2 ^ m - 1) ≤
      objective H B m θ κ ((1 - r ^ (2 ^ m)) • S + r ^ (2 ^ m) • U) := by
  have hb : 0 ≤ r ^ (2 ^ m) := pow_nonneg hr _
  have ha : 0 ≤ 1 - r ^ (2 ^ m) := sub_nonneg.mpr (pow_le_one₀ hr hr1)
  have hd := dyadicDensityObjective_kernel_perturbation_lower H B hm hθ hS hU
    htrace hUU hSU hUS hr hr1
  have hh := trace_sqrt_concave hS hU ha hb (by ring)
  have hu := realTrace_nonneg (CFC.sqrt_nonneg U).posSemidef
  have hh' := mul_le_mul_of_nonneg_left hh (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hκ)
  have hu' := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hκ) hb) hu
  dsimp [objective]
  nlinarith

/-- Faithfulness is proved for the new objective at its own maximizer. -/
theorem maximizer_posDef (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    {m : ℕ} (hm : 1 ≤ m) {θ κ : ℝ} (hθ : 0 < θ) (hκ : 0 ≤ κ)
    {S : Matrix n n ℂ} (hS : S ∈ densitySet)
    (hmax : ∀ T ∈ densitySet, objective H B m θ κ T ≤ objective H B m θ κ S) :
    S.PosDef := by
  by_contra hn
  obtain ⟨U, hU, htrace, hUU, hrootU, hUroot⟩ := exists_kernel_density_projection hS.1 hn
  have hSU : S * U = 0 := by
    calc
      _ = CFC.sqrt S * (CFC.sqrt S * U) := by
        rw [← Matrix.mul_assoc, CFC.sqrt_mul_sqrt_self S hS.1.nonneg]
      _ = 0 := by rw [hrootU, Matrix.mul_zero]
  have hUS : U * S = 0 := by
    calc
      _ = (U * CFC.sqrt S) * CFC.sqrt S := by
        rw [Matrix.mul_assoc, CFC.sqrt_mul_sqrt_self S hS.1.nonneg]
      _ = 0 := by rw [hUroot, Matrix.zero_mul]
  let K := |realTrace (H * U) - objective H B m θ κ S|
  have hK : 0 ≤ K := abs_nonneg _
  have hK1 : 0 < K + 1 := by linarith
  have hc : 0 < DyadicBoundaryGain.scale m θ := DyadicBoundaryGain.scale_pos hm hθ
  have hsmall : 0 < min 1 (DyadicBoundaryGain.scale m θ / (K + 1)) :=
    lt_min (by norm_num) (div_pos hc hK1)
  obtain ⟨r, hr, hrsmall⟩ := exists_between hsmall
  have hr1 : r < 1 := (lt_min_iff.mp hrsmall).1
  have hrK1 : r * (K + 1) < DyadicBoundaryGain.scale m θ :=
    (lt_div_iff₀ hK1).mp (lt_min_iff.mp hrsmall).2
  have hrK : K * r < DyadicBoundaryGain.scale m θ := by nlinarith
  have he : (2 ^ m - 1) + 1 = 2 ^ m := by have := DyadicBoundaryGain.order_ge_two hm; omega
  have hgain : 0 < DyadicBoundaryGain.scale m θ * r ^ (2 ^ m - 1) - r ^ (2 ^ m) * K := by
    calc
      0 < r ^ (2 ^ m - 1) * (DyadicBoundaryGain.scale m θ - K * r) :=
        mul_pos (pow_pos hr _) (sub_pos.mpr hrK)
      _ = _ := by rw [show r ^ (2 ^ m) = r ^ (2 ^ m - 1) * r by rw [← pow_succ, he]]; ring
  have ha : 0 ≤ 1 - r ^ (2 ^ m) := sub_nonneg.mpr (pow_le_one₀ hr.le hr1.le)
  have hb : 0 ≤ r ^ (2 ^ m) := pow_nonneg hr.le _
  have hmix : (1 - r ^ (2 ^ m)) • S + r ^ (2 ^ m) • U ∈ densitySet :=
    densitySet_convex hS ⟨hU, htrace⟩ ha hb (by ring)
  have hlower := kernel_perturbation_lower H B hm hθ.le hκ hS.1 hU htrace hUU hSU hUS hr.le hr1.le
  have hupper := hmax _ hmix
  have herr : -K ≤ realTrace (H * U) - objective H B m θ κ S := neg_abs_le _
  have herr' := mul_le_mul_of_nonneg_left herr hb
  nlinarith

theorem optimizer_posDef [Nonempty n] (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    {m : ℕ} (hm : 1 ≤ m) {θ κ : ℝ} (hθ : 0 < θ) (hκ : 0 ≤ κ) :
    (optimizer H B m θ κ).PosDef :=
  maximizer_posDef H B hm hθ hκ (optimizer_mem H B m θ κ) (optimizer_max H B m θ κ)

theorem strict_concave_posDef (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    {m : ℕ} (hm : 1 ≤ m) {θ κ : ℝ} (hθ : 0 < θ) (hκ : 0 ≤ κ)
    {S T : Matrix n n ℂ} (hS : S.PosDef) (hT : T.PosDef) (hne : S ≠ T)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    a * objective H B m θ κ S + b * objective H B m θ κ T <
      objective H B m θ κ (a • S + b • T) := by
  have hd := dyadicDensityObjective_strict_concave_posDef H B m hm θ hθ hS hT hne ha hb hab
  have hr := mul_le_mul_of_nonneg_left (trace_sqrt_concave hS.posSemidef hT.posSemidef
    ha.le hb.le hab) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hκ)
  dsimp [objective]
  nlinarith

theorem maximizers_eq (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    {m : ℕ} (hm : 1 ≤ m) {θ κ : ℝ} (hθ : 0 < θ) (hκ : 0 ≤ κ)
    {S T : Matrix n n ℂ} (hS : S ∈ densitySet) (hT : T ∈ densitySet)
    (hsmax : ∀ U ∈ densitySet, objective H B m θ κ U ≤ objective H B m θ κ S)
    (htmax : ∀ U ∈ densitySet, objective H B m θ κ U ≤ objective H B m θ κ T) : S = T := by
  by_contra hne
  have hmix := densitySet_convex hS hT (by norm_num : (0 : ℝ) ≤ 1/2)
    (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) + 1/2 = 1)
  have hstrict := strict_concave_posDef H B hm hθ hκ
    (maximizer_posDef H B hm hθ hκ hS hsmax) (maximizer_posDef H B hm hθ hκ hT htmax)
    hne (by norm_num : (0 : ℝ) < 1/2) (by norm_num : (0 : ℝ) < 1/2) (by norm_num)
  have hs := hsmax _ hmix
  have ht := htmax _ hmix
  linarith

theorem existsUnique_optimizer [Nonempty n] (H : Matrix n n ℂ)
    (B : ι → Matrix n n ℂ) {m : ℕ} (hm : 1 ≤ m) {θ κ : ℝ}
    (hθ : 0 < θ) (hκ : 0 ≤ κ) :
    ∃! S : Matrix n n ℂ, S ∈ densitySet ∧
      ∀ T ∈ densitySet, objective H B m θ κ T ≤ objective H B m θ κ S := by
  obtain ⟨S, hS, hmax⟩ := exists_maximizer H B m θ κ
  refine ⟨S, ⟨hS, hmax⟩, ?_⟩
  intro T hT
  exact maximizers_eq H B hm hθ hκ hT.1 hS hT.2 hmax

end MatrixSpencer.RectangularRidgePotential
