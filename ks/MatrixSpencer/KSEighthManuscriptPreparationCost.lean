import MatrixSpencer.KSEighthPreparationCost



open Matrix Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSEighthManuscriptPreparationCost
open KSPotentialModels KSEighthRetirementLoop KSEighthPreparationCost
variable {N : ℕ} {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
local instance : CStarAlgebra (Matrix n n ℂ) := {}

/-- Parseval input itself supplies the unit atom cap; it is not an additional
analytic or algorithmic assumption. -/
theorem signed_atom_norm_le_one (v : Fin N → n → ℂ)
    (hparseval : (∑ i, KSRankOne.atom (v i)) = 1) (i : Fin N) :
    ‖signedLift (KSRankOne.atom (v i))‖ ≤ 1 := by
  rw [signedLift_norm (KSRankOne.atom_isHermitian (v i))]
  have hle : KSRankOne.atom (v i) ≤ 1 := by
    rw [← hparseval]
    exact Finset.single_le_sum
      (fun j (_ : j ∈ Finset.univ) => (KSRankOne.atom_posSemidef (v j)).nonneg)
      (Finset.mem_univ i)
  apply (CStarAlgebra.norm_le_iff_le_algebraMap _ zero_le_one
    (KSRankOne.atom_posSemidef (v i)).nonneg).mpr
  simpa using hle

omit [Nonempty n] in
theorem snap_center_norm_le (v : Fin N → n → ℂ)
    (hbound : ∀i, ‖signedLift (KSRankOne.atom (v i))‖ ≤ 1) {ρ : ℝ} (hρ : 0 ≤ ρ)
    {x : Fin N → ℝ} (hx : x ∈ ksCube (1/8)) :
    ‖signedLift (center (fun i => KSRankOne.atom (v i)) (KSCubePreparation.snap (1/8) ρ x)) -
      signedLift (center (fun i => KSRankOne.atom (v i)) x)‖ ≤
      ρ * (1 : ℝ) * (frozenCount (1/8) (KSCubePreparation.snap (1/8) ρ x)-frozenCount (1/8) x) := by
  rw [KSPotentialModels.center, KSPotentialModels.center, signedLift_sum_smul, signedLift_sum_smul,
    ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, ‖KSCubePreparation.snap (1/8) ρ x i • signedLift (KSRankOne.atom (v i)) -
        x i • signedLift (KSRankOne.atom (v i))‖ := norm_sum_le _ _
    _ = ∑ i, |KSCubePreparation.snap (1/8) ρ x i-x i| * ‖signedLift (KSRankOne.atom (v i))‖ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← sub_smul, norm_smul, Real.norm_eq_abs]
    _ ≤ ∑ i, |KSCubePreparation.snap (1/8) ρ x i-x i| * (1 : ℝ) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hbound i) (abs_nonneg _))
    _ = (∑ i, |KSCubePreparation.snap (1/8) ρ x i-x i|) * (1 : ℝ) := (Finset.sum_mul _ _ _).symm
    _ ≤ (ρ * (frozenCount (1/8) (KSCubePreparation.snap (1/8) ρ x)-frozenCount (1/8) x)) * (1 : ℝ) :=
      mul_le_mul_of_nonneg_right (snap_sum_displacement (by norm_num) hρ hx) zero_le_one
    _ = _ := by ring

theorem snap_potential_cost (v : Fin N → n → ℂ)
    (hbound : ∀i, ‖signedLift (KSRankOne.atom (v i))‖ ≤ 1) (θ : ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ)
    {x : Fin N → ℝ} (hx : x ∈ ksCube (1/8)) :
    eighthPotential (fun i => KSRankOne.atom (v i)) θ (KSCubePreparation.snap (1/8) ρ x) ≤
      eighthPotential (fun i => KSRankOne.atom (v i)) θ x +
      ρ * (1 : ℝ) * (frozenCount (1/8) (KSCubePreparation.snap (1/8) ρ x)-frozenCount (1/8) x) := by
  let A := fun i => KSRankOne.atom (v i)
  let y := KSCubePreparation.snap (1/8) ρ x
  have hA : ∀ i, (A i).IsHermitian := fun i => KSRankOne.atom_isHermitian (v i)
  have hxowner : ∀ i, 0 ≤ truncatedOwners (1/8) 64 x i :=
    maskedOwners_nonneg (by norm_num) (by norm_num) hx _
  have hyowner : ∀ i, 0 ≤ truncatedOwners (1/8) 64 y i :=
    maskedOwners_nonneg (by norm_num) (by norm_num) (KSCubePreparation.snap_mem_cube (by norm_num) hx) _
  have hmono := commonPotential_mono A hA θ y hyowner hxowner
    (snap_owners_le (by norm_num) (by norm_num) hx)
  have hcenter := owner_center_cost (signedLift (center A x)) (signedLift (center A y))
    (signedLift_isHermitian (center_isHermitian A hA x))
    (signedLift_isHermitian (center_isHermitian A hA y))
    (KSCommonSource.family A) (KSCommonSource.family_isHermitian A hA)
    (KSCommonSource.coefficientCovariance_posSemidef hxowner) θ
  have hnorm := snap_center_norm_le v hbound hρ hx
  exact hmono.trans (hcenter.trans (add_le_add_left hnorm _))

theorem prepareState_potential_cost (v : Fin N → n → ℂ)
    (hbound : ∀i, ‖signedLift (KSRankOne.atom (v i))‖ ≤ 1) (θ : ℝ)
    {ρ τ : ℝ} (hρ : 0 ≤ ρ) (hτ : 0 ≤ τ)
    (report : (Fin N → ℝ) → ℝ)
    (hacc : ∀ x ∈ ksCube (1/8), |report x-eighthPotential (fun i => KSRankOne.atom (v i)) θ x| ≤ τ/8)
    {x : Fin N → ℝ} (hx : x ∈ ksCube (1/8)) :
    eighthPotential (fun i => KSRankOne.atom (v i)) θ
        (KSEighthPreparedState.prepareState (1/8) τ ρ report x) ≤
      eighthPotential (fun i => KSRankOne.atom (v i)) θ x +
      (ρ+τ) * (frozenCount (1/8) (KSEighthPreparedState.prepareState (1/8) τ ρ report x)-frozenCount (1/8) x) := by
  have hs := snap_potential_cost v hbound θ hρ hx
  have hp := prepare_cost (by norm_num : (0 : ℝ) ≤ 1/8) hτ report _ hacc N
    (KSCubePreparation.snap_mem_cube (by norm_num) hx (ρ := ρ))
  have hcount₁ := snap_count_mono (a := (1/8 : ℝ)) (ρ := ρ) x
  have hcount₂ := frozenCount_mono
    (prepare_preserves_frozen (a := (1/8 : ℝ)) (τ := τ) report N (KSCubePreparation.snap (1/8) ρ x))
  have ha : (0 : ℝ) < 1 := zero_lt_one
  change _ ≤ _ + (ρ+τ) *
    (frozenCount (1/8) (prepare (1/8) τ report N (KSCubePreparation.snap (1/8) ρ x))-frozenCount (1/8) x)
  dsimp only [KSEighthPreparedState.prepareState]
  nlinarith [mul_nonneg hτ (sub_nonneg.mpr hcount₁),
    mul_nonneg (mul_nonneg hρ ha.le) (sub_nonneg.mpr hcount₂)]

end MatrixSpencer.KSEighthManuscriptPreparationCost
