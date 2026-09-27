import MatrixSpencer.KSEighthLiveSource
import MatrixSpencer.KSEighthPreparedState
import MatrixSpencer.KSEighthNumericalValue
import MatrixSpencer.KSOwnerInputBounds

/-!
# Amortized cost of the actual eighth-cube preparation

The potential allowance is charged to newly frozen original labels. Thus a
finite walk pays for snapping and endpoint tests at most once per label,
rather than once per movement. Every statement concerns the defined snap
and finite retirement loop.
-/

open Matrix Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSEighthPreparationCost
open KSPotentialModels KSEighthRetirementLoop
variable {N : ℕ}

/-- Real-valued count, used only for proof bookkeeping. -/
def frozenCount (a : ℝ) (x : Fin N → ℝ) : ℝ := (ksFrozen a x).card

theorem frozenCount_mono {a : ℝ} {x y : Fin N → ℝ}
    (h : ∀ i, |x i| = a → y i = x i) : frozenCount a x ≤ frozenCount a y := by
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro i hi
  simp only [ksFrozen, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  rwa [h i hi]

theorem prepare_cost {a τ : ℝ} (ha : 0 ≤ a) (hτ : 0 ≤ τ)
    (report F : (Fin N → ℝ) → ℝ)
    (haccuracy : ∀ x ∈ ksCube a, |report x - F x| ≤ τ/8)
    (k : ℕ) {x : Fin N → ℝ} (hx : x ∈ ksCube a) :
    F (prepare a τ report k x) ≤ F x +
      τ * (frozenCount a (prepare a τ report k x) - frozenCount a x) := by
  induction k generalizing x with
  | zero => simp [prepare]
  | succ k ih =>
    cases hs : select a τ report x with
    | none => simp only [prepare, hs, sub_self, mul_zero, add_zero, le_refl]
    | some c =>
      have hu := update_mem_cube ha hx c
      have hcost := accepted_true_cost (select_some hs) (haccuracy x hx) (haccuracy _ hu)
      have hrest := ih hu
      have hinc : frozenCount a x + 1 ≤ frozenCount a (update a x c) := by
        have hn := Nat.succ_le_of_lt (update_frozen_lt ha (select_some hs))
        dsimp only [frozenCount]
        exact_mod_cast hn
      have hcharge := mul_le_mul_of_nonneg_left hinc hτ
      simp only [prepare, hs]
      nlinarith

theorem snap_count_mono {a ρ : ℝ} (x : Fin N → ℝ) :
    frozenCount a x ≤ frozenCount a (KSCubePreparation.snap a ρ x) :=
  frozenCount_mono (KSCubePreparation.snap_preserves_frozen x)

theorem snap_dead_eq {a ρ : ℝ} (ha : 0 ≤ a) (x : Fin N → ℝ) (i : Fin N)
    (hi : i ∉ ksFrozen a (KSCubePreparation.snap a ρ x) \ ksFrozen a x) :
    KSCubePreparation.snap a ρ x i = x i := by
  classical
  by_cases hf : |x i| = a
  · exact KSCubePreparation.snap_preserves_frozen x i hf
  · have hn : ¬ |KSCubePreparation.snap a ρ x i| = a := by
      intro he
      apply hi
      simp only [Finset.mem_sdiff, ksFrozen, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨he,hf⟩
    unfold KSCubePreparation.snap at *
    split_ifs with h
    · exact False.elim (hn (by rw [if_pos h]; exact KSCubePreparation.endpoint_abs ha _))
    · rfl

theorem snap_sum_displacement {a ρ : ℝ} (ha : 0 ≤ a) (hρ : 0 ≤ ρ)
    {x : Fin N → ℝ} (hx : x ∈ ksCube a) :
    (∑ i, |KSCubePreparation.snap a ρ x i-x i|) ≤
      ρ * (frozenCount a (KSCubePreparation.snap a ρ x)-frozenCount a x) := by
  classical
  let D := ksFrozen a (KSCubePreparation.snap a ρ x) \ ksFrozen a x
  have hsub : ksFrozen a x ⊆ ksFrozen a (KSCubePreparation.snap a ρ x) := by
    intro i hi
    simp only [ksFrozen, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    rwa [KSCubePreparation.snap_preserves_frozen x i hi]
  have he : (D.card : ℝ) = frozenCount a (KSCubePreparation.snap a ρ x)-frozenCount a x := by
    rw [show D.card = _ from Finset.card_sdiff_of_subset hsub, Nat.cast_sub (Finset.card_le_card hsub)]
    rfl
  calc
    _ = ∑ i ∈ D, |KSCubePreparation.snap a ρ x i-x i| := by
      symm
      apply Finset.sum_subset (Finset.subset_univ D)
      intro i _ hi
      rw [snap_dead_eq ha x i hi, sub_self, abs_zero]
    _ ≤ ∑ _i ∈ D, ρ := Finset.sum_le_sum (fun i _ => KSCubePreparation.snap_distance_le hρ hx i)
    _ = ρ * (frozenCount a (KSCubePreparation.snap a ρ x)-frozenCount a x) := by
      simp only [Finset.sum_const, nsmul_eq_mul, he]
      ring

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
local instance : CStarAlgebra (Matrix n n ℂ) := {}

/-- A change of center costs at most its actual operator norm. -/
theorem owner_center_cost {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H H' : Matrix n n ℂ) (hH : H.IsHermitian) (hH' : H'.IsHermitian)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (θ : ℝ) :
    ownerPotential H' A C θ ≤ ownerPotential H A C θ + ‖H'-H‖ := by
  rw [ownerPotential_eq_densityPotential H' A hA hC,
    ownerPotential_eq_densityPotential H A hA hC]
  obtain ⟨S,hS,he⟩ := exists_densityPotential_eq H' (covarianceKraus A C) θ
  rw [he, densityObjective_center_difference H H']
  exact add_le_add (densityObjective_le_potential H _ θ hS)
    (realTrace_mul_density_le_norm (hH'.sub hH) hS)

/-- Snapping removes owners and leaves the surviving owners unchanged. -/
theorem snap_owners_le {a ρ : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    {x : Fin N → ℝ} (hx : x ∈ ksCube a) (i : Fin N) :
    truncatedOwners a 64 (KSCubePreparation.snap a ρ x) i ≤ truncatedOwners a 64 x i := by
  by_cases hnear : a-|x i| ≤ ρ
  · have he : |KSCubePreparation.snap a ρ x i| = a := by
      simp only [KSCubePreparation.snap, if_pos hnear, KSCubePreparation.endpoint_abs ha]
    have hd : ¬ |KSCubePreparation.snap a ρ x i| < a := by rw [he]; exact lt_irrefl _
    rw [KSEighthLiveSource.truncated_dead a 64 _ i hd]
    exact maskedOwners_nonneg (by norm_num) ha1 hx _ i
  · have he : KSCubePreparation.snap a ρ x i = x i := by
      simp only [KSCubePreparation.snap, if_neg hnear]
    simp only [truncatedOwners, maskedOwners, live, Finset.mem_filter, Finset.mem_univ,
      true_and, naturalOwners, he, le_refl]

/-- Arithmetic input bound for every signed atom; no spectral oracle is used. -/
def atomCap (v : Fin N → n → ℂ) : ℝ :=
  1 + ∑ i, KSOwnerInputBounds.matrixBound (signedLift (KSRankOne.atom (v i)))

omit [DecidableEq n] [Nonempty n] in
theorem atomCap_pos (v : Fin N → n → ℂ) : 0 < atomCap v := by
  have h := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) =>
    (KSOwnerInputBounds.matrixBound_pos (signedLift (KSRankOne.atom (v i)))).le)
  unfold atomCap
  linarith

omit [Nonempty n] in
theorem atom_norm_le_cap (v : Fin N → n → ℂ) (i : Fin N) :
    ‖signedLift (KSRankOne.atom (v i))‖ ≤ atomCap v := by
  apply (KSOwnerInputBounds.norm_le_matrixBound _
    (signedLift_isHermitian (KSRankOne.atom_isHermitian _))).trans
  have h := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) =>
    (KSOwnerInputBounds.matrixBound_pos (signedLift (KSRankOne.atom (v j)))).le) (Finset.mem_univ i)
  unfold atomCap
  linarith


omit [Nonempty n] in
theorem snap_center_norm_le (v : Fin N → n → ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ)
    {x : Fin N → ℝ} (hx : x ∈ ksCube (1/8)) :
    ‖signedLift (center (fun i => KSRankOne.atom (v i)) (KSCubePreparation.snap (1/8) ρ x)) -
      signedLift (center (fun i => KSRankOne.atom (v i)) x)‖ ≤
      ρ * atomCap v * (frozenCount (1/8) (KSCubePreparation.snap (1/8) ρ x)-frozenCount (1/8) x) := by
  rw [KSPotentialModels.center, KSPotentialModels.center, signedLift_sum_smul, signedLift_sum_smul,
    ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, ‖KSCubePreparation.snap (1/8) ρ x i • signedLift (KSRankOne.atom (v i)) -
        x i • signedLift (KSRankOne.atom (v i))‖ := norm_sum_le _ _
    _ = ∑ i, |KSCubePreparation.snap (1/8) ρ x i-x i| * ‖signedLift (KSRankOne.atom (v i))‖ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← sub_smul, norm_smul, Real.norm_eq_abs]
    _ ≤ ∑ i, |KSCubePreparation.snap (1/8) ρ x i-x i| * atomCap v :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (atom_norm_le_cap v i) (abs_nonneg _))
    _ = (∑ i, |KSCubePreparation.snap (1/8) ρ x i-x i|) * atomCap v := (Finset.sum_mul _ _ _).symm
    _ ≤ (ρ * (frozenCount (1/8) (KSCubePreparation.snap (1/8) ρ x)-frozenCount (1/8) x)) * atomCap v :=
      mul_le_mul_of_nonneg_right (snap_sum_displacement (by norm_num) hρ hx) (atomCap_pos v).le
    _ = _ := by ring

theorem snap_potential_cost (v : Fin N → n → ℂ) (θ : ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ)
    {x : Fin N → ℝ} (hx : x ∈ ksCube (1/8)) :
    eighthPotential (fun i => KSRankOne.atom (v i)) θ (KSCubePreparation.snap (1/8) ρ x) ≤
      eighthPotential (fun i => KSRankOne.atom (v i)) θ x +
      ρ * atomCap v * (frozenCount (1/8) (KSCubePreparation.snap (1/8) ρ x)-frozenCount (1/8) x) := by
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
  have hnorm := snap_center_norm_le v hρ hx
  exact hmono.trans (hcenter.trans (add_le_add_left hnorm _))

/-- One allowance for each original label that preparation freezes. -/
def charge (v : Fin N → n → ℂ) (ρ τ : ℝ) : ℝ := ρ * atomCap v + τ

theorem prepareState_potential_cost (v : Fin N → n → ℂ) (θ : ℝ)
    {ρ τ : ℝ} (hρ : 0 ≤ ρ) (hτ : 0 ≤ τ)
    (report : (Fin N → ℝ) → ℝ)
    (hacc : ∀ x ∈ ksCube (1/8), |report x-eighthPotential (fun i => KSRankOne.atom (v i)) θ x| ≤ τ/8)
    {x : Fin N → ℝ} (hx : x ∈ ksCube (1/8)) :
    eighthPotential (fun i => KSRankOne.atom (v i)) θ
        (KSEighthPreparedState.prepareState (1/8) τ ρ report x) ≤
      eighthPotential (fun i => KSRankOne.atom (v i)) θ x +
      charge v ρ τ * (frozenCount (1/8) (KSEighthPreparedState.prepareState (1/8) τ ρ report x)-frozenCount (1/8) x) := by
  have hs := snap_potential_cost v θ hρ hx
  have hp := prepare_cost (by norm_num : (0 : ℝ) ≤ 1/8) hτ report _ hacc N
    (KSCubePreparation.snap_mem_cube (by norm_num) hx (ρ := ρ))
  have hcount₁ := snap_count_mono (a := (1/8 : ℝ)) (ρ := ρ) x
  have hcount₂ := frozenCount_mono
    (prepare_preserves_frozen (a := (1/8 : ℝ)) (τ := τ) report N (KSCubePreparation.snap (1/8) ρ x))
  have ha := atomCap_pos v
  change _ ≤ _ + charge v ρ τ *
    (frozenCount (1/8) (prepare (1/8) τ report N (KSCubePreparation.snap (1/8) ρ x))-frozenCount (1/8) x)
  unfold charge
  dsimp only [KSEighthPreparedState.prepareState]
  nlinarith [mul_nonneg hτ (sub_nonneg.mpr hcount₁),
    mul_nonneg (mul_nonneg hρ ha.le) (sub_nonneg.mpr hcount₂)]

end MatrixSpencer.KSEighthPreparationCost

