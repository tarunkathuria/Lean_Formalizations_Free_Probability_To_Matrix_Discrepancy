import MatrixSpencer.KSEighthLocalState
import MatrixSpencer.KSEighthActualRetirement
import MatrixSpencer.KSLiveCurve
import MatrixSpencer.KSSpinLiveSource
import MatrixSpencer.KSFinalAssembly

/-! Exact original-label restriction and endpoint updates for truncated owners. -/

open Matrix Filter Topology
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSEighthLiveSource
open KSPotentialModels KSLiveCurve

variable {N : ℕ} {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

theorem source_restrict (v : Fin N → n → ℂ) (a : ℝ) (x c : Fin N → ℝ)
    (hzero : ∀ i, ¬ |x i| < a → c i = 0) (X : Matrix (n ⊕ n) (n ⊕ n) ℂ) :
    covarianceSource (KSIndependentSource.family (fun i => KSRankOne.atom (v i)))
      (KSIndependentSource.coefficientCovariance c) X =
    covarianceSource (KSIndependentSource.family (fun i : Live a x => KSRankOne.atom (v i)))
      (KSIndependentSource.coefficientCovariance (fun i : Live a x => c i)) X := by
  rw [KSIndependentSource.source_eq_sum, KSIndependentSource.source_eq_sum]
  apply sum_restrict_live a x
  intro i hi
  simp only [hzero i hi, zero_smul]

theorem potential_restrict (v : Fin N → n → ℂ) (a : ℝ) (x c : Fin N → ℝ)
    (hzero : ∀ i, ¬ |x i| < a → c i = 0) (H : Matrix (n ⊕ n) (n ⊕ n) ℂ) (θ : ℝ) :
    ownerPotential H (KSIndependentSource.family (fun i => KSRankOne.atom (v i)))
      (KSIndependentSource.coefficientCovariance c) θ =
    ownerPotential H (KSIndependentSource.family (fun i : Live a x => KSRankOne.atom (v i)))
      (KSIndependentSource.coefficientCovariance (fun i : Live a x => c i)) θ := by
  unfold ownerPotential
  congr 2
  funext X
  unfold ownerObjective
  rw [source_restrict v a x c hzero X]

theorem truncated_dead (a u : ℝ) (x : Fin N → ℝ) (i : Fin N) (hi : ¬ |x i| < a) :
    truncatedOwners a u x i = 0 := by
  simp [truncatedOwners, maskedOwners, live, hi]

theorem truncated_live (a u : ℝ) (x : Fin N → ℝ) (i : Live a x) :
    truncatedOwners a u x i = naturalOwners u x i := by
  simp [truncatedOwners, maskedOwners, live, i.property]

theorem potential_state (v : Fin N → n → ℂ) {x : Fin N → ℝ}
    (hx : x ∈ ksCube (1 / 8)) {θ : ℝ} (hθ : 0 < θ) :
    eighthPotential (fun i => KSRankOne.atom (v i)) θ x =
    ownerPotential (signedLift (center (fun i => KSRankOne.atom (v i)) x))
      (KSEighthActualState.family (fun i : Live (1 / 8) x => v i))
      (KSEighthActualState.covariance (fun i : Live (1 / 8) x => x i)) θ := by
  have hc : ∀ i, 0 ≤ truncatedOwners (1 / 8) 64 x i :=
    fun i => maskedOwners_nonneg (by norm_num) (by norm_num) hx (live (1 / 8) x) i
  unfold eighthPotential commonPotential
  rw [KSCommonSource.potential_eq_independent _ (fun i => KSRankOne.atom (v i))
    (fun i => KSRankOne.atom_isHermitian (v i)) hc hθ,
    potential_restrict v (1 / 8) x _ (truncated_dead (1 / 8) 64 x)]
  congr 2
  funext i
  exact truncated_live (1 / 8) 64 x i

theorem restricted_update (x : Fin N → ℝ) (i : Live (1 / 8) x) :
    (fun j : Live (1 / 8) x => Function.update (truncatedOwners (1 / 8) 64 x) i 0 j) =
      Function.update (KSEighthBalanced.owner (fun j : Live (1 / 8) x => x j)) i 0 := by
  funext j
  by_cases hji : j = i
  · subst j; simp only [Function.update_self]
  · have hval : j.val ≠ i.val := fun he => hji (Subtype.ext he)
    rw [Function.update_of_ne hval, Function.update_of_ne hji, truncated_live]
    rfl

theorem potential_endpoint (v : Fin N → n → ℂ) {x : Fin N → ℝ}
    (hx : x ∈ ksCube (1 / 8)) {θ : ℝ} (hθ : 0 < θ) (i : Live (1 / 8) x)
    {s : ℝ} (hs : s = -(1 / 8 : ℝ) ∨ s = 1 / 8) :
    eighthPotential (fun j => KSRankOne.atom (v j)) θ (Function.update x i s) =
    ownerPotential (signedLift (center (fun j => KSRankOne.atom (v j)) x) +
        (s - x i) • signedLift (KSRankOne.atom (v i)))
      (KSEighthActualState.family (fun j : Live (1 / 8) x => v j))
      (KSIndependentSource.coefficientCovariance
        (Function.update (KSEighthBalanced.owner (fun j : Live (1 / 8) x => x j)) i 0)) θ := by
  have hy := ksCube_update_endpoint (by norm_num : (0 : ℝ) ≤ 1 / 8) hx i hs
  have hc : ∀ j, 0 ≤ truncatedOwners (1 / 8) 64 (Function.update x i s) j :=
    fun j => maskedOwners_nonneg (by norm_num) (by norm_num) hy _ j
  unfold eighthPotential commonPotential
  rw [KSCommonSource.potential_eq_independent _ (fun j => KSRankOne.atom (v j))
    (fun j => KSRankOne.atom_isHermitian (v j)) hc hθ,
    signed_center_update, truncatedOwners_update_endpoint 64 (by norm_num) x i hs]
  have hzero : ∀ j, ¬ |x j| < (1 / 8 : ℝ) →
      Function.update (truncatedOwners (1 / 8) 64 x) i 0 j = 0 := by
    intro j hj
    by_cases hji : j = i.val
    · subst j; rw [Function.update_self]
    · rw [Function.update_of_ne hji]
      exact truncated_dead (1 / 8) 64 x j hj
  rw [potential_restrict v (1 / 8) x _ hzero, restricted_update]
  rfl

theorem potential_path (v : Fin N → n → ℂ) {x : Fin N → ℝ}
    (hx : x ∈ ksCube (1 / 8)) {θ : ℝ} (hθ : 0 < θ) (h : Live (1 / 8) x → ℝ) :
    (fun t => eighthPotential (fun i => KSRankOne.atom (v i)) θ (path (1 / 8) x h t)) =ᶠ[𝓝 (0 : ℝ)]
      KSEighthLocalState.curvePotential (center (fun i => KSRankOne.atom (v i)) x)
        (fun i : Live (1 / 8) x => v i) θ (fun i : Live (1 / 8) x => x i) h := by
  filter_upwards [eventually_in_cube hx h, eventually_same_live x h, eventually_live x h] with t ht hl hlt
  have hc : ∀ i, 0 ≤ truncatedOwners (1 / 8) 64 (path (1 / 8) x h t) i :=
    fun i => maskedOwners_nonneg (by norm_num) (by norm_num) ht _ i
  unfold eighthPotential commonPotential KSEighthLocalState.curvePotential KSEighthLocalState.curveCenter
  rw [KSCommonSource.potential_eq_independent _ (fun i => KSRankOne.atom (v i))
    (fun i => KSRankOne.atom_isHermitian (v i)) hc hθ]
  have hzero : ∀ i, ¬ |x i| < (1 / 8 : ℝ) → truncatedOwners (1 / 8) 64 (path (1 / 8) x h t) i = 0 := by
    intro i hi
    apply truncated_dead
    rw [path_dead _ _ _ _ _ hi]
    exact hi
  rw [potential_restrict v (1 / 8) x _ hzero]
  have hcenter := KSSpinLiveSource.signed_center_path (fun i => KSRankOne.atom (v i)) (1 / 8) x h t
  rw [hcenter]
  congr 2
  funext i
  have hei : truncatedOwners (1 / 8) 64 (path (1 / 8) x h t) i =
      naturalOwners 64 (path (1 / 8) x h t) i := by
    exact truncated_live (1 / 8) 64 (path (1 / 8) x h t) ⟨i, hlt i⟩
  rw [hei]
  simp only [naturalOwners, path_live, KSEighthLocalState.curveOwners]

end MatrixSpencer.KSEighthLiveSource
