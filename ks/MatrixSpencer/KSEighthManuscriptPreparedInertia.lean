import MatrixSpencer.KSEighthManuscriptInertia
import MatrixSpencer.KSEighthPreparedHessian
import MatrixSpencer.KSEighthFacePotential



open Matrix Filter Topology Set Module
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSEighthManuscriptPreparedInertia
open KSPotentialModels KSLiveCurve KSEighthPreparedHessian
variable {N : ℕ} {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

theorem exists_large_negative_curve_subspace_of_exhaustion
    (v : Fin N → n → ℂ) {θ τ : ℝ} (hθ : 0 < θ) (hτ : 0 ≤ τ)
    (report : (Fin N → ℝ) → ℝ)
    (haccuracy : ∀ y ∈ ksCube (1/8),
      |report y - eighthPotential (fun j => KSRankOne.atom (v j)) θ y| ≤ τ/8)
    {x : Fin N → ℝ} (hx : x ∈ ksCube (1/8))
    (hex : KSEighthRetirementLoop.select (1/8) τ report x = none)
    [Nonempty (Live (1/8) x)] :
    ∃ W : Submodule ℝ (Live (1/8) x → ℝ),
      (13 / 16 : ℝ) * Fintype.card (Live (1/8) x) < (Module.finrank ℝ W : ℝ) ∧
      ∀ y ∈ W, y ≠ 0 →
      deriv (KSEighthLocalState.curvePotential (center (fun i => KSRankOne.atom (v i)) x)
        (fun i : Live (1/8) x => v i) θ (fun i => x i) (KSEighthBalanced.direction (fun i => x i) y)) 0 = 0 ∧
      iteratedDeriv 2 (KSEighthLocalState.curvePotential (center (fun i => KSRankOne.atom (v i)) x)
        (fun i : Live (1/8) x => v i) θ (fun i => x i) (KSEighthBalanced.direction (fun i => x i) y)) 0 < 0 := by
  let vl : Live (1/8) x → n → ℂ := fun i => v i
  let xl : Live (1/8) x → ℝ := fun i => x i
  let Q := center (fun i => KSRankOne.atom (v i)) x
  have hxl : ∀ i : Live (1/8) x, |xl i| ≤ (1/8 : ℝ) := fun i => i.property.le
  have hvl : ∀ i, vl i ≠ 0 := live_vector_ne_zero v θ hτ report haccuracy hx hex
  have hns₁ : ∀ i : Live (1/8) x,
      KSEighthBalanced.owner xl i * KSEighthBalanced.probe (KSEighthSupport.compressedVector vl)
        (KSEighthActualState.transport Q vl xl θ true) i < 1/8-xl i := by
    intro i
    apply lt_of_not_ge
    intro hs
    have hother := mul_nonneg (KSEighthBalanced.owner_pos xl hxl i).le
      (KSEighthActualRetirement.actual_probe_nonneg Q vl hvl xl hxl hθ i false)
    have hret := KSEighthActualRetirement.actual_retire Q vl hvl xl hxl hθ i (1/8-xl i) hs
      (by have hi := (abs_le.mp (hxl i)).2; linarith)
    have hr := rejected_endpoint v θ hτ report haccuracy hx hex i i.property (Or.inr rfl)
    rw [KSEighthLiveSource.potential_endpoint v hx hθ i (Or.inr rfl),
      KSEighthLiveSource.potential_state v hx hθ] at hr
    exact (not_lt_of_ge hret) hr
  have hns₂ : ∀ i : Live (1/8) x,
      KSEighthBalanced.owner xl i * KSEighthBalanced.probe (KSEighthSupport.compressedVector vl)
        (KSEighthActualState.transport Q vl xl θ false) i < 1/8+xl i := by
    intro i
    apply lt_of_not_ge
    intro hs
    have hother := mul_nonneg (KSEighthBalanced.owner_pos xl hxl i).le
      (KSEighthActualRetirement.actual_probe_nonneg Q vl hvl xl hxl hθ i true)
    have hret := KSEighthActualRetirement.actual_retire Q vl hvl xl hxl hθ i (-(1/8)-xl i)
      (by have hi := (abs_le.mp (hxl i)).1; linarith) (by linarith)
    have hr := rejected_endpoint v θ hτ report haccuracy hx hex i i.property (Or.inl rfl)
    rw [KSEighthLiveSource.potential_endpoint v hx hθ i (Or.inl rfl),
      KSEighthLiveSource.potential_state v hx hθ] at hr
    exact (not_lt_of_ge hret) hr
  exact KSEighthManuscriptInertia.exists_large_negative_curve_subspace Q
    (center_isHermitian _ (fun i => KSRankOne.atom_isHermitian (v i)) x)
    vl hvl xl hxl hθ hns₁ hns₂



def hessian (v : Fin N → n → ℂ) (θ : ℝ) (x : Fin N → ℝ) :
    Matrix (Fin (KSEighthLiveEnumeration.count x)) (Fin (KSEighthLiveEnumeration.count x)) ℝ :=
  (1 / 2 : ℝ) • KSNumericalHessian.hessian (KSEighthFacePotential.potential v θ x) 0

/-- Reindexing is the actual finite live-label enumeration, without changing
which labels share one coefficient. -/
def reindex (x : Fin N → ℝ) :
    (Live (1/8) x → ℝ) ≃ₗ[ℝ] (Fin (KSEighthLiveEnumeration.count x) → ℝ) :=
  LinearEquiv.funCongrLeft ℝ ℝ (KSEighthLiveEnumeration.liveEquiv x)

theorem lineDirection_reindex (x : Fin N → ℝ) (y : Live (1/8) x → ℝ) :
    KSEighthFacePotential.lineDirection x (WithLp.toLp 2 (reindex x y)) =
      KSEighthBalanced.direction (fun i : Live (1/8) x => x i) y := by
  funext i
  rw [KSEighthFacePotential.lineDirection, KSEighthLiveCoordinates.weightedMap_apply,
    KSEighthLiveEnumeration.extend_live,
    KSEighthBalanced.direction_eq _ _ (fun i => i.property.le)]
  change Real.sqrt (1 - x i ^ 2) *
    y (KSEighthLiveEnumeration.liveEquiv x ((KSEighthLiveEnumeration.liveEquiv x).symm i)) = _
  rw [Equiv.apply_symm_apply]


theorem exists_large_negative_hessian_of_exhaustion
    (v : Fin N → n → ℂ) {θ τ : ℝ} (hθ : 0 < θ) (hτ : 0 ≤ τ)
    (report : (Fin N → ℝ) → ℝ)
    (haccuracy : ∀ y ∈ ksCube (1/8),
      |report y - eighthPotential (fun j => KSRankOne.atom (v j)) θ y| ≤ τ/8)
    {x : Fin N → ℝ} (hx : x ∈ ksCube (1/8))
    (hex : KSEighthRetirementLoop.select (1/8) τ report x = none)
    [Nonempty (Live (1/8) x)] :
    ∃ W : Submodule ℝ (Fin (KSEighthLiveEnumeration.count x) → ℝ),
      (13 / 16 : ℝ) * KSEighthLiveEnumeration.count x < (finrank ℝ W : ℝ) ∧
      KSEighthInertia.StrictlyNegativeOn (hessian v θ x) W := by
  obtain ⟨W, hdim, hW⟩ := exists_large_negative_curve_subspace_of_exhaustion
    v hθ hτ report haccuracy hx hex
  refine ⟨W.map (reindex x).toLinearMap, ?_, ?_⟩
  · rw [(reindex x).finrank_map_eq]
    have hc : Fintype.card (Live (1/8) x) = KSEighthLiveEnumeration.count x :=
      (Fintype.card_congr (KSEighthLiveEnumeration.liveEquiv x)).symm.trans (Fintype.card_fin _)
    rwa [hc] at hdim
  · intro z hz hzne
    rcases hz with ⟨y, hy, rfl⟩
    have hyne : y ≠ 0 := by intro h; apply hzne; simp [h]
    have hdd := (hW y hy hyne).2
    let w := WithLp.toLp 2 (reindex x y)
    have he : (fun t : ℝ => KSEighthFacePotential.potential v θ x (t • w)) =
        KSEighthLocalState.curvePotential (center (fun i => KSRankOne.atom (v i)) x)
          (fun i : Live (1/8) x => v i) θ (fun i => x i)
          (KSEighthBalanced.direction (fun i => x i) y) := by
      funext t
      rw [KSEighthFacePotential.potential_line_eq, lineDirection_reindex]
    rw [← he] at hdd
    have hs : ContDiffAt ℝ 2 (KSEighthFacePotential.potential v θ x) 0 :=
      (KSEighthFacePotential.contDiffAt_potential v hθ x).of_le
        (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
    have hd := KSFourthDifference.line_second (KSEighthFacePotential.potential v θ x) 0 w hs
    simp only [zero_add] at hd
    rw [hd, ← KSNumericalHessian.hessian_rayleigh,
      KSRayleighAccuracy.realRayleigh_eq_quadratic] at hdd
    change reindex x y ⬝ᵥ ((hessian v θ x) *ᵥ reindex x y) < 0
    simp only [hessian, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
    exact mul_neg_of_pos_of_neg (by norm_num) hdd

/-- Actual finite reports discharge the sole accuracy premise of the generic
exhausted-test theorem. This is the large inertia of the prepared state itself. -/
theorem numerical_prepared_large_inertia {d : ℕ}
    (v : Fin N → Fin d → ℂ) {θ τ ρ : ℝ} (hθ : 0 < θ) (hτ : 0 < τ) (hd : 0 < d)
    (s : KSEighthWalkRun.PreparedState N ρ τ
      (KSEighthNumericalValue.stateReport v θ hd (τ/8)))
    (hactive : ¬KSEighthWalkRun.terminal s) :
    ∃ W : Submodule ℝ (Fin (KSEighthLiveEnumeration.count s.coeff) → ℝ),
      (13 / 16 : ℝ) * KSEighthLiveEnumeration.count s.coeff < (finrank ℝ W : ℝ) ∧
      KSEighthInertia.StrictlyNegativeOn (hessian v θ s.coeff) W := by
  classical
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  have hlive := KSEighthLiveEnumeration.count_pos_of_not_vertex s.cube hactive
  letI : Nonempty (Live (1/8) s.coeff) :=
    ⟨KSEighthLiveEnumeration.liveEquiv s.coeff ⟨0,hlive⟩⟩
  exact exists_large_negative_hessian_of_exhaustion v hθ hτ.le _
    (fun x hx => KSEighthNumericalValue.stateReport_accuracy v hθ
      (div_pos hτ (by norm_num)) hd hx) s.cube s.exhausted

end MatrixSpencer.KSEighthManuscriptPreparedInertia
