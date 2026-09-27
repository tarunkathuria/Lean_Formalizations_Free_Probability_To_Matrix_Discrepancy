import MatrixSpencer.KSEighthHessian
import MatrixSpencer.KSEighthLiveSource
import MatrixSpencer.KSEighthWalkRun
import MatrixSpencer.KSEighthNumericalValue

/-!
# Genuine eighth-cube negative curvature after exhausted numerical tests

The original-label endpoint reports exclude every nonincreasing endpoint
update. Zero live atoms are consequently impossible, and the original eighth
transport comparison supplies a negative second derivative of the actual
retained-owner potential. The final specialization uses the proved finite
value procedure and has no report-accuracy premise.
-/

open Matrix Filter Topology Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSEighthPreparedHessian

open KSPotentialModels KSLiveCurve
variable {N : ℕ} {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

omit [Nonempty n] in
/-- Exhaustion is tested at the actual supplied state, without a compact minimum. -/
theorem rejected_endpoint (v : Fin N → n → ℂ) (θ : ℝ) {τ : ℝ} (hτ : 0 ≤ τ)
    (report : (Fin N → ℝ) → ℝ)
    (haccuracy : ∀ y ∈ ksCube (1/8),
      |report y - eighthPotential (fun j => KSRankOne.atom (v j)) θ y| ≤ τ/8)
    {x : Fin N → ℝ} (hx : x ∈ ksCube (1/8))
    (hex : KSEighthRetirementLoop.select (1/8) τ report x = none)
    (i : Fin N) (hi : |x i| < 1/8) {s : ℝ} (hs : s = -(1/8 : ℝ) ∨ s = 1/8) :
    eighthPotential (fun j => KSRankOne.atom (v j)) θ x <
      eighthPotential (fun j => KSRankOne.atom (v j)) θ (Function.update x i s) := by
  apply lt_of_not_ge
  intro hcost
  let b : Bool := if s = (1/8 : ℝ) then true else false
  have he : KSEighthRetirementLoop.endpoint (1/8) b = s := by
    rcases hs with rfl | rfl <;> norm_num [b, KSEighthRetirementLoop.endpoint]
  have hy := ksCube_update_endpoint (by norm_num : (0 : ℝ) ≤ 1/8) hx i hs
  have hacc := KSEighthRetirementLoop.exact_safe_is_accepted hτ
    (c := (i,b)) hi (F := eighthPotential (fun j => KSRankOne.atom (v j)) θ)
    (by simpa only [KSEighthRetirementLoop.update, he] using hcost)
    (haccuracy x hx) (by simpa only [KSEighthRetirementLoop.update, he] using haccuracy _ hy)
  exact KSEighthRetirementLoop.select_none hex (i,b) hacc

theorem live_vector_ne_zero (v : Fin N → n → ℂ) (θ : ℝ) {τ : ℝ} (hτ : 0 ≤ τ)
    (report : (Fin N → ℝ) → ℝ)
    (haccuracy : ∀ y ∈ ksCube (1/8),
      |report y - eighthPotential (fun j => KSRankOne.atom (v j)) θ y| ≤ τ/8)
    {x : Fin N → ℝ} (hx : x ∈ ksCube (1/8))
    (hex : KSEighthRetirementLoop.select (1/8) τ report x = none)
    (i : Live (1/8) x) : v i ≠ 0 := by
  intro hz
  have hr := rejected_endpoint v θ hτ report haccuracy hx hex i i.property (Or.inr rfl)
  have hc := KSFinalAssembly.eighth_zero_atom_retirement (fun j => KSRankOne.atom (v j))
    (fun j => KSRankOne.atom_isHermitian (v j)) θ hx i (by simp [hz])
  exact (not_lt_of_ge hc) hr

theorem exists_negative_second_curve_of_exhaustion
    (v : Fin N → n → ℂ) {θ τ : ℝ} (hθ : 0 < θ) (hτ : 0 ≤ τ)
    (report : (Fin N → ℝ) → ℝ)
    (haccuracy : ∀ y ∈ ksCube (1/8),
      |report y - eighthPotential (fun j => KSRankOne.atom (v j)) θ y| ≤ τ/8)
    {x : Fin N → ℝ} (hx : x ∈ ksCube (1/8))
    (hex : KSEighthRetirementLoop.select (1/8) τ report x = none)
    [Nonempty (Live (1/8) x)] :
    ∃ h : Live (1/8) x → ℝ, h ≠ 0 ∧
      deriv (KSEighthLocalState.curvePotential (center (fun i => KSRankOne.atom (v i)) x)
        (fun i : Live (1/8) x => v i) θ (fun i => x i) h) 0 = 0 ∧
      iteratedDeriv 2 (KSEighthLocalState.curvePotential (center (fun i => KSRankOne.atom (v i)) x)
        (fun i : Live (1/8) x => v i) θ (fun i => x i) h) 0 < 0 := by
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
  exact KSEighthHessian.exists_negative_second_curve Q
    (center_isHermitian _ (fun i => KSRankOne.atom_isHermitian (v i)) x)
    vl hvl xl hxl hθ hns₁ hns₂

/-- Curvature is transferred to the actual discontinuous globally defined
potential along its current open face; no endpoint is crossed locally. -/
theorem exists_negative_second_of_exhaustion
    (v : Fin N → n → ℂ) {θ τ : ℝ} (hθ : 0 < θ) (hτ : 0 ≤ τ)
    (report : (Fin N → ℝ) → ℝ)
    (haccuracy : ∀ y ∈ ksCube (1/8),
      |report y - eighthPotential (fun j => KSRankOne.atom (v j)) θ y| ≤ τ/8)
    {x : Fin N → ℝ} (hx : x ∈ ksCube (1/8))
    (hex : KSEighthRetirementLoop.select (1/8) τ report x = none)
    [Nonempty (Live (1/8) x)] :
    ∃ h : Live (1/8) x → ℝ, h ≠ 0 ∧ extend (1/8) x h ≠ 0 ∧
      deriv (fun t => eighthPotential (fun j => KSRankOne.atom (v j)) θ (path (1/8) x h t)) 0 = 0 ∧
      iteratedDeriv 2 (fun t => eighthPotential (fun j => KSRankOne.atom (v j)) θ (path (1/8) x h t)) 0 < 0 := by
  obtain ⟨h, hn, hd, hdd⟩ := exists_negative_second_curve_of_exhaustion v hθ hτ report haccuracy hx hex
  have he := KSEighthLiveSource.potential_path v hx hθ h
  refine ⟨h, hn, extend_ne_zero _ _ hn, ?_, ?_⟩
  · exact he.deriv_eq.trans hd
  · rw [he.iteratedDeriv_eq 2]
    exact hdd

/-- The real numerical eighth state satisfies the curvature conclusion from
its actual finite report; no reporting or no-retirement oracle is assumed. -/
theorem numerical_prepared_negative_second {d : ℕ}
    (v : Fin N → Fin d → ℂ) {θ τ ρ : ℝ} (hθ : 0 < θ) (hτ : 0 < τ) (hd : 0 < d)
    (s : KSEighthWalkRun.PreparedState N ρ τ
      (KSEighthNumericalValue.stateReport v θ hd (τ/8)))
    (hactive : ¬KSEighthWalkRun.terminal s) :
    ∃ h : Live (1/8) s.coeff → ℝ, h ≠ 0 ∧ extend (1/8) s.coeff h ≠ 0 ∧
      deriv (fun t => eighthPotential (fun j => KSRankOne.atom (v j)) θ
        (path (1/8) s.coeff h t)) 0 = 0 ∧
      iteratedDeriv 2 (fun t => eighthPotential (fun j => KSRankOne.atom (v j)) θ
        (path (1/8) s.coeff h t)) 0 < 0 := by
  classical
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  have hne : Nonempty (Live (1/8) s.coeff) := by
    by_contra hn
    apply hactive
    apply (KSCubePreparation.vertex_iff_no_live (by norm_num) s.cube).mpr
    intro i hi
    exact hn ⟨⟨i,hi⟩⟩
  letI := hne
  exact exists_negative_second_of_exhaustion v hθ hτ.le _
    (fun x hx => KSEighthNumericalValue.stateReport_accuracy v hθ
      (div_pos hτ (by norm_num)) hd hx) s.cube s.exhausted

end MatrixSpencer.KSEighthPreparedHessian
