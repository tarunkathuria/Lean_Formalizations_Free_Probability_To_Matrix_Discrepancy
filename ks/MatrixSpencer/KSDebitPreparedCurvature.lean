import MatrixSpencer.KSDebitPreparedMargin
import MatrixSpencer.KSDebitLiveHessian

/-!
# Actual negative curvature after numerical full-cube preparation

All original coordinates and their determined debit are used in the function
being differentiated. The debit is locally constant on each open live face.
Failed reported endpoint tests therefore imply negative curvature of this
actual state potential, with no assumed optimizer, transport, no-safe test,
or compact minimum. Value-report accuracy is the remaining oracle premise.
-/

open Matrix Filter Topology Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSDebitPreparedCurvature

open KSDebitPreparation KSDebitPreparedMargin KSPotentialModels KSLiveCurve
variable {N : ℕ} {n : Type*} [Fintype n] [DecidableEq n]

theorem eventually_same_frozen (x : Fin N → ℝ) (h : Live 1 x → ℝ) :
    ∀ᶠ t in 𝓝 (0 : ℝ), ksFrozen 1 (path 1 x h t) = ksFrozen 1 x := by
  filter_upwards [eventually_live x h] with t ht
  ext i
  simp only [ksFrozen, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hi : |x i| < 1
  · exact iff_of_false (ne_of_lt (ht ⟨i, hi⟩)) (ne_of_lt hi)
  · rw [path_dead 1 x h t i hi]

theorem center_path_fixed_debit (A : Fin N → Matrix n n ℂ) (B : Matrix n n ℂ)
    (x : Fin N → ℝ) (h : Live 1 x → ℝ) (t : ℝ) :
    KSDebitCenter.center (KSPotentialModels.center A (path 1 x h t)) B =
      KSDebitCenter.center (KSPotentialModels.center A x) B +
        t • (∑ i, extend 1 x h i • signedLift (A i)) := by
  have hs : signedLift (KSPotentialModels.center A (path 1 x h t)) =
      signedLift (KSPotentialModels.center A x) +
        t • (∑ i, extend 1 x h i • signedLift (A i)) := by
    change signedLift (∑ i, path 1 x h t i • A i) =
      signedLift (∑ i, x i • A i) + _
    rw [signedLift_sum_smul, signedLift_sum_smul]
    simp only [path, add_smul,
      MulAction.mul_smul, Finset.sum_add_distrib, ← Finset.smul_sum]
  unfold KSDebitCenter.center
  rw [hs]
  abel

/-- The state-dependent debit is exactly constant near the base point of
the live line, so both potentials have the same derivatives there. -/
theorem statePotential_path_eventuallyEq (v : Fin N → n → ℂ) (δ η θ : ℝ)
    (x : Fin N → ℝ) (h : Live 1 x → ℝ) :
    (fun t => statePotential v δ η θ (path 1 x h t)) =ᶠ[𝓝 (0 : ℝ)]
      KSDebitLiveHessian.fullCurvePotential (stateCenter v δ η x) v θ x h := by
  filter_upwards [eventually_same_frozen x h] with t ht
  have hb := KSDebitBudget.debit_eq_of_same_frozen
    (fun i => KSRankOne.atom (v i)) δ η ht
  unfold statePotential KSDebitPotential.potential
  rw [hb, center_path_fixed_debit]
  rfl

/-- This is curvature of the actual globally defined state potential at
the output of the numerical preparation, along a nonzero original-label
direction. The conclusion does not refer to an auxiliary compact minimizer. -/
theorem exists_negative_second_after_prepare [Nonempty n]
    (v : Fin N → n → ℂ) {δ η θ : ℝ} (hδ : 0 ≤ δ) (hη : 0 ≤ η) (hθ : 0 < θ)
    (report : (Fin N → ℝ) → ℝ)
    (haccuracy : ∀ x ∈ ksCube 1, |report x - statePotential v δ η θ x| ≤ η / 8)
    {x : Fin N → ℝ} (hx : x ∈ ksCube 1)
    [Nonempty (Live 1 (prepare η report x))] :
    let y := prepare η report x
    ∃ h : Live 1 y → ℝ, h ≠ 0 ∧ extend 1 y h ≠ 0 ∧
      deriv (fun t => statePotential v δ η θ (path 1 y h t)) 0 = 0 ∧
      iteratedDeriv 2 (fun t => statePotential v δ η θ (path 1 y h t)) 0 < 0 := by
  let y := prepare η report x
  have hy := prepare_mem_cube η report hx
  have hH := KSPotentialModels.center_isHermitian
    (fun i => KSRankOne.atom (v i)) (fun i => KSRankOne.atom_isHermitian (v i)) y
  have hB := KSDebitBudget.debit_posSemidef
    (fun i => KSRankOne.atom (v i)) (fun i => KSRankOne.atom_posSemidef (v i)) hδ hη y
  obtain ⟨h, hh, hext, hd, hdd⟩ :=
    KSDebitLiveHessian.exists_negative_second_of_debit_rejection _ _ hH hB v hy hθ hδ
      (fun i => prepared_exact_rejection v δ hη hθ report haccuracy hx i i.property)
  refine ⟨h, hh, hext, ?_, ?_⟩
  · exact (statePotential_path_eventuallyEq v δ η θ y h).deriv_eq.trans hd
  · rw [(statePotential_path_eventuallyEq v δ η θ y h).iteratedDeriv_eq 2]
    exact hdd

end MatrixSpencer.KSDebitPreparedCurvature
