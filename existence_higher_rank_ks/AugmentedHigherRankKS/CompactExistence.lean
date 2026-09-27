import AugmentedHigherRankKS.EpochMinimum
import AugmentedHigherRankKS.EpochMovement
import AugmentedHigherRankKS.FourBlockLocalCurvature
import AugmentedHigherRankKS.Parameters

/-! The compact epoch theorem. Its local analytic obligations are discharged
by the actual optimized potential, not retained as theorem hypotheses. -/
open Matrix MatrixSpencer HigherRankKS.BalancedFrames Set
open scoped BigOperators Topology ContDiff MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace AugmentedHigherRankKS
variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n] [Nonempty n]

theorem exists_regularized_exhausted_epoch
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (k : ℕ) (hk : 1 ≤ k) (θ : ℝ) (hθ : 0 < θ)
    (x₀ : ι → ℝ) (hx₀ : ∀ i, -1 ≤ x₀ i ∧ x₀ i ≤ 1) :
    ∃ z ∈ epochDomain (reserveScale ((1 : ℝ) / 2 ^ k)) 4,
      (∀ i, reserve z i = 0) ∧
      epochPotential A ((1 : ℝ) / 2 ^ k) θ x₀ z ≤
        epochPotential A ((1 : ℝ) / 2 ^ k) θ x₀
          (initialState (reserveScale ((1 : ℝ) / 2 ^ k)) 4 x₀) := by
  let β : ℝ := 1 / 2 ^ k
  let a := reserveScale β
  have hβ : 0 < β := by dsimp [β]; positivity
  have hβ2 : β ≤ 1 / 2 := by
    apply one_div_le_one_div_of_le (by norm_num)
    exact le_self_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
  have hβ1 : β < 1 := lt_of_le_of_lt hβ2 (by norm_num)
  have ha : 0 < a := reserveScale_pos hβ
  obtain ⟨z, hz, hmin, hface, hzero, hval⟩ := exists_epoch_minimizer A hβ.le hβ1.le θ
    x₀ hx₀ ha (by norm_num : (0 : ℝ) ≤ 4)
  refine ⟨z, hz, ?_, hval⟩
  intro j
  by_contra hcj
  have hposj : 0 < reserve z j := lt_of_le_of_ne (hz j).2.2.2.2.1 (Ne.symm hcj)
  letI : Nonempty (ActiveOwners z) := ⟨⟨j, (mem_positiveReserves z j).mpr hposj⟩⟩
  let B : ActiveOwners z → Matrix n n ℂ := fun i => A i
  let c : ActiveOwners z → ℝ := fun i => reserve z i
  let x : ActiveOwners z → ℝ := fun i => position z i
  let H := augmentedCenter (discrepancy A x₀ z) (budgetCenter A x₀ z)
  have hc : ∀ i, 0 < c i := fun i => (mem_positiveReserves z i).mp i.property
  have hB : ∀ i, (B i).PosSemidef := fun i => hA i
  have hne : ∀ i, B i ≠ 0 := by
    intro i hi
    exact (ne_of_gt (hc i)) (hzero i hi)
  have hx : ∀ i, |x i| ≤ 1 := fun i => abs_le.mpr ⟨(hz i).1, (hz i).2.1⟩
  obtain ⟨M, hM, hmax⟩ := exists_optimizer H B hβ.le hβ1.le (fun i => (hc i).le) θ
  let S : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ) := ⟨M, hM.1.isHermitian⟩
  have hS : (S : Matrix (FourSpin n) (FourSpin n) ℂ).PosDef :=
    maximizer_posDef H B hβ hβ1 (fun i => (hc i).le) hθ hM hmax
  have hcap0 := epoch_minimizer_preparation_cap A hA k hk θ hθ x₀ ha hz hmin
    hzero S hM hmax
  have hcap : ∀ i, Frames.r B β c S i ^ 2 ≤ 1 / 48 := by
    intro i
    have hi := (hcap0 i).trans (reserveScale_cap hβ hβ2)
    simpa only [Frames.r, probeScale, div_pow, mul_pow, Real.sq_sqrt (hc i).le,
      mul_div_assoc] using hi
  obtain ⟨h, hh, _horth, hnegative⟩ := Frames.exists_negative_curvature B hB hne k hk c hc
    x (fun _ => 0) hx H θ hθ S hS hM.2 hmax hcap (reserveScale_dominates_response hβ)
  have hd := Frames.debit_pos B hB hne k hk c hc hS hh
  have hn : 0 ≤ iteratedDeriv 2 (fun t : ℝ => potential
      (H + t • Frames.coefficientForce B x h) B β
      (QuadraticReserveCurve.curve c a h t) θ) 0 := by
    have heq : (fun t : ℝ => epochPotential A β θ x₀
        (movement a z (liftActiveDirection z h) t)) =
        (fun t : ℝ => potential (H + t • Frames.coefficientForce B x h) B β
          (QuadraticReserveCurve.curve c a h t) θ) := by
      funext t
      exact epochPotential_movement_eq A β θ x₀ hz h t
    rw [← heq]
    exact epoch_movement_second_nonneg A hA k hk θ hθ x₀ ha hz hmin hface h
  have hdebit : 0 < a * Frames.debit B β c S h := mul_pos ha hd
  change _ < -a * Frames.debit B β c S h at hnegative
  nlinarith

/-- A complete exact epoch, with the auxiliary positive-root term removed. -/
theorem exists_exhausted_epoch
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    {b : ℝ} (hsum : ∑ i, A i ≤ b • (1 : Matrix n n ℂ))
    {ε : ℝ} (hε : 0 ≤ ε) (hN : ∀ i, ‖A i‖ ≤ ε)
    {r : ℕ} (hr : ∀ i, (A i).rank ≤ r)
    (k : ℕ) (hk : 1 ≤ k) (x₀ : ι → ℝ)
    (hx₀ : ∀ i, -1 ≤ x₀ i ∧ x₀ i ≤ 1) :
    ∃ z ∈ epochDomain (reserveScale ((1 : ℝ) / 2 ^ k)) 4,
      (∀ i, reserve z i = 0) ∧
      epochCenterSize A x₀ z ≤
        2 * Real.sqrt (4 * (reserveScale ((1 : ℝ) / 2 ^ k) * 4) *
          ε * (r : ℝ)^((1 : ℝ) / 2 ^ k) * b) := by
  have hβ : 0 < (1 : ℝ) / 2 ^ k := by positivity
  have hβ1 : (1 : ℝ) / 2 ^ k < 1 := by
    apply (div_lt_one (by positivity)).mpr
    exact one_lt_pow₀ (by norm_num) (by omega)
  apply exhausted_epoch_bound_of_regularized_values A hA hsum hε hN hr hβ hβ1
    (mul_nonneg (reserveScale_pos hβ).le (by norm_num)) x₀
  exact fun θ hθ => exists_regularized_exhausted_epoch A hA k hk θ hθ x₀ hx₀

end AugmentedHigherRankKS
