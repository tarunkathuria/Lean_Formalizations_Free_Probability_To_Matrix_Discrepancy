import MatrixSpencer.KSEighthNumericalController
import MatrixSpencer.KSInitialBounds

/-!
# Actual eighth-walk expected discrepancy

The finite numerical controller has no supplied drift or accuracy premise.
The accounting potential charges preparation once per newly frozen label.
Squared-norm progress bounds the expected number of actual movements; its
step-size factor cancels the proved quadratic Taylor drift.
-/

open Set Matrix
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSEighthWalkQuality
open KSEighthWalkRun KSEighthNumericalController KSEighthPreparationCost
variable {N d : ℕ}

/-- Proof-only accounting for the remaining original labels. -/
def accounting (v : Fin N → Fin d → ℂ) (ρ τ θ : ℝ) (x : Fin N → ℝ) : ℝ :=
  KSPotentialModels.eighthPotential (fun i => KSRankOne.atom (v i)) θ x +
    charge v ρ τ * ((N : ℝ)-frozenCount (1/8) x)

theorem charge_nonneg (v : Fin N → Fin d → ℂ) {ρ τ : ℝ} (hρ : 0 ≤ ρ) (hτ : 0 ≤ τ) :
    0 ≤ charge v ρ τ := add_nonneg (mul_nonneg hρ (atomCap_pos v).le) hτ

theorem prepare_accounting_le (v : Fin N → Fin d → ℂ) {ρ τ θ : ℝ}
    (hρ : 0 < ρ) (hτ : 0 < τ) (hθ : 0 < θ) (hd : 0 < d)
    {x : Fin N → ℝ} (hx : x ∈ ksCube (1/8)) :
    accounting v ρ τ θ (KSEighthPreparedState.prepareState (1/8) τ ρ
      (KSEighthNumericalValue.stateReport v θ hd (τ/8)) x) ≤ accounting v ρ τ θ x := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  have h := prepareState_potential_cost v θ hρ.le hτ.le _
    (fun z hz => KSEighthNumericalValue.stateReport_accuracy v hθ (div_pos hτ (by norm_num)) hd hz) hx
  unfold accounting
  linarith

theorem norm_le_accounting (v : Fin N → Fin d → ℂ) {ρ τ θ : ℝ}
    (hρ : 0 ≤ ρ) (hτ : 0 ≤ τ) (hθ : 0 ≤ θ) (hd : 0 < d)
    {x : Fin N → ℝ} (hx : x ∈ ksCube (1/8)) :
    ‖KSPotentialModels.center (fun i => KSRankOne.atom (v i)) x‖ ≤ accounting v ρ τ θ x := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  have hn := KSFinalAssembly.norm_le_eighthPotential (fun i => KSRankOne.atom (v i))
    (fun i => KSRankOne.atom_isHermitian (v i)) hθ hx
  have hc : frozenCount (1/8) x ≤ (N : ℝ) := by
    dsimp only [frozenCount]
    exact_mod_cast ksFrozen_card_le (1/8) x
  exact hn.trans (le_add_of_nonneg_right (mul_nonneg (charge_nonneg v hρ hτ) (sub_nonneg.mpr hc)))

theorem proposal_frozen_eq (v : Fin N → Fin d → ℂ) {ρ τ θ κ : ℝ}
    (hρ : 0 < ρ) (_hθ : 0 < θ) (_hκ : 0 < κ) (hd : 0 < d)
    (s : ReportState v ρ τ θ hd) (hs : ¬terminal s) {t : ℝ}
    (ht : |t| ≤ movementStep v ρ θ κ) :
    ksFrozen (1/8) (proposal s.coeff (numericalDirection v ρ τ θ κ hd s) t) = ksFrozen (1/8) s.coeff := by
  ext i
  simp only [ksFrozen, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hi : |s.coeff i| = (1/8 : ℝ)
  · rw [proposal_preserves_frozen _ _ _ i (numericalDirection_frozen v ρ τ θ κ hd s hs i hi)]
  · have hl : |s.coeff i| < (1/8 : ℝ) := lt_of_le_of_ne (abs_le.mpr ⟨s.cube.1 i,s.cube.2 i⟩) hi
    have hm := s.margin i hl
    have hdisp := proposal_displacement_le s.coeff _ (numericalDirection_norm v ρ τ θ κ hd s hs) t i
    have habs := abs_sub_abs_le_abs_sub (proposal s.coeff (numericalDirection v ρ τ θ κ hd s) t i) (s.coeff i)
    have hnew : |proposal s.coeff (numericalDirection v ρ τ θ κ hd s) t i| < (1/8 : ℝ) := by
      have hh := movementStep_le_half v ρ θ κ
      linarith
    exact iff_of_false (ne_of_lt hnew) hi

theorem step_accounting_le (v : Fin N → Fin d → ℂ) {ρ τ θ κ : ℝ}
    (hρ : 0 < ρ) (hτ : 0 < τ) (hθ : 0 < θ) (hκ : 0 < κ) (hd : 0 < d)
    (s : State (controller v hρ hθ hκ hd (τ := τ))) (hs : ¬terminal s) :
    let C := controller v hρ hθ hκ hd (τ := τ)
    (accounting v ρ τ θ (step C s false).coeff + accounting v ρ τ θ (step C s true).coeff)/2 ≤
      accounting v ρ τ θ s.coeff + 2*κ*C.stepSize^2 := by
  let C := controller v hρ hθ hκ hd (τ := τ)
  have hp (b : Bool) := prepare_accounting_le v hρ hτ hθ hd
    (proposal_mem_cube s.coeff s.cube (C.direction s) (C.direction_norm s hs)
      (C.direction_frozen s hs) (signedStep_abs_le C b) s.margin)
  have he (b : Bool) : frozenCount (1/8) (proposal s.coeff (C.direction s) (signedStep C b)) =
      frozenCount (1/8) s.coeff := by
    apply congrArg (fun D : Finset (Fin N) => (D.card : ℝ))
    apply proposal_frozen_eq v hρ hθ hκ hd s hs
    cases b <;> simp [signedStep, C, controller, abs_of_pos (movementStep_pos v hρ hθ hκ hd)]
  have hf := hp false
  have ht := hp true
  unfold accounting at hf ht ⊢
  rw [he false] at hf
  rw [he true] at ht
  have ha := proposal_average_le v hρ hτ hθ hκ hd s hs
  dsimp only at ha ⊢
  rw [step_active_coeff _ _ hs false, step_active_coeff _ _ hs true]
  change _ ≤ _ + 2*κ*C.stepSize^2
  change _ ≤ _ at ha
  simp only [signedStep, Bool.false_eq_true, ↓reduceIte] at hf ht
  dsimp only [C, controller] at hf ht ⊢
  simp only [signedStep, Bool.false_eq_true, ↓reduceIte]
  linarith

theorem expected_accounting_le (v : Fin N → Fin d → ℂ) {ρ τ θ κ : ℝ}
    (hρ : 0 < ρ) (hτ : 0 < τ) (hθ : 0 < θ) (hκ : 0 < κ) (hd : 0 < d)
    (T : ℕ) (s : State (controller v hρ hθ hκ hd (τ := τ))) :
    let C := controller v hρ hθ hκ hd (τ := τ)
    (run C T s).expectation (fun q => accounting v ρ τ θ q.coeff) ≤
      accounting v ρ τ θ s.coeff + κ*(N : ℝ)/16 := by
  let C := controller v hρ hθ hκ hd (τ := τ)
  let F := fun q : State C => accounting v ρ τ θ q.coeff
  have ht := KSFiniteCoinRun.progress_telescope terminal (step C) (fun q => -F q)
    (-(2*κ*C.stepSize^2)) (fun q hq => by
      have := step_accounting_le v hρ hτ hθ hκ hd q hq
      dsimp only at this
      dsimp only [F]
      linarith) T s
  change -F s + (-(2*κ*C.stepSize^2))*expectedMovements C T s ≤
    (run C T s).expectation (fun q => -F q) at ht
  rw [FiniteBranchingTermination.Tree.expectation_neg] at ht
  have hm := mul_le_mul_of_nonneg_left (expectedMovements_le C T s)
    (by positivity : 0 ≤ 2*κ*C.stepSize^2)
  have he : 2*κ*C.stepSize^2*(((N : ℝ)/64)/(C.stepSize^2/2)) = κ*(N : ℝ)/16 := by
    field_simp [ne_of_gt C.step_pos]
    ring
  rw [he] at hm
  dsimp only
  linarith

theorem expected_norm_le (v : Fin N → Fin d → ℂ) {ρ τ θ κ : ℝ}
    (hρ : 0 < ρ) (hτ : 0 < τ) (hθ : 0 < θ) (hκ : 0 < κ) (hd : 0 < d)
    (T : ℕ) :
    let C := controller v hρ hθ hκ hd (τ := τ)
    (run C T (initialState C)).expectation
      (fun q => ‖KSPotentialModels.center (fun i => KSRankOne.atom (v i)) q.coeff‖) ≤
      KSPotentialModels.eighthPotential (fun i => KSRankOne.atom (v i)) θ 0 +
        charge v ρ τ * N + κ*N/16 := by
  let C := controller v hρ hθ hκ hd (τ := τ)
  have hpoint : (run C T (initialState C)).expectation
      (fun q => ‖KSPotentialModels.center (fun i => KSRankOne.atom (v i)) q.coeff‖) ≤
      (run C T (initialState C)).expectation (fun q => accounting v ρ τ θ q.coeff) := by
    unfold FiniteBranchingTermination.Tree.expectation
    exact Finset.sum_le_sum (fun l _ => mul_le_mul_of_nonneg_left
      (norm_le_accounting v hρ.le hτ.le hθ.le hd ((run C T (initialState C)).leafState l).cube)
      ((run C T (initialState C)).leafWeight_pos l).le)
  have hexp := expected_accounting_le v hρ hτ hθ hκ hd T (initialState C)
  have hi : accounting v ρ τ θ (initialState C).coeff ≤ accounting v ρ τ θ 0 :=
    prepare_accounting_le v hρ hτ hθ hd (ksCube_zero (by norm_num))
  have hz : accounting v ρ τ θ 0 ≤ KSPotentialModels.eighthPotential (fun i => KSRankOne.atom (v i)) θ 0 + charge v ρ τ*N := by
    unfold accounting
    have hc : 0 ≤ frozenCount (1/8) (0 : Fin N → ℝ) := Nat.cast_nonneg _
    nlinarith [mul_nonneg (charge_nonneg v hρ.le hτ.le) hc]
  exact hpoint.trans (hexp.trans (add_le_add_right (hi.trans hz) _))

end MatrixSpencer.KSEighthWalkQuality
