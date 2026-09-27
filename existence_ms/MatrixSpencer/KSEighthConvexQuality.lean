import MatrixSpencer.KSEighthConvexController
import MatrixSpencer.KSEighthManuscriptQuality


open Matrix Set
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSEighthConvexQuality
open KSEighthManuscriptParameters KSEighthManuscriptRun KSEighthPreparationCost
open KSEighthLiveEnumeration KSEighthManuscriptControllerDrift KSEighthManuscriptQuality
variable {N d : ℕ}
set_option maxHeartbeats 1600000

theorem prepare_accounting_le (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ)
    (hbound : ∀i, ‖signedLift (KSRankOne.atom (v i))‖ ≤ 1) {δ θ : ℝ}
    (hN : 0 < N) (hδ : 0 < δ) (hθ : 0 < θ) (hd : 0 < d)
    {x : Fin N → ℝ} (hx : x ∈ ksCube (1/8)) :
    accounting v δ θ (KSEighthPreparedState.prepareState (1/8) (rho N δ) (rho N δ)
      (KSEighthConvexValue.stateReport O v θ hd (rho N δ/8)) x) ≤ accounting v δ θ x := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  have hρ := rho_pos hN hδ
  have h := KSEighthManuscriptPreparationCost.prepareState_potential_cost v hbound θ hρ.le hρ.le _
    (fun y hy => KSEighthConvexValue.stateReport_accuracy O v hθ (div_pos hρ (by norm_num)) hd hy) hx
  unfold accounting
  linarith

theorem proposal_frozen_eq (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ) {δ θ : ℝ}
    (hN : 0 < N) (hδ : 0 < δ) (hθ : 0 < θ) (hd : 0 < d)
    (s : State (KSEighthConvexController.controller O v hN hδ hθ hd)) (z : Fin (count s.coeff) × Bool) :
    ksFrozen (1/8) (KSEighthManuscriptMovement.proposal s.coeff
      ((KSEighthConvexController.controller O v hN hδ hθ hd).covariance s) (movementStep v δ θ) z) = ksFrozen (1/8) s.coeff := by
  let C := KSEighthConvexController.controller O v hN hδ hθ hd
  have hp := KSEighthManuscriptMovement.proposal_mem_cube (h := C.stepSize) s.cube (C.covariance_posSemidef s)
    (C.covariance_le_one s) (by simpa only [abs_of_pos C.step_pos] using C.step_le) s.margin z
  have hl := KSEighthManuscriptDriftGeometry.proposal_live_iff (h := C.stepSize) s.cube (C.covariance_posSemidef s)
    (C.covariance_le_one s) (by simpa only [abs_of_pos C.step_pos] using C.step_le) s.margin z
  ext i
  simp only [ksFrozen,Finset.mem_filter,Finset.mem_univ,true_and]
  have hxi : |s.coeff i| ≤ (1/8 : ℝ) := abs_le.mpr ⟨s.cube.1 i,s.cube.2 i⟩
  have hpi := abs_le.mpr ⟨hp.1 i,hp.2 i⟩
  constructor
  · intro he
    by_contra hn
    have hh := (hl i).mpr (lt_of_le_of_ne hxi hn)
    change |KSEighthManuscriptMovement.proposal s.coeff (C.covariance s) C.stepSize z i| = (1/8 : ℝ) at he
    rw [he] at hh
    exact (lt_irrefl _) hh
  · intro he
    exact congrArg abs (KSEighthManuscriptMovement.proposal_frozen _ _ _ z i he) |>.trans he

theorem step_accounting_le (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ)
    (hbound : ∀i, ‖signedLift (KSRankOne.atom (v i))‖ ≤ 1) {δ θ : ℝ}
    (hN : 0 < N) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hθ : 0 < θ) (hd : 0 < d)
    (s : State (KSEighthConvexController.controller O v hN hδ hθ hd)) (hs : ¬KSEighthWalkRun.terminal s) :
    let C := KSEighthConvexController.controller O v hN hδ hθ hd
    (∑i, (step C s).weight i * accounting v δ θ ((step C s).child i).coeff) ≤
      accounting v δ θ s.coeff + driftPerStep v δ θ := by
  let C := KSEighthConvexController.controller O v hN hδ hθ hd
  dsimp only
  change (∑i, (step C s).weight i * (fun q : State C => accounting v δ θ q.coeff) ((step C s).child i)) ≤ _
  rw [step_active_expectation C s hs (fun q => accounting v δ θ q.coeff)]
  have hc (z : Fin (count s.coeff) × Bool) := prepare_accounting_le O v hbound hN hδ hθ hd
    (KSEighthManuscriptMovement.proposal_mem_cube (h := C.stepSize) s.cube (C.covariance_posSemidef s)
      (C.covariance_le_one s) (by simpa only [abs_of_pos C.step_pos] using C.step_le) s.margin z)
  have hsum := Finset.sum_le_sum (fun z (_ : z ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (hc z) (KSEighthManuscriptSampler.weight_pos (count_pos_of_not_vertex s.cube hs) z).le)
  change (∑z, KSEighthManuscriptSampler.weight z*accounting v δ θ (child C s z).coeff) ≤ _ at hsum
  apply hsum.trans
  have hcount (z) : frozenCount (1/8) (KSEighthManuscriptMovement.proposal s.coeff (C.covariance s) C.stepSize z) =
      frozenCount (1/8) s.coeff := congrArg (fun S : Finset (Fin N) => (S.card : ℝ))
        (proposal_frozen_eq O v hN hδ hθ hd s z)
  simp only [accounting,hcount,mul_add,Finset.sum_add_distrib,← Finset.sum_mul,
    KSEighthManuscriptSampler.weight_sum (count_pos_of_not_vertex s.cube hs),one_mul]
  have hm := KSEighthConvexController.controller_average_le O v hN hδ hδ1 hθ hd s hs
  change (∑z, KSEighthManuscriptSampler.weight z * KSPotentialModels.eighthPotential
    (fun i => KSRankOne.atom (v i)) θ (KSEighthManuscriptMovement.proposal s.coeff (C.covariance s) C.stepSize z)) ≤ _ at hm
  linarith

theorem expected_potential_le (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ)
    (hbound : ∀i, ‖signedLift (KSRankOne.atom (v i))‖ ≤ 1) {δ θ : ℝ}
    (hN : 0 < N) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hθ : 0 < θ) (hd : 0 < d) (T : ℕ) :
    let C := KSEighthConvexController.controller O v hN hδ hθ hd
    (run C T (initialState C)).expectation
      (fun q => KSPotentialModels.eighthPotential (fun i => KSRankOne.atom (v i)) θ q.coeff) ≤
      KSPotentialModels.eighthPotential (fun i => KSRankOne.atom (v i)) θ 0 + δ/50 + δ/1000 := by
  let C := KSEighthConvexController.controller O v hN hδ hθ hd
  have hstep := step_accounting_le O v hbound hN hδ hδ1 hθ hd
  have ht := KSEighthManuscriptBranchingRun.drift_telescope KSEighthWalkRun.terminal (step C)
    (fun q => accounting v δ θ q.coeff) (driftPerStep v δ θ) hstep T (initialState C)
  have hm := mul_le_mul_of_nonneg_left (expectedMovements_le C T (initialState C))
    (driftPerStep_nonneg v hN hδ hθ hd)
  have hbudget := movement_total_budget v hN hδ hθ hd
  have hi : accounting v δ θ (initialState C).coeff ≤ accounting v δ θ 0 :=
    prepare_accounting_le O v hbound hN hδ hθ hd (ksCube_zero (by norm_num))
  have hinit : accounting v δ θ 0 ≤ KSPotentialModels.eighthPotential (fun i => KSRankOne.atom (v i)) θ 0 + δ/50 := by
    have hc : 0 ≤ frozenCount (1/8) (0 : Fin N → ℝ) := Nat.cast_nonneg _
    have hρ := rho_pos hN hδ
    have hr := KSEighthManuscriptBudgets.rho_count hN δ
    unfold accounting
    nlinarith
  have hp := KSEighthManuscriptBranchingRun.expectation_mono KSEighthWalkRun.terminal (step C) T
    (initialState C) _ (fun q => accounting v δ θ q.coeff)
    (fun q => potential_le_accounting v hN hδ θ q.coeff)
  change (run C T (initialState C)).expectation _ ≤ _ at hp
  dsimp only
  change _ ≤ _ + driftPerStep v δ θ*expectedMovements C T (initialState C) at ht
  change driftPerStep v δ θ*expectedMovements C T (initialState C) ≤
    driftPerStep v δ θ*((N:ℝ)/64/(movementStep v δ θ^2/2)) at hm
  change _ ≤ _ + _ + _
  exact hp.trans (ht.trans (by linarith))

/-- Primitive input theorem for the true stopped potential, including all
nonterminal cutoff leaves. It is this nonnegative quantity that Markov uses. -/
theorem expected_potential_le_nineteen (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ) {ε : ℝ}
    (hN : 0 < N) (hε : 0 < ε) (hε1 : ε ≤ 1) (hd : 0 < d)
    (hparseval : (∑i, KSRankOne.atom (v i)) = 1)
    (hsize : ∀i, ‖KSRankOne.atom (v i)‖ ≤ ε) (T : ℕ) :
    let hδ := Real.sqrt_pos.mpr hε
    let hθ := @ksRegularizerScale_pos (Fin d) _ _ ⟨⟨0,hd⟩⟩ ε hε
    let C := KSEighthConvexController.controller O v hN hδ hθ hd
    (run C T (initialState C)).expectation (fun q => KSPotentialModels.eighthPotential
      (fun i => KSRankOne.atom (v i)) (ksRegularizerScale ε (Fin d)) q.coeff) ≤ 19*Real.sqrt ε := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  have hδ := Real.sqrt_pos.mpr hε
  have hδ1 : Real.sqrt ε ≤ 1 := Real.sqrt_le_one.mpr hε1
  have hθ : 0 < ksRegularizerScale ε (Fin d) := ksRegularizerScale_pos hε
  have hbound : ∀i, ‖signedLift (KSRankOne.atom (v i))‖ ≤ 1 := by
    intro i
    rw [signedLift_norm (KSRankOne.atom_isHermitian (v i))]
    exact (hsize i).trans hε1
  have he := expected_potential_le O v hbound hN hδ hδ1 hθ hd T
  have hi := KSFinalAssembly.eighth_initial_bound v hparseval hε hsize
  dsimp only
  exact he.trans (by linarith)

end MatrixSpencer.KSEighthConvexQuality
