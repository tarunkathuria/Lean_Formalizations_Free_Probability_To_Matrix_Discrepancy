import MatrixSpencer.KSEighthConvexValue
import MatrixSpencer.KSEighthManuscriptControllerDrift


open Matrix Set Module
open scoped BigOperators MatrixOrder ContDiff Topology
noncomputable section
namespace MatrixSpencer.KSEighthConvexController
open KSEighthLiveEnumeration KSEighthHessianQueries KSEighthFacePotential
open KSEighthManuscriptParameters KSEighthManuscriptRun KSEighthManuscriptMovement
open KSEighthManuscriptControllerDrift
variable {N d : ℕ}
set_option maxHeartbeats 1600000

def hessianReport (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ)
    (θ η : ℝ) (hd : 0<d) (x : Fin N → ℝ) : Matrix (Fin (count x)) (Fin (count x)) ℝ :=
  (1/2:ℝ) • KSMatrixEntryAccuracy.symmetrize
    (KSNumericalHessian.matrixReport (KSEighthConvexValue.faceReport O v θ η hd x) 0 (queryMesh v θ η x))

theorem report_isSymm (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ)
    (θ η : ℝ) (hd : 0<d) (x : Fin N → ℝ) : (hessianReport O v θ η hd x).IsSymm := by
  unfold hessianReport
  change ((1/2:ℝ) • _)ᵀ=_
  rw [Matrix.transpose_smul,(KSMatrixEntryAccuracy.symmetrize_isSymm _).eq]

theorem report_entry_accuracy (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ)
    {θ η : ℝ} (hθ : 0<θ) (hη : 0<η) (hd : 0<d)
    {x : Fin N → ℝ} (hx : x∈ksCube (1/8)) (hk : 0<count x) :
    ∀i j,|KSEighthManuscriptPreparedInertia.hessian v θ x i j-hessianReport O v θ η hd x i j|≤η/count x := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  have hf : ContDiffAt ℝ 2 (potential v θ x) 0 :=
    (contDiffAt_potential v hθ x).of_le (WithTop.coe_le_coe.mpr (show (2:ℕ∞)≤⊤ from le_top))
  have he := KSNumericalHessian.selected_entry_error (potential v θ x)
    (KSEighthConvexValue.faceReport O v θ η hd x) 0 hk (by norm_num : (0:ℝ)<1/32)
    (KSEighthInputTaylorBound.fourthBudget_pos v hθ).le hη hf
    (line_bounds v hθ hd hx) (KSEighthConvexValue.query_accuracy O v hθ hη hd hx hk)
  have hs := KSMatrixEntryAccuracy.symmetrize_entry_error (KSNumericalHessian.hessian_isSymm _ _ hf) he
  intro i j
  have hij := hs i j
  change |(1/2:ℝ)*_-(1/2:ℝ)*_|≤_
  rw [←mul_sub,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤1/2)]
  have hnon : 0≤η/(count x:ℝ) := div_nonneg hη.le (Nat.cast_nonneg _)
  dsimp only [queryMesh]
  nlinarith

theorem report_frobenius_accuracy (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ)
    {θ η : ℝ} (hθ : 0<θ) (hη : 0<η) (hd : 0<d)
    {x : Fin N → ℝ} (hx : x∈ksCube (1/8)) (hk : 0<count x) :
    KSJacobiStep.frobeniusEnergy
      (KSEighthManuscriptPreparedInertia.hessian v θ x-hessianReport O v θ η hd x)≤η^2 := by
  have he := report_entry_accuracy O v hθ hη hd hx hk
  have hk' : (count x:ℝ)≠0 := by exact_mod_cast hk.ne'
  calc _ ≤ ∑_i : Fin (count x),∑_j : Fin (count x),(η/(count x:ℝ))^2 := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        have h := he i j
        change (KSEighthManuscriptPreparedInertia.hessian v θ x i j-hessianReport O v θ η hd x i j)^2≤_
        nlinarith [sq_abs (KSEighthManuscriptPreparedInertia.hessian v θ x i j-hessianReport O v θ η hd x i j),
          abs_nonneg (KSEighthManuscriptPreparedInertia.hessian v θ x i j-hessianReport O v θ η hd x i j),
          div_nonneg hη.le (Nat.cast_nonneg (α := ℝ) (count x))]
    _ = η^2 := by simp; field_simp

def covariance (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ)
    (θ η κ β : ℝ) (hd : 0<d) (x : Fin N → ℝ) :=
  KSEighthManuscriptCovariance.covariance (hessianReport O v θ η hd x) κ β

theorem covariance_spec (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ)
    {ρ τ θ η κ β : ℝ} (hτ : 0<τ) (hθ : 0<θ) (hη : 0<η) (hηκ : η≤κ)
    (hβ : 0<β) (hβsmall : β≤1/4) (hd : 0<d)
    (s : KSEighthWalkRun.PreparedState N ρ τ (KSEighthConvexValue.stateReport O v θ hd (τ/8)))
    (hs : ¬KSEighthWalkRun.terminal s) :
    (covariance O v θ η κ β hd s.coeff).PosSemidef ∧ covariance O v θ η κ β hd s.coeff≤1 ∧
      (3/4:ℝ)*count s.coeff≤Matrix.trace (covariance O v θ η κ β hd s.coeff) ∧
      Matrix.trace (covariance O v θ η κ β hd s.coeff*
        KSEighthManuscriptPreparedInertia.hessian v θ s.coeff)≤3*κ*count s.coeff := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  have hk := count_pos_of_not_vertex s.cube hs
  letI : Nonempty (KSLiveCurve.Live (1/8) s.coeff) := ⟨liveEquiv s.coeff ⟨0,hk⟩⟩
  obtain ⟨W,hdim,hW⟩ := KSEighthManuscriptPreparedInertia.exists_large_negative_hessian_of_exhaustion
    v hθ hτ.le _ (fun x hx => KSEighthConvexValue.stateReport_accuracy O v hθ
      (div_pos hτ (by norm_num)) hd hx) s.cube s.exhausted
  exact KSEighthManuscriptCovariance.covariance_spec _ _ (report_isSymm O v θ η hd s.coeff)
    (hη.trans_le hηκ) hβ hβsmall hk
    ((report_frobenius_accuracy O v hθ hη hd s.cube hk).trans (by nlinarith)) W hdim hW

def controller (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ) {δ θ : ℝ}
    (hN : 0<N) (hδ : 0<δ) (hθ : 0<θ) (hd : 0<d) : Controller N where
  ρ := rho N δ
  ρ_pos := rho_pos hN hδ
  τ := rho N δ
  report := KSEighthConvexValue.stateReport O v θ hd (rho N δ/8)
  stepSize := movementStep v δ θ
  step_pos := movementStep_pos v hN hδ hθ hd
  step_le := movementStep_margin v hN hδ hθ hd
  covariance := fun s => covariance O v θ (precision N δ) (kappa N δ) (beta v δ θ) hd s.coeff
  covariance_posSemidef := fun s => KSEighthManuscriptCovariance.covariance_posSemidef _ _ _
  covariance_le_one := fun s => (KSEighthManuscriptCovariance.covariance_feasible _ _ _).2.2.1
  covariance_trace := fun s _ => by
    unfold covariance
    rw [(KSEighthManuscriptCovariance.covariance_feasible _ _ _).2.2.2]
    unfold KSEighthManuscriptCovariance.target
    nlinarith [show (0:ℝ)≤count s.coeff from Nat.cast_nonneg _]

theorem controller_covariance_curvature (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ)
    {δ θ : ℝ} (hN : 0<N) (hδ : 0<δ) (hδ1 : δ≤1) (hθ : 0<θ) (hd : 0<d)
    (s : State (controller O v hN hδ hθ hd)) (hs : ¬KSEighthWalkRun.terminal s) :
    Matrix.trace ((controller O v hN hδ hθ hd).covariance s*
      KSEighthManuscriptPreparedInertia.hessian v θ s.coeff)≤3*kappa N δ*count s.coeff :=
  (covariance_spec O v (rho_pos hN hδ) hθ (precision_pos hN hδ) (precision_le hN hδ)
    (beta_pos v hN hδ hθ hd) (beta_le_quarter v hN hδ hδ1 hθ hd) hd s hs).2.2.2

theorem controller_average_le (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ)
    {δ θ : ℝ} (hN : 0<N) (hδ : 0<δ) (hδ1 : δ≤1) (hθ : 0<θ) (hd : 0<d)
    (s : State (controller O v hN hδ hθ hd)) (hs : ¬KSEighthWalkRun.terminal s) :
    (∑z,KSEighthManuscriptSampler.weight z*KSPotentialModels.eighthPotential
      (fun i => KSRankOne.atom (v i)) θ
        (proposal s.coeff ((controller O v hN hδ hθ hd).covariance s) (movementStep v δ θ) z))≤
      KSPotentialModels.eighthPotential (fun i => KSRankOne.atom (v i)) θ s.coeff+driftPerStep v δ θ := by
  let C := controller O v hN hδ hθ hd
  have h := KSEighthManuscriptDrift.proposal_average_le v hθ hd s.cube
    (count_pos_of_not_vertex s.cube hs) (C.covariance_posSemidef s) (C.covariance_le_one s)
    (movementStep_pos v hN hδ hθ hd) (movementStep_margin v hN hδ hθ hd)
    (KSEighthManuscriptBudgets.movement_normalized_radius v hN hδ1) s.margin
    (controller_covariance_curvature O v hN hδ hδ1 hθ hd s hs)
  apply h.trans
  have hκ := kappa_pos hN hδ
  have hkN : (count s.coeff:ℝ)≤N := by exact_mod_cast count_le s.coeff
  have hfirst := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hkN (show 0≤3*kappa N δ by positivity)) (sq_nonneg (movementStep v δ θ))
  have hM : KSEighthInputTaylorBound.fourthBudget v θ≤fourthCap v θ := by unfold fourthCap; linarith
  have hsecond := mul_le_mul_of_nonneg_right hM (show 0≤(N:ℝ)^2*movementStep v δ θ^4/24 by positivity)
  unfold driftPerStep
  nlinarith

theorem cutoff_probability (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ)
    {δ θ : ℝ} (hN : 0<N) (hδ : 0<δ) (hθ : 0<θ) (hd : 0<d)
    (s : State (controller O v hN hδ hθ hd)) :
    cutoffProbability (controller O v hN hδ hθ hd) (KSEighthManuscriptBudgets.cutoff v δ θ) s≤1/100 := by
  have ht := KSEighthManuscriptBudgets.cutoff_pos v hN hδ hθ hd
  have hh := KSEighthManuscriptBudgets.cutoff_lower v hN hδ hθ hd
  have hs := movementStep_pos v hN hδ hθ hd
  have htr : (0:ℝ)<KSEighthManuscriptBudgets.cutoff v δ θ := Nat.cast_pos.mpr ht
  apply (cutoffProbability_le _ _ ht s).trans
  change ((N:ℝ)/64)/(movementStep v δ θ^2/2*(KSEighthManuscriptBudgets.cutoff v δ θ:ℝ))≤_
  rw [div_le_iff₀ (by positivity : 0<movementStep v δ θ^2/2*(KSEighthManuscriptBudgets.cutoff v δ θ:ℝ))]
  nlinarith [Nat.cast_nonneg (α := ℝ) N]

end MatrixSpencer.KSEighthConvexController
