import MatrixSpencer.KSEighthManuscriptDrift
import MatrixSpencer.KSEighthManuscriptBudgets

/-! The concrete numerical covariance controller satisfies actual potential drift. -/

open Matrix Set
open scoped BigOperators MatrixOrder
noncomputable section
namespace MatrixSpencer.KSEighthManuscriptControllerDrift
open KSEighthManuscriptParameters KSEighthManuscriptRun KSEighthManuscriptMovement
open KSEighthLiveEnumeration
variable {N d : ℕ}

def driftPerStep (v : Fin N → Fin d → ℂ) (δ θ : ℝ) : ℝ :=
  3*kappa N δ*N*movementStep v δ θ^2 +
    fourthCap v θ*(N : ℝ)^2*movementStep v δ θ^4/24

theorem driftPerStep_nonneg (v : Fin N → Fin d → ℂ) {δ θ : ℝ}
    (hN : 0 < N) (hδ : 0 < δ) (hθ : 0 < θ) (hd : 0 < d) : 0 ≤ driftPerStep v δ θ := by
  have hκ := kappa_pos hN hδ
  have hM := fourthCap_pos v hθ hd
  unfold driftPerStep
  positivity


theorem controller_average_le (v : Fin N → Fin d → ℂ) {δ θ : ℝ}
    (hN : 0 < N) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hθ : 0 < θ) (hd : 0 < d)
    (s : State (controller v hN hδ hθ hd)) (hs : ¬KSEighthWalkRun.terminal s) :
    (∑z, KSEighthManuscriptSampler.weight z * KSPotentialModels.eighthPotential
      (fun i => KSRankOne.atom (v i)) θ
        (proposal s.coeff ((controller v hN hδ hθ hd).covariance s) (movementStep v δ θ) z)) ≤
      KSPotentialModels.eighthPotential (fun i => KSRankOne.atom (v i)) θ s.coeff + driftPerStep v δ θ := by
  let C := controller v hN hδ hθ hd
  have h := KSEighthManuscriptDrift.proposal_average_le v hθ hd s.cube
    (count_pos_of_not_vertex s.cube hs) (C.covariance_posSemidef s) (C.covariance_le_one s)
    (movementStep_pos v hN hδ hθ hd) (movementStep_margin v hN hδ hθ hd)
    (KSEighthManuscriptBudgets.movement_normalized_radius v hN hδ1) s.margin
    (controller_covariance_curvature v hN hδ hδ1 hθ hd s hs)
  apply h.trans
  have hκ := kappa_pos hN hδ
  have hkN : (count s.coeff : ℝ) ≤ N := by exact_mod_cast count_le s.coeff
  have hfirst := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hkN (show 0 ≤ 3*kappa N δ by positivity))
    (sq_nonneg (movementStep v δ θ))
  have hM : KSEighthInputTaylorBound.fourthBudget v θ ≤ fourthCap v θ := by unfold fourthCap; linarith
  have hsecond := mul_le_mul_of_nonneg_right hM
    (show 0 ≤ (N : ℝ)^2*movementStep v δ θ^4/24 by positivity)
  unfold driftPerStep
  nlinarith


theorem movement_total_budget (v : Fin N → Fin d → ℂ) {δ θ : ℝ}
    (hN : 0 < N) (hδ : 0 < δ) (hθ : 0 < θ) (hd : 0 < d) :
    driftPerStep v δ θ * (((N : ℝ)/64)/(movementStep v δ θ^2/2)) ≤ δ/1000 := by
  have ht := movementStep_pos v hN hδ hθ hd
  have he : driftPerStep v δ θ * (((N : ℝ)/64)/(movementStep v δ θ^2/2)) =
      (3/32 : ℝ)*kappa N δ*(N : ℝ)^2 +
        fourthCap v θ*(N : ℝ)^3*movementStep v δ θ^2/768 := by
    unfold driftPerStep
    field_simp [ht.ne']
    ring
  rw [he]
  have hk := KSEighthManuscriptBudgets.kappa_count_square hN δ
  have hr := KSEighthManuscriptBudgets.movement_remainder_budget v hN hδ hθ hd
  nlinarith

end MatrixSpencer.KSEighthManuscriptControllerDrift
