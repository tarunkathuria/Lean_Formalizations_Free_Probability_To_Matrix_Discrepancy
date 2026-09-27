import MatrixSpencer.OwnerWalkMesh
import MatrixSpencer.EpochState
import MatrixSpencer.FiniteBranchingTermination

/-! The actual support-dependent epoch step and its finite rank/fuel clock. -/
open Set Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace MatrixSpencer
noncomputable section
set_option maxHeartbeats 800000
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n] [Nonempty n]
local instance epochWalkMeshCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance epochWalkMeshPhysicalSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance

/-- The per-unit-time Taylor allowance used throughout the epoch. -/
def epochTaylorError (ι : Type*) [Fintype ι] : ℝ :=
  Real.sqrt (Fintype.card ι) / (200 * epochTimeLimit)

omit [DecidableEq ι] [Nonempty n] in
theorem epochTaylorError_pos (cfg : EpochConfig ι n) : 0 < epochTaylorError ι := by
  have hk : (0 : ℝ) < Fintype.card ι := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 32) cfg.count_large)
  exact div_pos (Real.sqrt_pos.mpr hk) (by norm_num [epochTimeLimit])

def EpochState.support (s : EpochState ι) : Submodule ℝ (EuclideanSpace ℝ ι) :=
  LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℝ) s.covariance).toLinearMap

/-- This proved existence term depends only on cfg and the coefficient subspace. -/
def EpochConfig.meshExistence (cfg : EpochConfig ι n) (K : Submodule ℝ (EuclideanSpace ℝ ι)) :=
  exists_ownerWalkMesh cfg.matrices cfg.hermitian (show (0 : ℝ) < 1 by norm_num)
    (‖cfg.offset‖ + Fintype.card ι) (show (0 : ℝ) < epochDustThreshold by norm_num [epochDustThreshold])
    (epochTaylorError_pos cfg) cfg.epsilon_pos K

def EpochConfig.mesh (cfg : EpochConfig ι n) (K : Submodule ℝ (EuclideanSpace ℝ ι)) : ℝ :=
  Classical.choose (cfg.meshExistence K)

theorem EpochConfig.mesh_pos (cfg : EpochConfig ι n) (K : Submodule ℝ (EuclideanSpace ℝ ι)) :
    0 < cfg.mesh K := (Classical.choose_spec (cfg.meshExistence K)).1

theorem EpochConfig.mesh_le_half (cfg : EpochConfig ι n) (K : Submodule ℝ (EuclideanSpace ℝ ι)) :
    cfg.mesh K ≤ (1 / 2 : ℝ) := (Classical.choose_spec (cfg.meshExistence K)).2.1

theorem EpochConfig.mesh_rounding (cfg : EpochConfig ι n) (K : Submodule ℝ (EuclideanSpace ℝ ι)) :
    cfg.mesh K * Real.sqrt (Fintype.card ι) ≤ cfg.epsilon :=
  (Classical.choose_spec (cfg.meshExistence K)).2.2.1

/-- The only shortening of a support mesh is the final step to the time horizon. -/
def EpochConfig.step (cfg : EpochConfig ι n) (s : EpochState ι) : ℝ :=
  epochMeshStep (cfg.mesh s.support) epochTimeLimit s.time

def EpochConfig.fuel (cfg : EpochConfig ι n) (s : EpochState ι) : ℕ :=
  epochMeshFuel (cfg.mesh s.support) epochTimeLimit s.time

omit [DecidableEq ι] in
theorem EpochState.time_lt_of_active (s : EpochState ι) (hactive : ¬ s.Terminal) :
    s.time < epochTimeLimit := lt_of_not_ge (fun ht => hactive (Or.inr (Or.inr ht)))

theorem EpochConfig.step_pos (cfg : EpochConfig ι n) (s : EpochState ι) (hactive : ¬ s.Terminal) :
    0 < cfg.step s := epochMeshStep_pos (cfg.mesh_pos _) (s.time_lt_of_active hactive)

theorem EpochConfig.step_le_mesh (cfg : EpochConfig ι n) (s : EpochState ι) :
    cfg.step s ≤ cfg.mesh s.support := epochMeshStep_le _ _ _

theorem EpochConfig.step_le_half (cfg : EpochConfig ι n) (s : EpochState ι) :
    cfg.step s ≤ (1 / 2 : ℝ) := (cfg.step_le_mesh s).trans (cfg.mesh_le_half _)

theorem EpochConfig.step_rounding (cfg : EpochConfig ι n) (s : EpochState ι) :
    cfg.step s * Real.sqrt (Fintype.card ι) ≤ cfg.epsilon :=
  (mul_le_mul_of_nonneg_right (cfg.step_le_mesh s) (Real.sqrt_nonneg _)).trans (cfg.mesh_rounding _)

theorem EpochConfig.step_time_le (cfg : EpochConfig ι n) (s : EpochState ι) (hactive : ¬ s.Terminal) :
    s.time + cfg.step s ^ 2 ≤ epochTimeLimit :=
  epochMeshStep_time_le (cfg.mesh_pos _) (s.time_lt_of_active hactive)

/-- The proved mesh estimate applies to the actual covariance short and actual center. -/
theorem EpochState.Invariant.step_drift {cfg : EpochConfig ι n} {s : EpochState ι}
    (hs : s.Invariant cfg) (hactive : ¬ s.Terminal) :
    ownerSamplerDrift cfg.matrices cfg.hermitian 1 (cfg.center s.point) s.covariance
      (epochCovariance_posSemidef s.covariance (frozenCoordinates s.point) s.point) (cfg.step s) ≤
      cfg.step s ^ 2 * realTrace (epochCovariance s.covariance (frozenCoordinates s.point) s.point *
        ownerCoefficientResponse cfg.matrices cfg.hermitian s.covariance 1 (cfg.center s.point)) +
        epochTaylorError ι * cfg.step s ^ 2 := by
  have hb := (Classical.choose_spec (cfg.meshExistence s.support)).2.2.2
  exact hb (cfg.center s.point) s.covariance
    (epochCenter_norm_le cfg.offset cfg.matrices cfg.hermitian cfg.contractions s.point hs.regular.1)
    hs.covariance_pos hs.covariance_le_one rfl (hs.ready hactive).1
    (epochCovariance s.covariance (frozenCoordinates s.point) s.point)
    (epochCovariance_posSemidef s.covariance (frozenCoordinates s.point) s.point)
    (epochCovariance_le hs.covariance_pos _ _) (hs.sample_trace_positive hactive).2
    (cfg.step s) ⟨(cfg.step_pos s hactive).le, cfg.step_le_mesh s⟩

/-- Positivity of the actual response turns Q≤C into the prepared scalar drift cap. -/
theorem EpochState.Invariant.step_drift_capped {cfg : EpochConfig ι n} {s : EpochState ι}
    (hs : s.Invariant cfg) (hactive : ¬ s.Terminal) :
    ownerSamplerDrift cfg.matrices cfg.hermitian 1 (cfg.center s.point) s.covariance
      (epochCovariance_posSemidef s.covariance (frozenCoordinates s.point) s.point) (cfg.step s) ≤
      (epochResponseConstant * Real.sqrt (Fintype.card ι) + epochTaylorError ι) * cfg.step s ^ 2 := by
  have htrace := ownerCoefficientResponse_trace_mono cfg.matrices cfg.hermitian hs.covariance_pos
    (show (0 : ℝ) < 1 by norm_num) (cfg.center s.point)
    (epochCovariance_le hs.covariance_pos (frozenCoordinates s.point) s.point)
  have hbound := mul_le_mul_of_nonneg_left (htrace.trans (hs.ready hactive).2) (sq_nonneg (cfg.step s))
  have hdrift := hs.step_drift hactive
  nlinarith

/-- The full-center expression agrees with the actual sampled coefficient movement. -/
theorem EpochConfig.center_epochMovedPoint (cfg : EpochConfig ι n) (C : Matrix ι ι ℝ)
    (x : EuclideanSpace ℝ ι) (h : ℝ) (o : ι × Bool) :
    cfg.center (epochMovedPoint C x h o) = cfg.center x +
      h • ownerPhysicalIncrement cfg.matrices cfg.hermitian (epochCoordinateIncrement C x o) :=
  epochCenter_add_smul cfg.offset cfg.matrices cfg.hermitian x (epochCoordinateIncrement C x o) h

/-- The same actual drift bound over only the positive branches, stated at the
actual moved coefficient point used by the finite transition construction. -/
theorem EpochState.Invariant.step_positive_drift_capped {cfg : EpochConfig ι n} {s : EpochState ι}
    (hs : s.Invariant cfg) (hactive : ¬ s.Terminal) :
    (∑ o : PositiveCovarianceOutcome (epochCovariance_posSemidef s.covariance (frozenCoordinates s.point) s.point),
      covarianceSampleWeight (epochCovariance_posSemidef s.covariance (frozenCoordinates s.point) s.point) o *
        (ownerPotential (cfg.center (epochMovedPoint s.covariance s.point (cfg.step s) o)) cfg.matrices
          (s.covariance - cfg.step s ^ 2 • epochCovariance s.covariance (frozenCoordinates s.point) s.point) 1 -
          ownerPotential (cfg.center s.point) cfg.matrices s.covariance 1)) ≤
      (epochResponseConstant * Real.sqrt (Fintype.card ι) + epochTaylorError ι) * cfg.step s ^ 2 := by
  have hdrift := hs.step_drift_capped hactive
  rw [← positive_ownerSamplerDrift_eq cfg.matrices cfg.hermitian 1 (cfg.center s.point)
    s.covariance (epochCovariance_posSemidef s.covariance (frozenCoordinates s.point) s.point)
    (hs.sample_trace_positive hactive).2 (cfg.step s)] at hdrift
  simpa only [EpochConfig.center_epochMovedPoint, epochCoordinateIncrement] using hdrift

/-- Matrix rank agrees with the dimension of the actual Euclidean operator range. -/
theorem matrix_rank_eq_finrank_euclidean_range (C : Matrix ι ι ℝ) :
    C.rank = Module.finrank ℝ (LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℝ) C).toLinearMap) := by
  rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin, Matrix.toEuclideanLin_eq_toLin]
  exact C.rank_eq_finrank_range_toLin (PiLp.basisFun 2 ℝ ι) (PiLp.basisFun 2 ℝ ι)

/-- Under PSD domination, unchanged rank forces literal equality of supports. -/
theorem posSemidef_range_eq_of_le_of_rank_eq {C D : Matrix ι ι ℝ}
    (hC : C.PosSemidef) (hD : D.PosSemidef) (hDC : D ≤ C) (hrank : D.rank = C.rank) :
    LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℝ) D).toLinearMap =
      LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℝ) C).toLinearMap := by
  apply Submodule.eq_of_le_of_finrank_eq (posSemidef_range_le_of_le hD hC hDC)
  simpa only [← matrix_rank_eq_finrank_euclidean_range] using hrank

/-- Positive fuel remains at every active state. -/
theorem EpochConfig.fuel_pos (cfg : EpochConfig ι n) (s : EpochState ι) (hactive : ¬ s.Terminal) :
    0 < cfg.fuel s := epochMeshFuel_pos (cfg.mesh_pos _) (s.time_lt_of_active hactive)

/-- Equal-rank PSD children use exactly the parent's support mesh. -/
theorem EpochConfig.mesh_eq_of_rank_eq (cfg : EpochConfig ι n) {s t : EpochState ι}
    (hs : s.covariance.PosSemidef) (ht : t.covariance.PosSemidef)
    (hcov : t.covariance ≤ s.covariance) (hrank : t.covariance.rank = s.covariance.rank) :
    cfg.mesh t.support = cfg.mesh s.support :=
  congrArg cfg.mesh (posSemidef_range_eq_of_le_of_rank_eq hs ht hcov hrank)

/-- Every actual child decreases the natural clock when its covariance rank is unchanged. -/
theorem EpochConfig.fuel_decreases_of_rank_eq (cfg : EpochConfig ι n) {s t : EpochState ι}
    (hs : s.covariance.PosSemidef) (ht : t.covariance.PosSemidef)
    (hactive : ¬ s.Terminal) (hcov : t.covariance ≤ s.covariance)
    (hrank : t.covariance.rank = s.covariance.rank)
    (htime : t.time = s.time + cfg.step s ^ 2) : cfg.fuel t < cfg.fuel s := by
  have hm := cfg.mesh_eq_of_rank_eq hs ht hcov hrank
  unfold EpochConfig.fuel
  rw [hm, htime]
  exact epochMeshFuel_decreases (cfg.mesh_pos _) (s.time_lt_of_active hactive)

/-- An arbitrary new support mesh is harmless on a strict rank loss; otherwise
PSD order fixes the support and the actual capped step strictly decreases fuel. -/
theorem EpochConfig.rank_fuel_decrease (cfg : EpochConfig ι n) {s t : EpochState ι}
    (hs : s.covariance.PosSemidef) (ht : t.covariance.PosSemidef)
    (hactive : ¬ s.Terminal) (hcov : t.covariance ≤ s.covariance)
    (htime : t.time = s.time + cfg.step s ^ 2) :
    FiniteBranchingTermination.RankFuelDecrease (fun v : EpochState ι => v.covariance.rank)
      cfg.fuel t s := by
  have hrank := CovarianceDust.rank_le_of_posSemidef_le ht hcov
  rcases lt_or_eq_of_le hrank with hlt | heq
  · exact Or.inl hlt
  · exact Or.inr ⟨heq, cfg.fuel_decreases_of_rank_eq hs ht hactive hcov heq htime⟩

end
end MatrixSpencer
