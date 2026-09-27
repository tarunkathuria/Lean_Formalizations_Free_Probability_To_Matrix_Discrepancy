import MatrixSpencer.DyadicOwnerWalkMesh
import MatrixSpencer.DyadicEpochLocalMoments

/-! The actual uniform potential drift mesh for finite dyadic epochs. -/
open Set Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace MatrixSpencer
noncomputable section
set_option maxHeartbeats 800000
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n] [Nonempty n]
local instance dyadicEpochDriftMeshCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance dyadicEpochDriftMeshSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance

def DyadicEpochConfig.taylorError (cfg : DyadicEpochConfig ι n) : ℝ :=
  Real.sqrt (Fintype.card ι : ℝ) / (200 * cfg.duration)

omit [DecidableEq ι] [Nonempty n] in
theorem DyadicEpochConfig.taylorError_pos (cfg : DyadicEpochConfig ι n) : 0 < cfg.taylorError := by
  have hk : (0 : ℝ) < Fintype.card ι := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 32) cfg.count_large)
  exact div_pos (Real.sqrt_pos.mpr hk) (mul_pos (by norm_num) cfg.duration_pos)

theorem DyadicEpochConfig.center_movedPoint (cfg : DyadicEpochConfig ι n) (C : Matrix ι ι ℝ)
    (x : EuclideanSpace ℝ ι) (h : ℝ) (o : ι × Bool) :
    cfg.center (epochMovedPoint C x h o) = cfg.center x +
      h • ownerPhysicalIncrement cfg.matrices cfg.hermitian (epochCoordinateIncrement C x o) :=
  epochCenter_add_smul cfg.offset cfg.matrices cfg.hermitian x (epochCoordinateIncrement C x o) h

/-- The potential drift over the retained positive samples equals the actual owner sampler drift. -/
theorem dyadicEpochPotentialDrift_eq_sampler (cfg : DyadicEpochConfig ι n)
    (s : DyadicEpochState ι) (h : ℝ)
    (htrace : 0 < realTrace (epochCovariance s.covariance (frozenCoordinates s.point) s.point)) :
    dyadicEpochPotentialDrift cfg s h =
      dyadicOwnerSamplerDrift cfg.matrices cfg.hermitian cfg.depth cfg.weight (cfg.center s.point)
        s.covariance (epochCovariance_posSemidef s.covariance (frozenCoordinates s.point) s.point) h := by
  rw [← positive_dyadicOwnerSamplerDrift_eq cfg.matrices cfg.hermitian cfg.depth cfg.weight
    (cfg.center s.point) s.covariance
    (epochCovariance_posSemidef s.covariance (frozenCoordinates s.point) s.point) htrace h]
  simp only [dyadicEpochPotentialDrift, DyadicEpochConfig.center_movedPoint,
    epochCoordinateIncrement, DyadicEpochConfig.potential, dyadicEpochMovedCovariance,
    dyadicOwnerPotential]

/-- One proved mesh works at every invariant state with this coefficient support.
All smoothness, bounded-direction, and response-monotonicity hypotheses are discharged. -/
theorem exists_dyadic_epoch_drift_mesh (cfg : DyadicEpochConfig ι n)
    (K : Submodule ℝ (EuclideanSpace ℝ ι)) :
    ∃ mesh > 0, mesh ≤ (1 / 2 : ℝ) ∧ mesh * Real.sqrt (Fintype.card ι) ≤ cfg.epsilon ∧
      ∀ s : DyadicEpochState ι, s.Invariant cfg → ¬ s.Terminal cfg →
        LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℝ) s.covariance).toLinearMap = K →
        ∀ h ∈ Icc (0 : ℝ) mesh,
          dyadicEpochPotentialDrift cfg s h ≤ cfg.energyRate * h ^ 2 := by
  obtain ⟨mesh, hmesh, hhalf, hround, hb⟩ := exists_dyadicOwnerWalkMesh
    cfg.matrices cfg.hermitian cfg.depth cfg.depth_positive cfg.weight cfg.weight_positive
    (‖cfg.offset‖ + Fintype.card ι)
    (show (0 : ℝ) < epochDustThreshold by norm_num [epochDustThreshold])
    cfg.taylorError_pos cfg.epsilon_pos K
  refine ⟨mesh, hmesh, hhalf, hround, ?_⟩
  intro s hs hactive hRange h hh
  have hdrift := hb (cfg.center s.point) s.covariance
    (epochCenter_norm_le cfg.offset cfg.matrices cfg.hermitian cfg.contractions s.point hs.regular.1)
    hs.covariance_pos hs.covariance_le_one hRange (hs.ready hactive).1
    (epochCovariance s.covariance (frozenCoordinates s.point) s.point)
    (epochCovariance_posSemidef s.covariance (frozenCoordinates s.point) s.point)
    (epochCovariance_le hs.covariance_pos _ _) (hs.sample_trace_positive hactive).2 h hh
  have htrace := dyadicOwnerCoefficientResponse_trace_mono cfg.matrices cfg.hermitian
    hs.covariance_pos cfg.depth cfg.depth_positive cfg.weight cfg.weight_positive (cfg.center s.point)
    (epochCovariance_le hs.covariance_pos (frozenCoordinates s.point) s.point)
  have hbound := mul_le_mul_of_nonneg_left (htrace.trans (hs.ready hactive).2) (sq_nonneg h)
  rw [dyadicEpochPotentialDrift_eq_sampler cfg s h (hs.sample_trace_positive hactive).2]
  change _ ≤ (cfg.responseCoefficient * Real.sqrt (Fintype.card ι) + cfg.taylorError) * h ^ 2
  nlinarith

end
end MatrixSpencer
