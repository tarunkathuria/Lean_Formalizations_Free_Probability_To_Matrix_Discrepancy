import MatrixSpencer.EpochState

/-!
# An actual initialized epoch

The identity owner is prepared by the proved compact minimization and
finite dust procedure. All state invariants and the initial paid energy
budget are discharged for that actual choice.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix Set
noncomputable section
namespace MatrixSpencer

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n] [Nonempty n]
local instance epochInitialCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance epochInitialSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance

def initialEpochState (cfg : EpochConfig ι n) (C : Matrix ι ι ℝ) (p d : ℝ) : EpochState ι :=
  ⟨cfg.start, C, 0, p, d, 0, 0⟩

theorem frozenCoordinates_start_empty (cfg : EpochConfig ι n) :
    frozenCoordinates cfg.start = ∅ := by
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro i hi
  exact cfg.start_unfrozen i ((mem_frozenCoordinates cfg.start i).mp hi)

theorem initialEpochState_invariant (cfg : EpochConfig ι n)
    {C : Matrix ι ι ℝ} {p d : ℝ}
    (hp : DustPreparedOwner (cfg.center cfg.start) cfg.matrices cfg.hermitian
      1 epochTracePriceScale epochDustThreshold 1 C p d) :
    (initialEpochState cfg C p d).Invariant cfg := by
  have htrace := hp.trace_account
  have htraceI : realTrace (1 : Matrix ι ι ℝ) = Fintype.card ι := by simp [realTrace]
  have hdust := hp.dust_budget
  rw [Matrix.rank_one] at hdust
  refine ⟨cfg.start_regular, hp.covariance.1.posSemidef, hp.covariance.2,
    le_rfl, by norm_num [epochTimeLimit, initialEpochState], hp.paid_nonneg, hp.dust_nonneg, le_rfl,
    ?_, hdust, ?_, ?_, ?_, ?_⟩
  · change (Fintype.card ι : ℝ) * (1 - 0) - p - d ≤ realTrace C
    rw [realTrace_sub, htraceI] at htrace
    linarith
  · change (0 : ℝ) ≤ cfg.epsilon * (frozenCoordinates cfg.start).card
    rw [frozenCoordinates_start_empty]
    simp
  · change |ownerCertificateTangent cfg.anchor 1 (cfg.center cfg.start) - 0| ≤ 0
    simp only [EpochConfig.anchor, ownerCertificateTangent, sub_self, Matrix.mul_zero,
      realTrace_zero, sub_zero, abs_zero, le_refl]
  · change ‖cfg.start‖ ^ 2 + (Fintype.card ι : ℝ) / 16 * 0 ≤ ‖cfg.start‖ ^ 2
    simp
  · intro _
    refine ⟨hp.floor, ?_⟩
    have hr := hp.response
    have hsqrt : Real.sqrt epochTracePriceScale = 64 := by norm_num [epochTracePriceScale]
    rw [hsqrt] at hr
    change realTrace (C * ownerCoefficientResponse cfg.matrices cfg.hermitian C 1
      (cfg.center cfg.start)) ≤ epochResponseConstant * Real.sqrt (Fintype.card ι : ℝ)
    have hs := Real.sqrt_nonneg (Fintype.card ι : ℝ)
    dsimp only [epochResponseConstant]
    linarith

/-- Prepared initialization exists and starts with at most twice the square-root label budget. -/
theorem exists_initial_epoch (cfg : EpochConfig ι n) :
    ∃ s : EpochState ι, s.Invariant cfg ∧ s.point = cfg.start ∧ s.time = 0 ∧
      s.tangent = 0 ∧ s.rounding = 0 ∧
      ownerCertificate cfg.anchor cfg.matrices 1 (cfg.center s.point) s.covariance +
        (epochTracePriceScale / Real.sqrt (Fintype.card ι : ℝ)) * s.paid ≤
          2 * Real.sqrt (Fintype.card ι : ℝ) := by
  have hk : 0 < Fintype.card ι := lt_of_lt_of_le (by norm_num : 0 < 32) cfg.count_large
  obtain ⟨C, p, d, hp⟩ := exists_dust_prepared_owner (cfg.center cfg.start)
    cfg.matrices cfg.hermitian cfg.contractions (C := 1) Matrix.PosSemidef.one le_rfl
    (by norm_num : (0 : ℝ) < 1) (by norm_num [epochTracePriceScale] : 0 < epochTracePriceScale)
    (by norm_num [epochDustThreshold] : 0 < epochDustThreshold) hk
  refine ⟨initialEpochState cfg C p d, initialEpochState_invariant cfg hp,
    rfl, rfl, rfl, rfl, ?_⟩
  change ownerCertificate cfg.anchor cfg.matrices 1 cfg.anchor C +
    (epochTracePriceScale / Real.sqrt (Fintype.card ι : ℝ)) * p ≤ _
  rw [ownerCertificate_at_anchor]
  have hinit := ownerPotential_le_base_add cfg.anchor cfg.matrices cfg.hermitian cfg.contractions
    (C := 1) Matrix.PosSemidef.one le_rfl 1
  have hpay := hp.payment
  change ownerPotential cfg.anchor cfg.matrices C 1 +
    (epochTracePriceScale / Real.sqrt (Fintype.card ι : ℝ)) * p ≤
      ownerPotential cfg.anchor cfg.matrices 1 1 at hpay
  linarith

end MatrixSpencer
