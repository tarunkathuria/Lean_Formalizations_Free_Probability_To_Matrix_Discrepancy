import MatrixSpencer.DyadicEpochState

/-!
# Initialization from concrete dyadic preparation data

The matrix, trace payment, floor, and response facts remain explicit
preparation data. No analytic existence is asserted here.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix Set
noncomputable section
namespace MatrixSpencer

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n] [Nonempty n]
local instance dyadicEpochInitialCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance dyadicEpochInitialSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance

def initialDyadicEpochState (cfg : DyadicEpochConfig ι n) (C : Matrix ι ι ℝ) (p d : ℝ) : DyadicEpochState ι :=
  ⟨cfg.start, C, 0, p, d, 0, 0⟩

omit [Nonempty n] in
theorem dyadic_frozenCoordinates_start_empty (cfg : DyadicEpochConfig ι n) :
    frozenCoordinates cfg.start = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  exact cfg.start_unfrozen i ((mem_frozenCoordinates cfg.start i).mp hi)

theorem initialDyadicEpochState_invariant (cfg : DyadicEpochConfig ι n)
    {C : Matrix ι ι ℝ} {p d : ℝ}
    (hp : DyadicPreparedCovariance cfg (cfg.center cfg.start) 1 C p d) :
    (initialDyadicEpochState cfg C p d).Invariant cfg := by
  have htrace := hp.trace_account
  have htraceI : realTrace (1 : Matrix ι ι ℝ) = Fintype.card ι := by simp [realTrace]
  have hdust := hp.dust_budget
  rw [Matrix.rank_one] at hdust
  refine ⟨cfg.start_regular, hp.covariance.1.posSemidef, hp.covariance.2,
    le_rfl, cfg.duration_pos.le, hp.paid_nonneg, hp.dust_nonneg, le_rfl,
    ?_, hdust, ?_, ?_, ?_, ?_⟩
  · change (Fintype.card ι : ℝ) * (1 - 0) - p - d ≤ realTrace C
    rw [realTrace_sub, htraceI] at htrace
    linarith
  · change (0 : ℝ) ≤ cfg.epsilon * (frozenCoordinates cfg.start).card
    rw [dyadic_frozenCoordinates_start_empty]
    simp
  · change |dyadicOwnerCertificateTangent cfg.anchor cfg.depth cfg.weight (cfg.center cfg.start) - 0| ≤ 0
    simp only [DyadicEpochConfig.anchor, dyadicOwnerCertificateTangent, sub_self, Matrix.mul_zero,
      realTrace_zero, abs_zero, le_refl]
  · change ‖cfg.start‖ ^ 2 + (Fintype.card ι : ℝ) / 16 * 0 ≤ ‖cfg.start‖ ^ 2
    simp
  · intro _
    exact ⟨hp.floor, hp.response⟩

/-- Initialization is certified by explicit actual preparation data. -/
theorem initialDyadicEpochState_energy_le (cfg : DyadicEpochConfig ι n)
    {C : Matrix ι ι ℝ} {p d : ℝ}
    (hp : DyadicPreparedCovariance cfg (cfg.center cfg.start) 1 C p d) :
    dyadicOwnerCertificate cfg.anchor cfg.matrices cfg.depth cfg.weight cfg.anchor C +
      (epochTracePriceScale / Real.sqrt (Fintype.card ι : ℝ)) * p ≤
        2 * Real.sqrt (Fintype.card ι : ℝ) := by
  rw [dyadicOwnerCertificate_at_anchor]
  have hinit := regularizedOwnerPotential_le_base_add cfg.anchor cfg.matrices cfg.hermitian
    cfg.contractions (C := 1) Matrix.PosSemidef.one le_rfl
    (dyadicTsallisRegularizer cfg.depth cfg.weight)
    (continuousOn_density_dyadicTsallisRegularizer cfg.depth cfg.weight)
  have hpay := hp.payment
  change regularizedOwnerPotential cfg.anchor cfg.matrices C
      (dyadicTsallisRegularizer cfg.depth cfg.weight) +
    (epochTracePriceScale / Real.sqrt (Fintype.card ι : ℝ)) * p ≤
      regularizedOwnerPotential cfg.anchor cfg.matrices 1
        (dyadicTsallisRegularizer cfg.depth cfg.weight) at hpay
  linarith

end MatrixSpencer
