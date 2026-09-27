import SeamlessKS.AnalyticBounds
import SeamlessKS.Run

/-! End-to-end probability and output guarantees for the literal new walk.
Only the original Parseval vectors and the explicit affine SDP solver are
inputs. The local analytic, numerical, and stopping premises are all proved. -/
open Matrix Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace SeamlessKS.Probability
open MatrixSpencer SeamlessKS.State SeamlessKS.StatePotential SeamlessKS.Parameters SeamlessKS.Walk
open MatrixSpencer.KSFiniteCoinRun
attribute [local instance] Classical.propDecidable
variable {N d : ℕ}

theorem stepBounds [Nonempty (Fin d)] (O : KSConvexValueOracle.Solver)
    (v : Fin N → Fin d → ℂ) (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1) :
    TrialProbability.StepBounds Walk.terminal (Walk.step O v hd hp)
      (fun s => account v (Input.theta v) (zeta N) s.toCubeState)
      (fun s => Progress.entropy s.coeff)
      (fun s => ‖StatePotential.signedSum v s.coeff‖) (Walk.normReport v)
      0 (beta v) (movementStep v^2) (Input.delta v) where
  delta_pos := Input.delta_pos v hd hp
  c_pos := sq_pos_of_pos (movementStep_pos v hd hp)
  beta_nonneg := (beta_pos v hd hp).le
  entropy_nonneg := fun s => (Progress.entropy_bounds (coeff_abs_le s.toCubeState)).1
  entropy_drop := WalkGeometry.step_entropy O v hd hp
  potential_drift := AnalyticBounds.step_drift O v hd hp
  discrepancy_nonneg := fun s => norm_nonneg _
  discrepancy_le := fun s => by
    simpa only [add_zero] using
      StatePotential.norm_le_account v (Input.theta_pos v hd hp) (zeta N) s.toCubeState
  report_accuracy := fun s _ => Walk.normReport_accuracy v hd hp s

/-- One actual capped trial is accepted with probability at least three
quarters, including both numerical norm rejection and unfinished leaves. -/
theorem one_trial_acceptance_ge [Nonempty (Fin d)] (O : KSConvexValueOracle.Solver)
    (v : Fin N → Fin d → ℂ) (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1) :
    (3:ℝ)/4≤TrialProbability.Retry.singleSuccess (Run.attempt O v hd hp).leafWeight
      (fun l => Run.accepts v ((Run.attempt O v hd hp).leafState l)) := by
  exact TrialProbability.one_trial_acceptance_ge_three_quarters (stepBounds O v hd hp)
    (horizon v) (horizon_pos v hd hp) (Walk.initial v hd hp)
    (entropy_horizon_budget v hd hp _ (coeff_abs_le (Walk.initial v hd hp).toCubeState))
    (WalkGeometry.initial_ledger v hd hp)

/-- The probability is the product-weight sum of the actual first accepted
output event, after exactly the supplied finite retry budget. -/
theorem successProbability_ge [Nonempty (Fin d)] (O : KSConvexValueOracle.Solver)
    (v : Fin N → Fin d → ℂ) (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1) (r : ℕ) :
    1-(1/4:ℝ)^r≤Run.successProbability O v hd hp r := by
  have hh := TrialProbability.Retry.successProbability_ge (Run.attempt O v hd hp).leafWeight
    (fun l => ((Run.attempt O v hd hp).leafWeight_pos l).le)
    (Run.attempt O v hd hp).leafWeight_sum
    (fun l => ((Run.attempt O v hd hp).leafState l).coeff)
    (fun l => Run.accepts v ((Run.attempt O v hd hp).leafState l))
    (one_trial_acceptance_ge O v hd hp) r
  norm_num only [show (1-(3:ℝ)/4)=(1/4:ℝ) by norm_num] at hh
  exact hh

/-- Every returned original-label signing has the advertised bound for any
supplied upper bound on the atom sizes. -/
theorem output_sound [Nonempty (Fin d)] (O : KSConvexValueOracle.Solver)
    (v : Fin N → Fin d → ℂ) (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1)
    {ε : ℝ} (hε : 0≤ε) (hsize : ∀ i, ‖KSRankOne.atom (v i)‖≤ε)
    (r : ℕ) (z : Run.Draws O v hd hp r) (σ : Fin N → ℝ)
    (hout : Run.output O v hd hp r z=some σ) :
    (∀ i,IsSign (σ i)) ∧ ‖∑ i,σ i • KSRankOne.atom (v i)‖≤400*Real.sqrt ε := by
  have hs := Run.output_sound O v hd hp r z σ hout
  exact ⟨hs.1,hs.2.trans (mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt (Input.epsilon_le v hε hsize)) (by norm_num))⟩

/-- The complete positive-dimension endpoint names the defined algorithm,
its true probability, and its deterministic all-output certificate. -/
theorem actual_run_guarantee [Nonempty (Fin d)] (O : KSConvexValueOracle.Solver)
    (v : Fin N → Fin d → ℂ) (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1)
    {ε : ℝ} (hε : 0≤ε) (hsize : ∀ i, ‖KSRankOne.atom (v i)‖≤ε) (r : ℕ) :
    1-(1/4:ℝ)^r≤Run.successProbability O v hd hp r ∧
    (∀ z : Run.Draws O v hd hp r, ∀ σ : Fin N → ℝ,
      Run.output O v hd hp r z=some σ →
        (∀ i,IsSign (σ i)) ∧ ‖∑ i,σ i • KSRankOne.atom (v i)‖≤400*Real.sqrt ε) ∧
    (∀ s : WalkState N, ∀ b i, |s.coeff i|=1 → (Walk.step O v hd hp s b).coeff i=s.coeff i) :=
  ⟨successProbability_ge O v hd hp r,output_sound O v hd hp hε hsize r,
    WalkGeometry.step_preserves_frozen O v hd hp⟩

/-- In dimension zero the explicit all-ones answer uses no value queries. -/
def emptyDimensionOutput (N : ℕ) : Fin N → ℝ := fun _ => 1

theorem emptyDimensionOutput_sound (v : Fin N → Fin 0 → ℂ) {ε : ℝ} (hε : 0≤ε) :
    (∀ i,IsSign (emptyDimensionOutput N i)) ∧
      ‖∑ i,emptyDimensionOutput N i • KSRankOne.atom (v i)‖≤400*Real.sqrt ε := by
  constructor
  · intro i
    exact Or.inl rfl
  · have he : (∑ i,emptyDimensionOutput N i • KSRankOne.atom (v i))=
        (0 : Matrix (Fin 0) (Fin 0) ℂ) := Subsingleton.elim _ _
    rw [he,norm_zero]
    positivity

end SeamlessKS.Probability
