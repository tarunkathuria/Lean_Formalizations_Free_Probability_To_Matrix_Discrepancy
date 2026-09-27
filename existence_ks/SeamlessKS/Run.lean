import SeamlessKS.WalkGeometry

/-! The actual capped local walk, norm test, and first-accepted return value.
The deterministic output guarantee and completion bound are unconditional;
the spectral probability estimate is assembled after actual potential drift. -/
open Set Matrix
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace SeamlessKS.Run
open MatrixSpencer SeamlessKS.State SeamlessKS.StatePotential SeamlessKS.Parameters SeamlessKS.Walk
open MatrixSpencer.KSFiniteCoinRun
attribute [local instance] Classical.propDecidable
variable {N d : ℕ} [Nonempty (Fin d)]

def attempt (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ)
    (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1) :=
  runTree Walk.terminal (Walk.step O v hd hp) (horizon v) (Walk.initial v hd hp)

def accepts (v : Fin N → Fin d → ℂ) (s : WalkState N) : Bool :=
  TrialProbability.accepts Walk.terminal (normReport v) (Input.delta v) s

abbrev Draws (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ)
    (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1) (r : ℕ) :=
  TrialProbability.Retry.Draws (attempt O v hd hp).Leaves r

def output (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ)
    (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1) (r : ℕ) :
    Draws O v hd hp r → Option (Fin N → ℝ) :=
  TrialProbability.Retry.firstAccepted (fun l => ((attempt O v hd hp).leafState l).coeff)
    (fun l => accepts v ((attempt O v hd hp).leafState l)) r

def drawWeight (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ)
    (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1) (r : ℕ) :
    Draws O v hd hp r → ℝ := TrialProbability.Retry.weight (attempt O v hd hp).leafWeight r

theorem drawWeight_nonneg (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ)
    (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1) (r : ℕ) (z : Draws O v hd hp r) :
    0≤drawWeight O v hd hp r z :=
  TrialProbability.Retry.weight_nonneg _ (fun l => ((attempt O v hd hp).leafWeight_pos l).le) r z

theorem drawWeight_sum (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ)
    (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1) (r : ℕ) :
    (∑ z : Draws O v hd hp r,drawWeight O v hd hp r z)=1 :=
  TrialProbability.Retry.weight_sum _ (attempt O v hd hp).leafWeight_sum r

theorem accepts_sound (v : Fin N → Fin d → ℂ) (hd : 0<d)
    (hp : ∑ i,KSRankOne.atom (v i)=1) (s : WalkState N) (ha : accepts v s=true) :
    (∀ i,IsSign (s.coeff i)) ∧ ‖StatePotential.signedSum v s.coeff‖≤400*Input.delta v := by
  obtain ⟨ht,hr⟩ := (TrialProbability.accepts_iff s).mp ha
  have he := (abs_le.mp (Walk.normReport_accuracy v hd hp s)).1
  exact ⟨(State.terminal_iff_signing s.toCubeState).mp ht,by linarith⟩

/-- Every actual returned value is a full original-label signing and passes
its independently computed norm certificate. -/
theorem output_sound (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ)
    (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1) (r : ℕ) (z : Draws O v hd hp r)
    (σ : Fin N → ℝ) (hout : output O v hd hp r z=some σ) :
    (∀ i,IsSign (σ i)) ∧ ‖∑ i,σ i • KSRankOne.atom (v i)‖≤400*Input.delta v := by
  apply TrialProbability.Retry.firstAccepted_sound _ _
    (fun σ => (∀ i,IsSign (σ i)) ∧ ‖∑ i,σ i • KSRankOne.atom (v i)‖≤400*Input.delta v)
    _ r z σ hout
  intro l hl
  exact accepts_sound v hd hp _ hl

def successProbability (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ)
    (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1) (r : ℕ) : ℝ :=
  ∑ z : Draws O v hd hp r, drawWeight O v hd hp r z *
    (if (output O v hd hp r z).isSome then 1 else 0)

/-- The actual local walk completes with probability at least 7/8 at its
explicit horizon. This theorem already discharges every progress premise. -/
theorem cutoff_le_eighth (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ)
    (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1) :
    activeProbability Walk.terminal (Walk.step O v hd hp) (horizon v) (Walk.initial v hd hp)≤1/8 := by
  let R : WalkState N → ℝ := fun s => 2*(N:ℝ)-Progress.entropy s.coeff
  have hbound : ∀ s, R s≤2*(N:ℝ) := by
    intro s
    have he := (Progress.entropy_bounds (coeff_abs_le s.toCubeState)).1
    dsimp only [R]
    linarith
  have hgain : ∀ s, ¬Walk.terminal s → R s+movementStep v^2≤
      (R (Walk.step O v hd hp s false)+R (Walk.step O v hd hp s true))/2 := by
    intro s hs
    have hh := WalkGeometry.step_entropy O v hd hp s hs
    dsimp only [R]
    linarith
  have hr : 0≤R (Walk.initial v hd hp) := by
    exact sub_nonneg.mpr (TrialProbability.entropy_le_two_labels _
      (coeff_abs_le (Walk.initial v hd hp).toCubeState))
  have hh := activeProbability_le Walk.terminal (Walk.step O v hd hp) R
    (sq_pos_of_pos (movementStep_pos v hd hp)) hbound hgain
    (horizon v) (horizon_pos v hd hp) (Walk.initial v hd hp) hr
  apply hh.trans
  have hpos : 0<movementStep v^2*(horizon v:ℝ) :=
    mul_pos (sq_pos_of_pos (movementStep_pos v hd hp)) (Nat.cast_pos.mpr (horizon_pos v hd hp))
  apply (div_le_iff₀ hpos).mpr
  have hb := horizon_budget v hd hp
  linarith

end SeamlessKS.Run
