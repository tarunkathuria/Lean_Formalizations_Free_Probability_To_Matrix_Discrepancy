import RadialKS.Walk

/-! Every movement increases squared Euclidean norm; boundary preparation
preserves this progress and freezes coordinates only near a true cube face. -/
open Set Matrix
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace RadialKS.WalkGeometry
open MatrixSpencer SeamlessKS SeamlessKS.State SeamlessKS.StatePotential SeamlessKS.Proposals
open SeamlessKS.Parameters RadialKS.Walk
attribute [local instance] Classical.propDecidable
variable {N d : ℕ} [Nonempty (Fin d)]

theorem rawStep_some (O : KSConvexValueOracle.Solver)
    (v : Fin N → Fin d → ℂ) (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1)
    (s : WalkState N) (hs : ¬Walk.terminal s) (i : Fin N)
    (hi : chosenLabel O v s=some i) :
    rawStep O v hd hp s hs = outwardMove (rho_pos (Input.labels_pos v hd hp)) s i
      (OutwardSelection.selected_live O v _ _ _ _ s i hi) (outwardStep N)
      (outwardStep_pos (Input.labels_pos v hd hp)).le
      (by unfold outwardStep; have hr := rho_pos (Input.labels_pos v hd hp); linarith) := by
  unfold rawStep
  split
  · rename_i j hj
    have he : j=i := Option.some.inj (hj.symm.trans hi)
    subst j
    rfl
  · rename_i hj
    rw [hi] at hj
    contradiction

theorem rawStep_none (O : KSConvexValueOracle.Solver)
    (v : Fin N → Fin d → ℂ) (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1)
    (s : WalkState N) (hs : ¬Walk.terminal s)
    (hi : chosenLabel O v s=none) :
    rawStep O v hd hp s hs = Progress.radialMove (rho_pos (Input.labels_pos v hd hp)) s
      (direction O v hd hp s hs hi) (direction_norm O v hd hp s hs hi)
      (direction_frozen O v hd hp s hs hi)
      (signedStep v (chooseSign O v hd hp s hs hi))
      (SeamlessKS.Walk.signedStep_bound v hd hp _) := by
  unfold rawStep
  split
  · rename_i j hj
    rw [hi] at hj
    contradiction
  · rfl

theorem rawStep_preserves_frozen (O : KSConvexValueOracle.Solver)
    (v : Fin N → Fin d → ℂ) (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1)
    (s : WalkState N) (hs : ¬Walk.terminal s)
    (i : Fin N) (hi : |s.coeff i|=1) : (rawStep O v hd hp s hs).coeff i=s.coeff i := by
  unfold rawStep
  split
  · rename_i j hj
    exact outward_preserves_frozen s j (OutwardSelection.selected_live O v _ _ _ _ s j hj) _ i hi
  · exact Progress.proposal_frozen s _ (direction_frozen O v hd hp s hs _) _ i hi

theorem rawStep_displacement (O : KSConvexValueOracle.Solver)
    (v : Fin N → Fin d → ℂ) (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1)
    (s : WalkState N) (hs : ¬Walk.terminal s) (i : Fin N) :
    |(rawStep O v hd hp s hs).coeff i-s.coeff i|≤rho N/8 := by
  unfold rawStep
  split
  · apply (outward_displacement (outwardStep_pos (Input.labels_pos v hd hp)).le s.coeff _ i).trans
    unfold outwardStep
    have hr := rho_pos (Input.labels_pos v hd hp)
    linarith
  · rename_i hn
    apply (Progress.proposal_displacement s.coeff _ (direction_norm O v hd hp s hs hn) _ i).trans
    have hb := SeamlessKS.Walk.signedStep_bound v hd hp (chooseSign O v hd hp s hs hn)
    have hr := rho_pos (Input.labels_pos v hd hp)
    linarith

theorem rawStep_energy (O : KSConvexValueOracle.Solver)
    (v : Fin N → Fin d → ℂ) (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1)
    (s : WalkState N) (hs : ¬Walk.terminal s) :
    Progress.energy s.coeff + movementStep v^2 ≤ Progress.energy (rawStep O v hd hp s hs).coeff := by
  have hN := Input.labels_pos v hd hp
  have hh := movementStep_pos v hd hp
  have hha : movementStep v^2≤outwardStep N^2 :=
    pow_le_pow_left₀ hh.le (movementStep_le_outwardStep v) 2
  cases hi : chosenLabel O v s with
  | some i =>
    rw [rawStep_some O v hd hp s hs i hi]
    exact (add_le_add_left hha _).trans (Progress.outward_energy s.coeff i (outwardStep_pos hN).le)
  | none =>
    rw [rawStep_none O v hd hp s hs hi,
      Progress.radialMove_energy _ _ _ _ _ (direction_orthogonal O v hd hp s hs hi)]
    cases chooseSign O v hd hp s hs hi <;>
      simp [signedStep,SeamlessKS.Walk.signedStep]

theorem step_energy (O : KSConvexValueOracle.Solver)
    (v : Fin N → Fin d → ℂ) (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1)
    (s : WalkState N) (hs : ¬Walk.terminal s) :
    Progress.energy s.coeff + movementStep v^2 ≤ Progress.energy (Walk.step O v hd hp s).coeff := by
  have hr := rawStep_energy O v hd hp s hs
  have hp' := Progress.prepare_energy (rho_pos (Input.labels_pos v hd hp)).le
    (rawStep O v hd hp s hs)
  simp only [Walk.step,dif_neg hs]
  exact hr.trans hp'

theorem step_preserves_frozen (O : KSConvexValueOracle.Solver)
    (v : Fin N → Fin d → ℂ) (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1)
    (s : WalkState N) (i : Fin N) (hi : |s.coeff i|=1) :
    (Walk.step O v hd hp s).coeff i=s.coeff i := by
  by_cases hs : Walk.terminal s
  · rw [Walk.step_terminal O v hd hp s hs]
  · simp only [Walk.step,dif_neg hs]
    rw [prepare_preserves_frozen _ _ i (by rw [rawStep_preserves_frozen O v hd hp s hs i hi]; exact hi),
      rawStep_preserves_frozen O v hd hp s hs i hi]

end RadialKS.WalkGeometry
