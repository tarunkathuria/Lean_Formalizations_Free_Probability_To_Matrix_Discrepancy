import SeamlessKS.Walk

/-! All-path geometry and entropy progress of the defined walk. -/
open Set Matrix
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace SeamlessKS.WalkGeometry
open MatrixSpencer SeamlessKS.State SeamlessKS.StatePotential SeamlessKS.Proposals
open SeamlessKS.Parameters SeamlessKS.Walk
attribute [local instance] Classical.propDecidable
variable {N d : ℕ}

theorem rho_lt_one (hN : 0<N) : rho N<1 := by
  have hn : (1:ℝ)≤N := by exact_mod_cast hN
  have hp : (0:ℝ)<100*(N:ℝ)^2 := by positivity
  unfold rho
  apply (div_lt_iff₀ hp).mpr
  nlinarith

theorem initial_coeff_zero (v : Fin N → Fin d → ℂ) (hd : 0<d)
    (hp : ∑ i,KSRankOne.atom (v i)=1) : (Walk.initial v hd hp).coeff=0 := by
  have hr := rho_lt_one (Input.labels_pos v hd hp)
  ext i
  simp [Walk.initial,State.initial,prepare,KSCubePreparation.snap,not_le.mpr hr]

/-- The entire remaining rounding allowance is smaller than the local
spectral tolerance. It is a proof quantity, not a stored walk register. -/
theorem reserve_le_beta (v : Fin N → Fin d → ℂ) (hd : 0<d)
    (hp : ∑ i,KSRankOne.atom (v i)=1) (s : CubeState N (rho N)) :
    reserve v s≤beta v := by
  have hn : (0:ℝ)<N := Nat.cast_pos.mpr (Input.labels_pos v hd hp)
  have hsum : (∑ i,‖KSRankOne.atom (v i)‖)≤(N:ℝ)*Input.epsilon v := by
    have hh := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => Input.atom_norm_le_epsilon v i)
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using hh
  have he : Input.epsilon v≤Input.delta v := by
    have hs := Input.delta_sq v
    have hnonneg := Input.delta_nonneg v
    have hu := Input.delta_le_one v hp
    nlinarith
  calc
    reserve v s≤rho N*∑ i,‖KSRankOne.atom (v i)‖ := reserve_le v s
    _ ≤rho N*((N:ℝ)*Input.epsilon v) :=
      mul_le_mul_of_nonneg_left hsum (rho_pos (Input.labels_pos v hd hp)).le
    _ =Input.epsilon v/(100*(N:ℝ)) := by unfold rho; field_simp
    _ ≤Input.delta v/(100*(N:ℝ)) := div_le_div_of_nonneg_right he (by positivity)
    _ =beta v := rfl

theorem initial_ledger [Nonempty (Fin d)] (v : Fin N → Fin d → ℂ) (hd : 0<d)
    (hp : ∑ i,KSRankOne.atom (v i)=1) :
    account v (Input.theta v) (zeta N) (Walk.initial v hd hp).toCubeState+
      0+beta v*Progress.entropy (Walk.initial v hd hp).coeff≤36*Input.delta v := by
  have hf : potential v (Input.theta v) (zeta N) (Walk.initial v hd hp).toCubeState≤
      34*Input.delta v := by
    have hh := Input.smooth_initial_potential_le v hd hp (zeta_pos (Input.labels_pos v hd hp)).le
    simpa only [potential,debit,StatePotential.signedSum,initial_coeff_zero,
      Pi.zero_apply,zero_smul,Finset.sum_const_zero,SourceTransport.smoothWeights] using hh
  have hr := reserve_le_beta v hd hp (Walk.initial v hd hp).toCubeState
  have hb : beta v≤Input.delta v := by
    have hn : (1:ℝ)≤N := by exact_mod_cast Input.labels_pos v hd hp
    exact div_le_self (Input.delta_nonneg v) (by nlinarith)
  have he := beta_entropy_bound v hd hp (Walk.initial v hd hp).coeff
    (coeff_abs_le (Walk.initial v hd hp).toCubeState)
  unfold account
  linarith

section Movements
variable [Nonempty (Fin d)]

theorem rawStep_some (O : KSConvexValueOracle.Solver)
    (v : Fin N → Fin d → ℂ) (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1)
    (s : WalkState N) (hs : ¬Walk.terminal s) (i : Fin N)
    (hi : chosenLabel O v s=some i) (b : Bool) :
    rawStep O v hd hp s hs b = outwardMove (rho_pos (Input.labels_pos v hd hp)) s i
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
    (hi : chosenLabel O v s=none) (b : Bool) :
    rawStep O v hd hp s hs b = symmetricMove (rho_pos (Input.labels_pos v hd hp))
      (zeta_pos (Input.labels_pos v hd hp)).le s (direction O v s hs)
      (direction_norm O v s hs) (signedStep v b) (signedStep_bound v hd hp b) := by
  unfold rawStep
  split
  · rename_i j hj
    rw [hi] at hj
    contradiction
  · rfl

theorem rawStep_preserves_frozen (O : KSConvexValueOracle.Solver)
    (v : Fin N → Fin d → ℂ) (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1)
    (s : WalkState N) (hs : ¬Walk.terminal s) (b : Bool)
    (i : Fin N) (hi : |s.coeff i|=1) : (rawStep O v hd hp s hs b).coeff i=s.coeff i := by
  unfold rawStep
  split
  · rename_i j hj
    exact outward_preserves_frozen s j (OutwardSelection.selected_live O v _ _ _ _ s j hj) _ i hi
  · exact symmetric_preserves_frozen _ s _ _ i hi

theorem rawStep_reserve_nonincreasing (O : KSConvexValueOracle.Solver)
    (v : Fin N → Fin d → ℂ) (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1)
    (s : WalkState N) (hs : ¬Walk.terminal s) (b : Bool) :
    reserve v (rawStep O v hd hp s hs b)≤reserve v s.toCubeState :=
  reserve_mono v s.toCubeState (rawStep O v hd hp s hs b)
    (rawStep_preserves_frozen O v hd hp s hs b)

theorem rawStep_displacement (O : KSConvexValueOracle.Solver)
    (v : Fin N → Fin d → ℂ) (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1)
    (s : WalkState N) (hs : ¬Walk.terminal s) (b : Bool) (i : Fin N) :
    |(rawStep O v hd hp s hs b).coeff i-s.coeff i|≤rho N/8 := by
  unfold rawStep
  split
  · apply (outward_displacement (outwardStep_pos (Input.labels_pos v hd hp)).le s.coeff _ i).trans
    unfold outwardStep
    have hr := rho_pos (Input.labels_pos v hd hp)
    linarith
  · exact symmetric_displacement (zeta_pos (Input.labels_pos v hd hp)).le s _
      (direction_norm O v s hs) _ (signedStep_bound v hd hp b) i

theorem rawStep_entropy (O : KSConvexValueOracle.Solver)
    (v : Fin N → Fin d → ℂ) (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1)
    (s : WalkState N) (hs : ¬Walk.terminal s) :
    (Progress.entropy (rawStep O v hd hp s hs false).coeff+
      Progress.entropy (rawStep O v hd hp s hs true).coeff)/2≤
      Progress.entropy s.coeff-movementStep v^2 := by
  have hr := rho_pos (Input.labels_pos v hd hp)
  have ha := outwardStep_pos (Input.labels_pos v hd hp)
  have hh := movementStep_pos v hd hp
  have hha : movementStep v^2≤outwardStep N^2 :=
    pow_le_pow_left₀ hh.le (movementStep_le_outwardStep v) 2
  cases hi : chosenLabel O v s with
  | some i =>
    have he := outward_entropy hr s i (OutwardSelection.selected_live O v _ _ _ _ s i hi)
      (outwardStep N) ha.le (by unfold outwardStep; linarith)
    rw [rawStep_some O v hd hp s hs i hi false, rawStep_some O v hd hp s hs i hi true]
    linarith
  | none =>
    have he := symmetric_entropy hr (zeta_pos (Input.labels_pos v hd hp)).le s
      (direction O v s hs) (direction_norm O v s hs) (direction_frozen O v s hs)
      (movementStep v) (by simpa only [abs_of_pos hh] using movementStep_le_outwardStep v)
    rw [rawStep_none O v hd hp s hs hi false, rawStep_none O v hd hp s hs hi true]
    simp only [signedStep,Bool.false_eq_true,↓reduceIte]
    convert he using 1
    ring

theorem step_preserves_frozen (O : KSConvexValueOracle.Solver)
    (v : Fin N → Fin d → ℂ) (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1)
    (s : WalkState N) (b : Bool) (i : Fin N) (hi : |s.coeff i|=1) :
    (Walk.step O v hd hp s b).coeff i=s.coeff i := by
  by_cases hs : Walk.terminal s
  · rw [Walk.step_terminal O v hd hp s hs b]
  · simp only [Walk.step,dif_neg hs]
    rw [prepare_preserves_frozen _ _ i (by rw [rawStep_preserves_frozen O v hd hp s hs b i hi]; exact hi),
      rawStep_preserves_frozen O v hd hp s hs b i hi]

theorem step_entropy (O : KSConvexValueOracle.Solver)
    (v : Fin N → Fin d → ℂ) (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1)
    (s : WalkState N) (hs : ¬Walk.terminal s) :
    (Progress.entropy (Walk.step O v hd hp s false).coeff+
      Progress.entropy (Walk.step O v hd hp s true).coeff)/2≤
      Progress.entropy s.coeff-movementStep v^2 := by
  have hfalse := prepare_entropy (rho_pos (Input.labels_pos v hd hp)).le
    (rawStep O v hd hp s hs false)
  have htrue := prepare_entropy (rho_pos (Input.labels_pos v hd hp)).le
    (rawStep O v hd hp s hs true)
  have hraw := rawStep_entropy O v hd hp s hs
  simp only [Walk.step,dif_neg hs]
  linarith

end Movements
end SeamlessKS.WalkGeometry
