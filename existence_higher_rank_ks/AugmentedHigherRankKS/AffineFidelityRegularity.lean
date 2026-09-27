import AugmentedHigherRankKS.FidelityRelativeJets
import MatrixSpencer.KSObjectiveValueBound

/-! Actual affine density jets and the root regularizer. -/
open Matrix MatrixSpencer HigherRankKS Filter
open scoped BigOperators Topology ContDiff MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1200000
namespace AugmentedHigherRankKS
open BalancedTransportJets BalancedRegularity
variable {n : Type*} [Fintype n] [DecidableEq n]
local instance affineRegCStar : CStarAlgebra (Matrix n n ℂ) := {}

theorem jet_affine_one (S X : Matrix n n ℂ) :
    jet (fun t : ℝ => S + t • X) 1 = X := by
  rw [jet_one]
  simpa using (((hasDerivAt_id (0 : ℝ)).smul_const X).const_add S).deriv

theorem jet_affine_two (S X : Matrix n n ℂ) :
    jet (fun t : ℝ => S + t • X) 2 = 0 := by
  have hd : deriv (fun t : ℝ => S + t • X) = fun _ => X := by
    funext t
    simpa using (((hasDerivAt_id t).smul_const X).const_add S).deriv
  simp [jet_two, hd]

theorem jet_affine_three (S X : Matrix n n ℂ) :
    jet (fun t : ℝ => S + t • X) 3 = 0 := by
  have hd : deriv (fun t : ℝ => S + t • X) = fun _ => X := by
    funext t
    simpa using (((hasDerivAt_id t).smul_const X).const_add S).deriv
  simp [jet_three, hd]

theorem jet_const {j : ℕ} (hj : 1 ≤ j) (S : Matrix n n ℂ) :
    jet (fun _ : ℝ => S) j = 0 := by
  have hz (k : ℕ) : iteratedDeriv k (fun _ : ℝ => (0 : Matrix n n ℂ)) = fun _ => 0 := by
    induction k with
    | zero => rfl
    | succ k hk =>
      rw [iteratedDeriv_succ, hk]
      funext t
      exact deriv_const t 0
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  have hdc : deriv (fun _ : ℝ => S) = fun _ => 0 := funext (fun t => deriv_const t S)
  simp only [jet, iteratedDeriv_succ', hdc, hz, smul_zero]

theorem jet_affine_order {S X : Matrix n n ℂ} (hS : S.PosSemidef) {b : ℝ}
    (hb : 0 ≤ b) (hlo : -b • S ≤ X) (hhi : X ≤ b • S) :
    ∀ j : ℕ, 1 ≤ j → j ≤ 3 →
      -(b^j) • S ≤ jet (fun t : ℝ => S + t • X) j ∧
      jet (fun t : ℝ => S + t • X) j ≤ b^j • S := by
  intro j hj1 hj3
  interval_cases j
  · rw [jet_affine_one, pow_one]
    exact ⟨hlo, hhi⟩
  all_goals
    simp only [jet_affine_two, jet_affine_three]
    constructor
    · simpa only [neg_smul] using neg_nonpos.mpr (hS.smul (pow_nonneg hb _)).nonneg
    · exact (hS.smul (pow_nonneg hb _)).nonneg

theorem fidelity_identity_right {S : Matrix n n ℂ} (hS : S.PosSemidef) :
    fidelity S 1 = realTrace (CFC.sqrt S) := by
  simp only [fidelity, fidelityCore, Matrix.mul_one,
    CFC.sqrt_mul_sqrt_self S hS.nonneg]

/-- The trace root uses the same faithful fidelity bound with constant second input. -/
theorem root_affine_scalarJet_le
    (S X : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef)
    (ht : realTrace (S : Matrix n n ℂ) = 1)
    {d b : ℝ} (hd : 1 ≤ d) (hdn : Real.sqrt (Fintype.card n : ℝ) ≤ d)
    (hb : 0 ≤ b) (hlo : -b • (S : Matrix n n ℂ) ≤ X)
    (hhi : (X : Matrix n n ℂ) ≤ b • (S : Matrix n n ℂ)) :
    ∀ j : ℕ, 1 ≤ j → j ≤ 3 →
      |scalarJet (fun t : ℝ => 2*realTrace (CFC.sqrt (S + t • X : Matrix n n ℂ))) j| ≤
        2*Real.sqrt (Fintype.card n : ℝ)*(100*d*b)^j := by
  let A : ℝ → selfAdjoint (Matrix n n ℂ) := fun t => S + t • X
  let B : ℝ → selfAdjoint (Matrix n n ℂ) := fun _ => ⟨1, Matrix.isHermitian_one⟩
  have hA : ContDiffAt ℝ 3 A 0 := contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const)
  have hB : ContDiffAt ℝ 3 B 0 := contDiffAt_const
  have hAP : (A 0 : Matrix n n ℂ).PosDef := by simpa [A] using hS
  have hBP : (B 0 : Matrix n n ℂ).PosDef := Matrix.PosDef.one
  have hbd : ∀ j : ℕ, 1 ≤ j → j ≤ 3 →
      -(b^j) • (B 0 : Matrix n n ℂ) ≤ jet (fun t => (B t : Matrix n n ℂ)) j ∧
      jet (fun t => (B t : Matrix n n ℂ)) j ≤ b^j • (B 0 : Matrix n n ℂ) := by
    intro j hj hj3
    rw [jet_const hj]
    constructor
    · simpa only [neg_smul] using neg_nonpos.mpr
        (Matrix.PosSemidef.one.smul (pow_nonneg hb j)).nonneg
    · exact (Matrix.PosSemidef.one.smul (pow_nonneg hb j)).nonneg
  have hh := fidelity_jet_le_of_order hA hB hAP hBP hd hdn hb
    (by simpa [A] using jet_affine_order hS.posSemidef hb hlo hhi) hbd
  have he : (fun t : ℝ => 2*fidelity (A t : Matrix n n ℂ) (B t : Matrix n n ℂ)) =ᶠ[𝓝 0]
      (fun t : ℝ => 2*realTrace (CFC.sqrt (S + t • X : Matrix n n ℂ))) := by
    filter_upwards [hA.continuousAt.eventually (eventually_posDef_of_posDef (A 0) hAP)] with t hat
    exact congrArg (fun z : ℝ => 2*z) (fidelity_identity_right hat.posSemidef)
  have hval : fidelity (A 0 : Matrix n n ℂ) (B 0 : Matrix n n ℂ) ≤
      Real.sqrt (Fintype.card n : ℝ) := by
    have htr : realTrace (1 : Matrix n n ℂ) = Fintype.card n := by
      simp [realTrace, Matrix.trace, Matrix.diag]
    simpa only [A, B, zero_smul, add_zero, ht, htr, one_mul] using
      fidelity_le_sqrt_trace_mul hS.posSemidef
        (Matrix.PosSemidef.one : (1 : Matrix n n ℂ).PosSemidef)
  intro j hj1 hj3
  have hj := hh j hj1 hj3
  rw [scalarJet, he.iteratedDeriv_eq j] at hj
  exact hj.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hval (by norm_num))
    (pow_nonneg (by positivity) j))

theorem scalarJet_add {f g : ℝ → ℝ}
    (hf : ContDiffAt ℝ 3 f 0) (hg : ContDiffAt ℝ 3 g 0)
    {j : ℕ} (hj : (j : WithTop ℕ∞) ≤ 3) :
    scalarJet (fun t => f t + g t) j = scalarJet f j + scalarJet g j := by
  have hh := iteratedDeriv_add (hf.of_le hj) (hg.of_le hj)
  change iteratedDeriv j (fun t => f t + g t) 0 = _ at hh
  simp only [scalarJet, hh]
  ring

theorem scalarJet_const_mul {f : ℝ → ℝ}
    (hf : ContDiffAt ℝ 3 f 0) {j : ℕ} (hj : (j : WithTop ℕ∞) ≤ 3) (a : ℝ) :
    scalarJet (fun t => a * f t) j = a * scalarJet f j := by
  rw [scalarJet, iteratedDeriv_const_mul (hf.of_le hj) a, scalarJet]
  ring

theorem scalarJet_realTrace {F : ℝ → Matrix n n ℂ}
    (hF : ContDiffAt ℝ 3 F 0) {j : ℕ} (hj : (j : WithTop ℕ∞) ≤ 3) :
    scalarJet (fun t => realTrace (F t)) j = realTrace (jet F j) := by
  have hh := iteratedDeriv_clm (realTraceCLM (n := n)) hF hj
  change iteratedDeriv j (fun t => realTrace (F t)) 0 = realTrace (iteratedDeriv j F 0) at hh
  rw [scalarJet, hh, jet, realTrace_smul]

theorem affine_center_scalarJet_two (H K S X : Matrix n n ℂ) :
    scalarJet (fun t : ℝ => realTrace ((H+t•K)*(S+t•X))) 2 = realTrace (K*X) := by
  have h1 : ContDiffAt ℝ 3 (fun t : ℝ => H+t•K) 0 :=
    contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const)
  have h2 : ContDiffAt ℝ 3 (fun t : ℝ => S+t•X) 0 :=
    contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const)
  rw [scalarJet_realTrace (h1.mul h2) (by norm_num), jet_mul_two h1 h2,
    jet_affine_two, jet_affine_two, jet_affine_one, jet_affine_one]
  simp

theorem affine_center_scalarJet_three (H K S X : Matrix n n ℂ) :
    scalarJet (fun t : ℝ => realTrace ((H+t•K)*(S+t•X))) 3 = 0 := by
  have h1 : ContDiffAt ℝ 3 (fun t : ℝ => H+t•K) 0 :=
    contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const)
  have h2 : ContDiffAt ℝ 3 (fun t : ℝ => S+t•X) 0 :=
    contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const)
  rw [scalarJet_realTrace (h1.mul h2) (by norm_num), jet_mul_three h1 h2,
    jet_affine_three, jet_affine_three, jet_affine_two, jet_affine_two]
  simp

end AugmentedHigherRankKS
