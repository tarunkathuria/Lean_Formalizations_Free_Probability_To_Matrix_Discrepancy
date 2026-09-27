import SeamlessKS.LivePotential
import SeamlessKS.ActualHessian
import SeamlessKS.OutwardSelection

/-! Rejected actual outward tests force negative curvature on the actual live
face. In particular, zero vector labels cannot enter this branch. -/
open Matrix Filter Topology Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
noncomputable section
set_option maxHeartbeats 2000000
namespace SeamlessKS.LiveHessian
open MatrixSpencer SeamlessKS.State SeamlessKS.StatePotential SeamlessKS.LivePotential
open MatrixSpencer.KSLiveEnumeration (count liveEquiv)
open MatrixSpencer.KSFullManuscriptLiveCoordinates (face)
variable {N : ℕ} {ρ : ℝ} {n : Type*} [Fintype n] [DecidableEq n]
local instance {k : Type*} [Fintype k] [DecidableEq k] : CStarAlgebra (Matrix k k ℂ) := {}

def outwardSign (x : ℝ) : ℝ := if 0≤x then 1 else -1

theorem outwardSign_abs (x : ℝ) : |outwardSign x|=1 := by
  unfold outwardSign
  split_ifs <;> norm_num

theorem outwardSign_mul (x : ℝ) : outwardSign x*x=|x| := by
  unfold outwardSign
  split_ifs with h
  · simp [abs_of_nonneg h]
  · simp [abs_of_neg (lt_of_not_ge h)]

theorem outwardSign_step (x a : ℝ) : x+a*outwardSign x=Progress.outward x a := by
  unfold outwardSign Progress.outward
  split_ifs <;> ring

theorem zero_atom_source_update {k : ℕ} (v : Fin k → n → ℂ)
    (c : Fin k → ℝ) (i : Fin k) (hi : v i=0) (d : ℝ)
    (X : Matrix (n ⊕ n) (n ⊕ n) ℂ) :
    covarianceSource (KSSpinSource.family (fun j => KSRankOne.atom (v j)))
      (KSSpinSource.coefficientCovariance (Function.update c i d)) X =
    covarianceSource (KSSpinSource.family (fun j => KSRankOne.atom (v j)))
      (KSSpinSource.coefficientCovariance c) X := by
  rw [KSSpinSource.source_eq_tracePrepare v _ X,KSSpinSource.source_eq_tracePrepare v _ X]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j=i
  · subst j
    simp [hi,KSSpinSource.doubled]
  · rw [Function.update_of_ne hj]

theorem zero_atom_restrictedValue {k : ℕ} (M : Matrix (n ⊕ n) (n ⊕ n) ℂ)
    (v : Fin k → n → ℂ) (x : Fin k → ℝ) (θ ζ : ℝ)
    (i : Fin k) (hi : v i=0) (t : ℝ) :
    restrictedValue M v x θ ζ (EuclideanSpace.single i t)=restrictedValue M v x θ ζ 0 := by
  rw [restrictedValue_single,LocalComparison.smoothWeights_update]
  have hM : M+t • signedLift (KSRankOne.atom (v i))=M := by
    rw [hi,KSRankOne.atom_zero]
    simp only [signedLift,neg_zero,Matrix.fromBlocks_zero,smul_zero,add_zero]
  rw [hM]
  simp only [restrictedValue,PiLp.zero_apply,zero_smul,Finset.sum_const_zero,add_zero]
  unfold ownerPotential
  congr 2
  funext X
  unfold ownerObjective
  rw [zero_atom_source_update v _ i hi]

theorem face_outward_eq (v : Fin N → n → ℂ) (s : CubeState N ρ)
    (θ ζ a : ℝ) (i : Fin (count s.coeff)) :
    faceValue v θ ζ s (EuclideanSpace.single i (a*outwardSign (livePositions s.coeff i))) =
    KSDebitPotential.potential
      (StatePotential.signedSum v (Proposals.outwardVector s.coeff (liveEquiv s.coeff i) a))
      (debit v s) v
      (SourceTransport.smoothWeights ζ (Proposals.outwardVector s.coeff (liveEquiv s.coeff i) a)) θ := by
  have he : face s.coeff (EuclideanSpace.single i (a*outwardSign (livePositions s.coeff i))) =
      Proposals.outwardVector s.coeff (liveEquiv s.coeff i) a := by
    rw [face_single]
    unfold Proposals.outwardVector livePositions
    rw [outwardSign_step]
  unfold faceValue
  rw [he]

theorem live_nonzero_of_increases (v : Fin N → n → ℂ) (s : CubeState N ρ)
    (θ ζ a : ℝ)
    (hinc : ∀ i : Fin (count s.coeff), potential v θ ζ s <
      faceValue v θ ζ s (EuclideanSpace.single i (a*outwardSign (livePositions s.coeff i)))) :
    ∀ i, liveVectors v s.coeff i≠0 := by
  intro i hi
  have hh := hinc i
  rw [← faceValue_zero v θ ζ s,faceValue_eq_restricted,faceValue_eq_restricted,
    zero_atom_restrictedValue _ _ _ _ _ i hi] at hh
  exact lt_irrefl _ hh

theorem secants_fail_of_increases [Nonempty n]
    (v : Fin N → n → ℂ) (s : PreparedState N ρ)
    {θ ζ a : ℝ} (hθ : 0<θ) (hζ : 0<ζ) (ha : 0<a) (hscale : ζ≤a/10)
    (har : a≤ρ)
    (hinc : ∀ i : Fin (count s.coeff), potential v θ ζ s.toCubeState <
      faceValue v θ ζ s.toCubeState
        (EuclideanSpace.single i (a*outwardSign (livePositions s.coeff i)))) :
    ∀ i, Source.secant 64 ζ |livePositions s.coeff i| a * realTrace
      (SourceTransport.stateTransport (liveVectors v s.coeff)
        (SourceTransport.smoothWeights ζ (livePositions s.coeff))
        (ActualHessian.actualOptimizer (center v s.toCubeState) (liveVectors v s.coeff)
          θ ζ (livePositions s.coeff)) *
        KSSpinCompression.compressedAtom (KSSpinLocalState.atoms (liveVectors v s.coeff)) i)≤1 := by
  intro i
  by_contra hfail
  have hmargin : |livePositions s.coeff i|+a≤1 := by
    have hh := s.margin (liveEquiv s.coeff i) (liveEquiv s.coeff i).property
    change |s.coeff (liveEquiv s.coeff i)|+a≤1
    linarith
  have hc := LocalComparison.smooth_outward_position (center v s.toCubeState)
    (liveVectors v s.coeff) (livePositions s.coeff) (livePositions_interior s.coeff)
    hζ ha hscale hθ i hmargin (outwardSign (livePositions s.coeff i))
    (outwardSign_abs _) (outwardSign_mul _) (le_of_lt (lt_of_not_ge hfail))
  have hh := hinc i
  rw [← faceValue_zero v θ ζ s.toCubeState,faceValue_eq_restricted,faceValue_eq_restricted,
    restrictedValue_single,restrictedValue_zero] at hh
  exact not_lt_of_ge hc hh

theorem exists_negative_face_curve [Nonempty n]
    (v : Fin N → n → ℂ) (s : PreparedState N ρ) (hm : 0<count s.coeff)
    (hB : (debit v s.toCubeState).PosSemidef)
    {θ ζ a : ℝ} (hθ : 0<θ) (hζ : 0<ζ) (ha : 0<a) (hscale : ζ≤a/10)
    (har : a≤ρ)
    (hinc : ∀ i : Fin (count s.coeff), potential v θ ζ s.toCubeState <
      faceValue v θ ζ s.toCubeState
        (EuclideanSpace.single i (a*outwardSign (livePositions s.coeff i)))) :
    ∃ h : EuclideanSpace ℝ (Fin (count s.coeff)), h≠0 ∧
      deriv (fun t : ℝ => faceValue v θ ζ s.toCubeState (t • h)) 0=0 ∧
      iteratedDeriv 2 (fun t : ℝ => faceValue v θ ζ s.toCubeState (t • h)) 0<0 := by
  letI : Nonempty (Fin (count s.coeff)) := ⟨⟨0,hm⟩⟩
  obtain ⟨h,hh,hfirst,hsecond⟩ := ActualHessian.exists_negative_second_debit_curve_actual
    (StatePotential.signedSum v s.coeff) (debit v s.toCubeState)
    (signedSum_isHermitian v s.coeff) hB (liveVectors v s.coeff)
    (live_nonzero_of_increases v s.toCubeState θ ζ a hinc)
    (livePositions s.coeff) (livePositions_interior s.coeff) hθ hζ ha hscale
    (secants_fail_of_increases v s hθ hζ ha hscale har hinc)
  let hE : EuclideanSpace ℝ (Fin (count s.coeff)) := WithLp.toLp 2 h
  have hEne : hE≠0 := by
    intro he
    apply hh
    exact congrArg WithLp.ofLp he
  have heq : (fun t : ℝ => faceValue v θ ζ s.toCubeState (t • hE))=
      SmoothPotential.curvePotential (center v s.toCubeState) (liveVectors v s.coeff)
        θ ζ (livePositions s.coeff) h := by
    funext t
    rw [faceValue_eq_restricted,restrictedValue_curve]
    rfl
  refine ⟨hE,hEne,?_,?_⟩ <;> rw [heq]
  · exact hfirst
  · exact hsecond

theorem leastRayleigh_neg_of_increases [Nonempty n]
    (v : Fin N → n → ℂ) (s : PreparedState N ρ) (hm : 0<count s.coeff)
    (hB : (debit v s.toCubeState).PosSemidef)
    {θ ζ a : ℝ} (hθ : 0<θ) (hζ : 0<ζ) (ha : 0<a) (hscale : ζ≤a/10)
    (har : a≤ρ)
    (hinc : ∀ i : Fin (count s.coeff), potential v θ ζ s.toCubeState <
      faceValue v θ ζ s.toCubeState
        (EuclideanSpace.single i (a*outwardSign (livePositions s.coeff i)))) :
    KSRayleighAccuracy.leastRayleigh
      (KSFullManuscriptHessian.weighted (NormalizedHessian.sourceWeight ζ (livePositions s.coeff))
        (KSNumericalHessian.hessian (faceValue v θ ζ s.toCubeState) 0))<0 := by
  letI : Nonempty (Fin (count s.coeff)) := ⟨⟨0,hm⟩⟩
  obtain ⟨h,hh,_,hsecond⟩ := exists_negative_face_curve v s hm hB hθ hζ ha hscale har hinc
  apply NormalizedHessian.leastRayleigh_neg_of_curve
    (NormalizedHessian.sourceWeight ζ (livePositions s.coeff))
    (NormalizedHessian.sourceWeight_pos ζ (livePositions s.coeff) (livePositions_interior s.coeff))
    (faceValue v θ ζ s.toCubeState) 0 h
    ((contDiffAt_faceValue v s.toCubeState hB hθ hζ).of_le
      (WithTop.coe_le_coe.mpr (show (2 : ℕ∞)≤⊤ from le_top))) hh
  simpa only [zero_add] using hsecond

/-- The Hessian alternative is obtained from the actual finite SDP-value
tests, rather than provided as a hypothesis to the walk. -/
theorem leastRayleigh_neg_of_none {d : ℕ} [Nonempty (Fin d)]
    (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ) (s : PreparedState N ρ)
    (hm : 0<count s.coeff) (hB : (debit v s.toCubeState).PosSemidef)
    {θ ζ ν a : ℝ} (hθ : 0<θ) (hν : 0<ν) (hρ : 0<ρ)
    (hζ : 0<ζ) (ha : 0<a) (hscale : ζ≤a/10) (har : a≤ρ/8)
    (hn : OutwardSelection.select O v θ ζ ν a s=none) :
    KSRayleighAccuracy.leastRayleigh
      (KSFullManuscriptHessian.weighted (NormalizedHessian.sourceWeight ζ (livePositions s.coeff))
        (KSNumericalHessian.hessian (faceValue v θ ζ s.toCubeState) 0))<0 := by
  apply leastRayleigh_neg_of_increases v s hm hB hθ hζ ha hscale (by linarith)
  intro i
  rw [face_outward_eq]
  exact OutwardSelection.none_true_increase O v hθ hν hρ ha.le har s hn
    (liveEquiv s.coeff i) (liveEquiv s.coeff i).property

end SeamlessKS.LiveHessian
