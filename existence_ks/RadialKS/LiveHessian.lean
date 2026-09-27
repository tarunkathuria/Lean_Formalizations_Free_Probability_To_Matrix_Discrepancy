import SeamlessKS.LiveHessian
import RadialKS.ActualHessian
open Matrix Filter Topology Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
noncomputable section
set_option maxHeartbeats 2000000
namespace RadialKS.LiveHessian
open MatrixSpencer SeamlessKS.State SeamlessKS.StatePotential SeamlessKS.LivePotential
open MatrixSpencer.KSLiveEnumeration (count liveEquiv)
open MatrixSpencer.KSFullManuscriptLiveCoordinates (face)
variable {N : ℕ} {ρ : ℝ} {n : Type*} [Fintype n] [DecidableEq n]
local instance {k : Type*} [Fintype k] [DecidableEq k] : CStarAlgebra (Matrix k k ℂ) := {}

open SeamlessKS.LiveHessian
theorem exists_negative_face_curve [Nonempty n]
    (v : Fin N → n → ℂ) (s : PreparedState N ρ) (hm : 0<count s.coeff)
    (hB : (debit v s.toCubeState).PosSemidef)
    {θ ζ a : ℝ} (hθ : 0<θ) (hζ : 0<ζ) (ha : 0<a) (hscale : ζ≤a/10)
    (har : a≤ρ)
    (hinc : ∀ i : Fin (count s.coeff), potential v θ ζ s.toCubeState <
      faceValue v θ ζ s.toCubeState
        (EuclideanSpace.single i (a*outwardSign (livePositions s.coeff i)))) :
    ∃ h : EuclideanSpace ℝ (Fin (count s.coeff)), h≠0 ∧ livePositions s.coeff ⬝ᵥ WithLp.ofLp h = 0 ∧
      deriv (fun t : ℝ => faceValue v θ ζ s.toCubeState (t • h)) 0=0 ∧
      iteratedDeriv 2 (fun t : ℝ => faceValue v θ ζ s.toCubeState (t • h)) 0<0 := by
  letI : Nonempty (Fin (count s.coeff)) := ⟨⟨0,hm⟩⟩
  obtain ⟨h,hh,horth,hfirst,hsecond⟩ := RadialKS.ActualHessian.exists_negative_second_debit_curve_actual
    (SeamlessKS.StatePotential.signedSum v s.coeff) (debit v s.toCubeState)
    (signedSum_isHermitian v s.coeff) hB (liveVectors v s.coeff)
    (live_nonzero_of_increases v s.toCubeState θ ζ a hinc)
    (livePositions s.coeff) (livePositions s.coeff) (livePositions_interior s.coeff) hθ hζ ha hscale
    (secants_fail_of_increases v s hθ hζ ha hscale har hinc)
  let hE : EuclideanSpace ℝ (Fin (count s.coeff)) := WithLp.toLp 2 h
  have hEne : hE≠0 := by
    intro he
    apply hh
    exact congrArg WithLp.ofLp he
  have heq : (fun t : ℝ => faceValue v θ ζ s.toCubeState (t • hE))=
      SeamlessKS.SmoothPotential.curvePotential (center v s.toCubeState) (liveVectors v s.coeff)
        θ ζ (livePositions s.coeff) h := by
    funext t
    rw [faceValue_eq_restricted,restrictedValue_curve]
    rfl
  refine ⟨hE,hEne,horth,?_,?_⟩ <;> rw [heq]
  · exact hfirst
  · exact hsecond

/-- A Euclidean unit direction orthogonal to the actual coefficient vector,
with negative raw Hessian Rayleigh quotient. -/
theorem exists_unit_raw_negative [Nonempty n]
    (v : Fin N → n → ℂ) (s : PreparedState N ρ) (hm : 0<count s.coeff)
    (hB : (debit v s.toCubeState).PosSemidef)
    {θ ζ a : ℝ} (hθ : 0<θ) (hζ : 0<ζ) (ha : 0<a) (hscale : ζ≤a/10)
    (har : a≤ρ)
    (hinc : ∀ i : Fin (count s.coeff), potential v θ ζ s.toCubeState <
      faceValue v θ ζ s.toCubeState
        (EuclideanSpace.single i (a*outwardSign (livePositions s.coeff i)))) :
    ∃ g : EuclideanSpace ℝ (Fin (count s.coeff)), ‖g‖=1 ∧
      livePositions s.coeff ⬝ᵥ WithLp.ofLp g = 0 ∧
      KSRayleighAccuracy.realRayleigh
        (KSNumericalHessian.hessian (faceValue v θ ζ s.toCubeState) 0) g < 0 := by
  obtain ⟨h, hh, ho, _, hn⟩ := exists_negative_face_curve v s hm hB hθ hζ ha hscale har hinc
  have hp : 0 < ‖h‖ := norm_pos_iff.mpr hh
  have hi : 0 < ‖h‖⁻¹ := inv_pos.mpr hp
  let g := ‖h‖⁻¹ • h
  have hg : ‖g‖=1 := by
    rw [show g = ‖h‖⁻¹ • h from rfl, norm_smul, Real.norm_eq_abs,
      abs_of_pos hi, inv_mul_cancel₀ hp.ne']
  refine ⟨g,hg,?_,?_⟩
  · change livePositions s.coeff ⬝ᵥ (‖h‖⁻¹ • WithLp.ofLp h) = 0
    rw [dotProduct_smul, ho, smul_zero]
  · have hf : ContDiffAt ℝ 2 (faceValue v θ ζ s.toCubeState) 0 :=
      (contDiffAt_faceValue v s.toCubeState hB hθ hζ).of_le
        (WithTop.coe_le_coe.mpr (show (2 : ℕ∞)≤⊤ from le_top))
    have hn' : iteratedDeriv 2
        (fun t : ℝ => faceValue v θ ζ s.toCubeState (0 + t • h)) 0 < 0 := by
      simpa only [zero_add] using hn
    rw [KSFourthDifference.line_second _ _ _ hf] at hn'
    rw [KSNumericalHessian.hessian_rayleigh]
    change fderiv ℝ (fderiv ℝ (faceValue v θ ζ s.toCubeState)) 0
      (‖h‖⁻¹ • h) (‖h‖⁻¹ • h) < 0
    simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    exact mul_neg_of_pos_of_neg hi (mul_neg_of_pos_of_neg hi hn')

/-- The radial alternative follows from the actual numerical outward tests. -/
theorem exists_unit_raw_negative_of_none {d : ℕ} [Nonempty (Fin d)]
    (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ) (s : PreparedState N ρ)
    (hm : 0<count s.coeff) (hB : (debit v s.toCubeState).PosSemidef)
    {θ ζ ν a : ℝ} (hθ : 0<θ) (hν : 0<ν) (hρ : 0<ρ)
    (hζ : 0<ζ) (ha : 0<a) (hscale : ζ≤a/10) (har : a≤ρ/8)
    (hn : SeamlessKS.OutwardSelection.select O v θ ζ ν a s=none) :
    ∃ g : EuclideanSpace ℝ (Fin (count s.coeff)), ‖g‖=1 ∧
      livePositions s.coeff ⬝ᵥ WithLp.ofLp g = 0 ∧
      KSRayleighAccuracy.realRayleigh
        (KSNumericalHessian.hessian (faceValue v θ ζ s.toCubeState) 0) g < 0 := by
  apply exists_unit_raw_negative v s hm hB hθ hζ ha hscale (by linarith)
  intro i
  rw [face_outward_eq]
  exact SeamlessKS.OutwardSelection.none_true_increase O v hθ hν hρ ha.le har s hn
    (liveEquiv s.coeff i) (liveEquiv s.coeff i).property

end RadialKS.LiveHessian
