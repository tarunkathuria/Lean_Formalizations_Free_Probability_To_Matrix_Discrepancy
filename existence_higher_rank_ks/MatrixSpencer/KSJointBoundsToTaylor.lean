import MatrixSpencer.KSDebitNumericalDrift
import MatrixSpencer.KSActualEnvelope
import MatrixSpencer.KSTaylorBudget

/-!
# Actual joint derivative caps imply the controller's Taylor bounds

The certificate below contains only second, third and fourth derivative norm
caps for the actual joint density objective. Smoothness, fixed debit and
frozen labels, the exact normalized query paths, and the outer fourth bound
are proved here. The joint caps themselves remain an explicit analytic input.
-/

open Matrix Set Filter
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff Topology
noncomputable section
namespace MatrixSpencer.KSJointBoundsToTaylor

open KSLiveCurve KSWeightedLiveCoordinates KSDebitPreparedMargin KSActualEnvelope
open KSDebitHessianQueries KSDebitNumericalDrift KSControllerParameters
variable {N d : ℕ} [Nonempty (Fin d)]
local instance {k : Type*} [Fintype k] [DecidableEq k] : CStarAlgebra (Matrix k k ℂ) := {}

omit [Nonempty (Fin d)] in
/-- Hermitian symmetry uses only real debit coefficients. -/
theorem stateCenter_isHermitian (v : Fin N → Fin d → ℂ) (δ η : ℝ) (x : Fin N → ℝ) :
    (stateCenter v δ η x).IsHermitian := by
  apply KSDebitCenter.center_isHermitian
  · exact KSPotentialModels.center_isHermitian _ (fun i => KSRankOne.atom_isHermitian (v i)) x
  · change (KSDebitBudget.debit _ δ η x)ᴴ = _
    simp [KSDebitBudget.debit, Matrix.conjTranspose_sum,
      fun i => (KSRankOne.atom_isHermitian (v i)).eq]

/-- Only actual joint derivative norms are assumed, on the controller's radius. -/
structure JointBounds (v : Fin N → Fin d → ℂ) (δ η θ B : ℝ) (hd : 0 < d) : Prop where
  bounds : ∀ (s : Prepared v δ η θ hd), ¬KSDebitWalkRun.terminal s →
    ∀ (h : Live 1 s.coeff → ℝ), (∀ i, |h i| ≤ 2) →
    ∀ t : ℝ, |t| ≤ δ / 16 →
      let F := curveObjective (stateCenter v δ η s.coeff)
        (stateCenter_isHermitian v δ η s.coeff) (fun i : Live 1 s.coeff => v i)
        θ (fun i => s.coeff i) h
      let b := curveBranch (stateCenter v δ η s.coeff)
        (stateCenter_isHermitian v δ η s.coeff) (fun i : Live 1 s.coeff => v i)
        θ (fun i => s.coeff i) h t
      secondNorm F (t,b) ≤ B ∧ thirdNorm F (t,b) ≤ B ∧ fourthNorm F (t,b) ≤ B

/-- The actual physical coefficient direction corresponding to normalized coordinates. -/
def coefficientDirection (x : Fin N → ℝ)
    (w : EuclideanSpace ℝ (Fin (KSLiveEnumeration.count x))) : Live 1 x → ℝ :=
  fun i => weightedMap x w i

theorem coefficientDirection_le_two (x : Fin N → ℝ)
    (w : EuclideanSpace ℝ (Fin (KSLiveEnumeration.count x))) (hw : ‖w‖ ≤ 2)
    (i : Live 1 x) : |coefficientDirection x w i| ≤ 2 := by
  have hi := PiLp.norm_apply_le (weightedMap x w) i.val
  rw [Real.norm_eq_abs] at hi
  exact hi.trans ((weightedMap_norm x w).trans hw)

theorem weightedMap_eq_extend (x : Fin N → ℝ)
    (w : EuclideanSpace ℝ (Fin (KSLiveEnumeration.count x))) (i : Fin N) :
    weightedMap x w i = KSLiveCurve.extend 1 x (coefficientDirection x w) i := by
  by_cases hi : |x i| < 1
  · exact (KSLiveCurve.extend_live 1 x (coefficientDirection x w) ⟨i,hi⟩).symm
  · rw [weightedMap_apply, KSLiveEnumeration.extend_dead x w i hi,
      KSLiveCurve.extend_dead 1 x _ i hi, mul_zero]

theorem face_smul_eq_path (x : Fin N → ℝ)
    (w : EuclideanSpace ℝ (Fin (KSLiveEnumeration.count x))) (t : ℝ) :
    face x (t • w) = path 1 x (coefficientDirection x w) t := by
  funext i
  rw [face, map_smul]
  change x i + t * weightedMap x w i = _
  rw [weightedMap_eq_extend]
  rfl

theorem radius_mem_curveDomain {δ t : ℝ} (hδ : 0 < δ) (ht : |t| ≤ δ / 16) :
    t ∈ curveDomain δ 2 := by
  change - (δ * 1 / (4 * (2 + 1))) < t ∧ t < δ * 1 / (4 * (2 + 1))
  have hh := abs_le.mp ht
  constructor <;> nlinarith

/-- No coordinate reaches an endpoint anywhere in the larger analytic interval. -/
theorem path_live_on_domain {δ : ℝ} (hδ : 0 < δ) (x : Fin N → ℝ)
    (h : Live 1 x → ℝ) (hmargin : ∀ i : Live 1 x, δ ≤ 1 - |x i|)
    (hdir : ∀ i, |h i| ≤ 2) {t : ℝ} (ht : t ∈ curveDomain δ 2)
    (i : Live 1 x) : |path 1 x h t i| < 1 := by
  have he := KSOwnerRelativeSource.displacement_le_of_radius hδ.le
    (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 2) (hdir i) (abs_lt.mpr ht).le
  rw [path_live]
  have hh := abs_add_le (x i) (t * h i)
  simp only [mul_one] at he
  linarith [hmargin i]

theorem path_same_frozen_on_domain {δ : ℝ} (hδ : 0 < δ) (x : Fin N → ℝ)
    (h : Live 1 x → ℝ) (hmargin : ∀ i : Live 1 x, δ ≤ 1 - |x i|)
    (hdir : ∀ i, |h i| ≤ 2) {t : ℝ} (ht : t ∈ curveDomain δ 2) :
    ksFrozen 1 (path 1 x h t) = ksFrozen 1 x := by
  ext i
  simp only [ksFrozen, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hi : |x i| < 1
  · exact iff_of_false (ne_of_lt (path_live_on_domain hδ x h hmargin hdir ht ⟨i,hi⟩))
      (ne_of_lt hi)
  · rw [path_dead 1 x h t i hi]

theorem path_mem_cube_on_domain {δ : ℝ} (hδ : 0 < δ) {x : Fin N → ℝ} (hx : x ∈ ksCube 1)
    (h : Live 1 x → ℝ) (hmargin : ∀ i : Live 1 x, δ ≤ 1 - |x i|)
    (hdir : ∀ i, |h i| ≤ 2) {t : ℝ} (ht : t ∈ curveDomain δ 2) :
    path 1 x h t ∈ ksCube 1 := by
  have hb (i : Fin N) : |path 1 x h t i| ≤ 1 := by
    by_cases hi : |x i| < 1
    · exact (path_live_on_domain hδ x h hmargin hdir ht ⟨i,hi⟩).le
    · rw [path_dead 1 x h t i hi]
      exact abs_le.mpr ⟨hx.1 i, hx.2 i⟩
  exact ⟨fun i => (abs_le.mp (hb i)).1, fun i => (abs_le.mp (hb i)).2⟩

omit [Nonempty (Fin d)] in
/-- The globally defined debit-state potential equals the fixed-debit curve on the interval. -/
theorem state_path_eq_fullCurve (v : Fin N → Fin d → ℂ) {δ η θ : ℝ}
    (hδ : 0 < δ) (x : Fin N → ℝ) (h : Live 1 x → ℝ)
    (hmargin : ∀ i : Live 1 x, δ ≤ 1 - |x i|) (hdir : ∀ i, |h i| ≤ 2)
    {t : ℝ} (ht : t ∈ curveDomain δ 2) :
    KSDebitPreparation.statePotential v δ η θ (path 1 x h t) =
      KSDebitLiveHessian.fullCurvePotential (stateCenter v δ η x) v θ x h t := by
  have hb := KSDebitBudget.debit_eq_of_same_frozen (fun i => KSRankOne.atom (v i)) δ η
    (path_same_frozen_on_domain hδ x h hmargin hdir ht)
  unfold KSDebitPreparation.statePotential KSDebitPotential.potential
  rw [hb, KSDebitPreparedCurvature.center_path_fixed_debit]
  rfl

/-- Smoothness follows from the actual positive live-owner covariance. -/
theorem fullCurve_contDiffAt (v : Fin N → Fin d → ℂ) {δ η θ : ℝ}
    (hδ : 0 < δ) (hθ : 0 < θ) {x : Fin N → ℝ} (hx : x ∈ ksCube 1)
    (h : Live 1 x → ℝ) (hmargin : ∀ i : Live 1 x, δ ≤ 1 - |x i|)
    (hdir : ∀ i, |h i| ≤ 2) {t : ℝ} (ht : t ∈ curveDomain δ 2) :
    ContDiffAt ℝ ∞ (KSDebitLiveHessian.fullCurvePotential (stateCenter v δ η x) v θ x h) t := by
  let M := stateCenter v δ η x
  let hM := stateCenter_isHermitian v δ η x
  let vr := fun i : Live 1 x => v i
  let xr := fun i : Live 1 x => x i
  have hp := curveC_posDef hδ (by norm_num : (0 : ℝ) ≤ 2) hmargin hdir ht
  have hj := contDiffAt_jointHermitianOwnerPotential (KSSpinSource.family (KSSpinLocalState.atoms vr))
    (KSSpinSource.family_isHermitian _ (fun i => KSRankOne.atom_isHermitian (vr i))) hθ
    (curveH M hM vr h t) (curveC xr h t) hp
  have hc := hj.comp t ((contDiff_curveH M hM vr h).contDiffAt.prodMk (contDiff_curveC xr h).contDiffAt)
  rw [show KSDebitLiveHessian.fullCurvePotential M v θ x h =
    KSDebitLocalState.curvePotential M vr θ xr h from
      funext (KSDebitLiveHessian.fullCurvePotential_eq M v θ hx h)]
  exact hc

omit [Nonempty (Fin d)] in
/-- Equality on an open interval transfers every derivative of the actual state function. -/
theorem state_path_eventuallyEq (v : Fin N → Fin d → ℂ) {δ η θ : ℝ}
    (hδ : 0 < δ) (x : Fin N → ℝ) (h : Live 1 x → ℝ)
    (hmargin : ∀ i : Live 1 x, δ ≤ 1 - |x i|) (hdir : ∀ i, |h i| ≤ 2)
    {t : ℝ} (ht : t ∈ curveDomain δ 2) :
    (fun u => KSDebitPreparation.statePotential v δ η θ (path 1 x h u)) =ᶠ[𝓝 t]
      KSDebitLiveHessian.fullCurvePotential (stateCenter v δ η x) v θ x h := by
  filter_upwards [isOpen_Ioo.mem_nhds ht] with u hu
  exact state_path_eq_fullCurve v hδ x h hmargin hdir hu

/-- All normalized lines of norm at most two meet the required smoothness. -/
theorem face_line_contDiffOn (v : Fin N → Fin d → ℂ) {δ η θ : ℝ}
    (hδ : 0 < δ) (hθ : 0 < θ) {x : Fin N → ℝ} (hx : x ∈ ksCube 1)
    (hmargin : ∀ i : Live 1 x, δ ≤ 1 - |x i|)
    (w : EuclideanSpace ℝ (Fin (KSLiveEnumeration.count x))) (hw : ‖w‖ ≤ 2) :
    ContDiffOn ℝ 4 (fun t : ℝ => facePotential v δ η θ x (t • w)) (Icc (- (δ / 16)) (δ / 16)) := by
  intro t ht
  have hd := coefficientDirection_le_two x w hw
  have hi := radius_mem_curveDomain hδ (abs_le.mpr ht)
  have hc := fullCurve_contDiffAt v (η := η) hδ hθ hx (coefficientDirection x w) hmargin hd hi
  have he := state_path_eventuallyEq v (η := η) (θ := θ) hδ x (coefficientDirection x w) hmargin hd hi
  have hs := hc.congr_of_eventuallyEq he
  have hf : (fun t : ℝ => facePotential v δ η θ x (t • w)) =
      (fun t => KSDebitPreparation.statePotential v δ η θ (path 1 x (coefficientDirection x w) t)) := by
    funext t
    rw [facePotential, face_smul_eq_path]
  rw [hf]
  exact (hs.of_le (WithTop.coe_le_coe.mpr (show (4 : ℕ∞) ≤ ⊤ from le_top))).contDiffWithinAt

/-- The joint bounds imply the true outer fourth derivative cap on every sampled line. -/
theorem face_line_fourth_le (v : Fin N → Fin d → ℂ) {δ η θ B : ℝ}
    (hδ : 0 < δ) (hθ : 0 < θ) (hB : 0 ≤ B) (hd : 0 < d)
    (hJoint : JointBounds v δ η θ B hd)
    (s : Prepared v δ η θ hd) (hs : ¬KSDebitWalkRun.terminal s)
    (w : EuclideanSpace ℝ (Fin (KSLiveEnumeration.count s.coeff))) (hw : ‖w‖ ≤ 2)
    {t : ℝ} (ht : |t| ≤ δ / 16) :
    |iteratedDeriv 4 (fun u => facePotential v δ η θ s.coeff (u • w)) t| ≤
      KSTaylorBudget.budget N δ θ B := by
  let h := coefficientDirection s.coeff w
  have hdir := coefficientDirection_le_two s.coeff w hw
  have hmargin (i : Live 1 s.coeff) : δ ≤ 1 - |s.coeff i| := (s.margin i i.property).le
  have hi := radius_mem_curveDomain hδ ht
  obtain ⟨h₂,h₃,h₄⟩ := hJoint.bounds s hs h hdir t ht
  have hf := fullCurvePotential_fourth_le (stateCenter v δ η s.coeff)
    (stateCenter_isHermitian v δ η s.coeff) v hθ hδ (by norm_num : (0 : ℝ) ≤ 2)
    s.cube h hmargin hdir hi hB h₂ h₃ h₄
  have he := state_path_eventuallyEq v (η := η) (θ := θ) hδ s.coeff h hmargin hdir hi
  have he' : (fun u => facePotential v δ η θ s.coeff (u • w)) =ᶠ[𝓝 t]
      KSDebitLiveHessian.fullCurvePotential (stateCenter v δ η s.coeff) v θ s.coeff h := by
    simpa only [facePotential, face_smul_eq_path] using he
  rw [he'.iteratedDeriv_eq 4]
  exact hf.trans (KSTaylorBudget.envelopeCap_le_budget N δ θ B)

omit [Nonempty (Fin d)] in
/-- The finite Jacobi output is unit length before zero extension. -/
theorem liveDirection_norm (v : Fin N → Fin d → ℂ) (δ η θ M : ℝ) (hd : 0 < d)
    (s : Prepared v δ η θ hd) (hs : ¬KSDebitWalkRun.terminal s) :
    ‖liveDirection v δ η θ M hd s hs‖ = 1 := by
  unfold liveDirection KSNumericalHessian.output
  exact KSJacobiRayleigh.outputVector_norm _ _ _

/-- All Taylor fields for the actual finite numerical controller, from joint caps only. -/
theorem remainingTaylorBounds (v : Fin N → Fin d → ℂ) {δ η θ B : ℝ}
    (hδ : 0 < δ) (hθ : 0 < θ) (hB : 0 ≤ B) (hd : 0 < d)
    (hJoint : JointBounds v δ η θ B hd) :
    RemainingTaylorBounds v δ η θ (KSTaylorBudget.budget N δ θ B) hd := by
  let M := KSTaylorBudget.budget N δ θ B
  have hm := KSTaylorBudget.movementStep_le_hessianRadius N hδ hB hθ
  constructor
  · intro s hs i j
    have hmargin (i : Live 1 s.coeff) : δ ≤ 1 - |s.coeff i| := (s.margin i i.property).le
    have hp := face_line_contDiffOn v (η := η) hδ hθ s.cube hmargin _
      (coordinate_add_norm_le_two i j)
    have hn := face_line_contDiffOn v (η := η) hδ hθ s.cube hmargin _
      (coordinate_sub_norm_le_two i j)
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [zero_add, hessianRadius] using hp
    · simpa only [zero_add, hessianRadius] using hn
    · intro t ht
      simpa only [zero_add] using face_line_fourth_le v hδ hθ hB hd hJoint s hs _
        (coordinate_add_norm_le_two i j) (abs_le.mpr ht)
    · intro t ht
      simpa only [zero_add] using face_line_fourth_le v hδ hθ hB hd hJoint s hs _
        (coordinate_sub_norm_le_two i j) (abs_le.mpr ht)
  · intro s hs
    have hmargin (i : Live 1 s.coeff) : δ ≤ 1 - |s.coeff i| := (s.margin i i.property).le
    have hw : ‖liveDirection v δ η θ M hd s hs‖ ≤ 2 := by rw [liveDirection_norm]; norm_num
    have hc := face_line_contDiffOn v (η := η) hδ hθ s.cube hmargin _ hw
    apply hc.mono
    intro t ht
    change -movementStep N δ M ≤ t ∧ t ≤ movementStep N δ M at ht
    change movementStep N δ M ≤ δ / 16 at hm
    constructor <;> linarith [ht.1, ht.2]
  · intro s hs t ht
    have hw : ‖liveDirection v δ η θ M hd s hs‖ ≤ 2 := by rw [liveDirection_norm]; norm_num
    have htime : |t| ≤ δ / 16 := by
      change movementStep N δ M ≤ δ / 16 at hm
      change -movementStep N δ M ≤ t ∧ t ≤ movementStep N δ M at ht
      exact abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
    exact face_line_fourth_le v hδ hθ hB hd hJoint s hs _ hw htime

/-- Conditional only on actual joint derivative caps, the numerical controller has the proved drift. -/
theorem localPotentialDrift_of_jointBounds (v : Fin N → Fin d → ℂ) {δ η θ B : ℝ}
    (hδ : 0 < δ) (hη : 0 < η) (hθ : 0 < θ) (hB : 0 ≤ B) (hd : 0 < d)
    (hJoint : JointBounds v δ η θ B hd) :
    KSDebitWalkQuality.LocalPotentialDrift
      (KSDebitNumericalController.controller v hδ hη hθ
        (KSTaylorBudget.budget_pos N (δ := δ) hB hθ).le hd) (driftCoefficient N δ) :=
  KSDebitNumericalDrift.localPotentialDrift v hδ hη hθ
    (KSTaylorBudget.budget_pos N (δ := δ) hB hθ).le hd (remainingTaylorBounds v hδ hθ hB hd hJoint)

end MatrixSpencer.KSJointBoundsToTaylor
