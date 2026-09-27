import MatrixSpencer.KSFullManuscriptQueries
import MatrixSpencer.KSFullManuscriptJointPoint



open Matrix Set Filter
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff Topology
noncomputable section
namespace MatrixSpencer.KSFullManuscriptTaylor
set_option maxHeartbeats 1200000

open KSFullManuscriptParameters KSFullManuscriptLiveCoordinates KSFullManuscriptQueries
open KSLiveCurve KSActualEnvelope
variable {N d : ℕ} [Nonempty (Fin d)]

def budget (v : Fin N → Fin d → ℂ) (δ η θ : ℝ) : ℝ :=
  max (KSTaylorBudget.envelopeCap (KSJointBoundParameters.jointCap v δ η θ) θ)
    (6144 * curvatureTolerance N δ / δ ^ 2) + 1

theorem budget_pos (v : Fin N → Fin d → ℂ) {δ η θ : ℝ}
    (hδ : 0 < δ) (hη : 0 ≤ η) (hθ : 0 < θ) : 0 < budget v δ η θ := by
  have h := KSTaylorBudget.envelopeCap_nonneg
    (KSJointBoundParameters.jointCap_pos v hδ hη hθ).le hθ
  have hm := le_max_left (KSTaylorBudget.envelopeCap (KSJointBoundParameters.jointCap v δ η θ) θ)
    (6144 * curvatureTolerance N δ / δ ^ 2)
  unfold budget
  linarith

theorem envelope_le (v : Fin N → Fin d → ℂ) (δ η θ : ℝ) :
    KSTaylorBudget.envelopeCap (KSJointBoundParameters.jointCap v δ η θ) θ ≤ budget v δ η θ := by
  have h := le_max_left (KSTaylorBudget.envelopeCap (KSJointBoundParameters.jointCap v δ η θ) θ)
    (6144 * curvatureTolerance N δ / δ ^ 2)
  unfold budget
  linarith

theorem scalar_le (v : Fin N → Fin d → ℂ) (δ η θ : ℝ) :
    6144 * curvatureTolerance N δ / δ ^ 2 ≤ budget v δ η θ := by
  have h := le_max_right (KSTaylorBudget.envelopeCap (KSJointBoundParameters.jointCap v δ η θ) θ)
    (6144 * curvatureTolerance N δ / δ ^ 2)
  unfold budget
  linarith

theorem movementStep_le_radius (v : Fin N → Fin d → ℂ) {δ η θ : ℝ}
    (hδ : 0 < δ) (hη : 0 ≤ η) (hθ : 0 < θ) :
    movementStep N δ (budget v δ η θ) ≤ δ / 16 := by
  have hM := budget_pos v hδ hη hθ
  have hb := (div_le_iff₀ (sq_pos_of_pos hδ)).mp (scalar_le v δ η θ)
  have hs : 24 * curvatureTolerance N δ / budget v δ η θ ≤ (δ / 16) ^ 2 := by
    apply (div_le_iff₀ hM).mpr
    nlinarith
  exact (min_le_right _ _).trans ((Real.sqrt_le_iff).mpr ⟨by positivity, hs⟩)

theorem queryStep_le_radius (v : Fin N → Fin d → ℂ) (hN : 0 < N) {δ η θ : ℝ}
    (hδ : 0 < δ) (hη : 0 ≤ η) (hθ : 0 < θ) :
    queryStep N δ (budget v δ η θ) ≤ δ / 16 := by
  have hM := budget_pos v hδ hη hθ
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hden : 0 < 8 * (N : ℝ) * budget v δ η θ := by positivity
  have hb := (div_le_iff₀ (sq_pos_of_pos hδ)).mp (scalar_le v δ η θ)
  have hp := mul_le_mul_of_nonneg_right hn (mul_nonneg hM.le (sq_nonneg δ))
  have hκ := (curvatureTolerance_pos hN hδ).le
  have hs : curvatureTolerance N δ / (8 * N * budget v δ η θ) ≤ (δ / 16) ^ 2 := by
    apply (div_le_iff₀ hden).mpr
    nlinarith
  exact (min_le_right _ _).trans ((Real.sqrt_le_iff).mpr ⟨by positivity, hs⟩)

theorem line_contDiffOn (v : Fin N → Fin d → ℂ) {δ η θ : ℝ}
    (hδ : 0 < δ) (hθ : 0 < θ) {x : Fin N → ℝ} (hx : x ∈ ksCube 1)
    (hmargin : ∀ i : Live 1 x, δ ≤ 1 - |x i|)
    (w : KSNumericalHessian.Space (KSLiveEnumeration.count x)) (hw : ‖w‖ ≤ 2) :
    ContDiffOn ℝ 4 (fun t : ℝ => facePotential v δ η θ x (t • w))
      (Icc (-(δ / 16)) (δ / 16)) := by
  intro t ht
  have hd := coefficientDirection_le_two x w hw
  have hi := KSJointBoundsToTaylor.radius_mem_curveDomain hδ (abs_le.mpr ht)
  have hc := KSJointBoundsToTaylor.fullCurve_contDiffAt v (η := η) hδ hθ hx
    (coefficientDirection x w) hmargin hd hi
  have he := KSJointBoundsToTaylor.state_path_eventuallyEq v (η := η) (θ := θ)
    hδ x (coefficientDirection x w) hmargin hd hi
  have hs := hc.congr_of_eventuallyEq he
  have hf : (fun t : ℝ => facePotential v δ η θ x (t • w)) =
      (fun t => KSDebitPreparation.statePotential v δ η θ
        (path 1 x (coefficientDirection x w) t)) := by
    funext t
    rw [facePotential, face_smul_eq_path]
  rw [hf]
  exact (hs.of_le (WithTop.coe_le_coe.mpr (show (4 : ℕ∞) ≤ ⊤ from le_top))).contDiffWithinAt

theorem line_fourth_le (v : Fin N → Fin d → ℂ) {δ η θ : ℝ}
    (hδ : 0 < δ) (hη : 0 ≤ η) (hθ : 0 < θ) {x : Fin N → ℝ} (hx : x ∈ ksCube 1)
    (hmargin : ∀ i : Live 1 x, δ ≤ 1 - |x i|)
    (w : KSNumericalHessian.Space (KSLiveEnumeration.count x)) (hw : ‖w‖ ≤ 2)
    {t : ℝ} (ht : |t| ≤ δ / 16) :
    |iteratedDeriv 4 (fun u => facePotential v δ η θ x (u • w)) t| ≤ budget v δ η θ := by
  let h := coefficientDirection x w
  have hdir := coefficientDirection_le_two x w hw
  have hi := KSJointBoundsToTaylor.radius_mem_curveDomain hδ ht
  obtain ⟨h₂,h₃,h₄⟩ := KSFullManuscriptJointPoint.joint_bounds v hδ hη hθ x hx h hmargin hdir ht
  have hf := fullCurvePotential_fourth_le (KSDebitPreparedMargin.stateCenter v δ η x)
    (KSJointBoundsToTaylor.stateCenter_isHermitian v δ η x) v hθ hδ (by norm_num : (0 : ℝ) ≤ 2)
    hx h hmargin hdir hi (KSJointBoundParameters.jointCap_pos v hδ hη hθ).le h₂ h₃ h₄
  have he := KSJointBoundsToTaylor.state_path_eventuallyEq v (η := η) (θ := θ) hδ x h hmargin hdir hi
  have he' : (fun u => facePotential v δ η θ x (u • w)) =ᶠ[𝓝 t]
      KSDebitLiveHessian.fullCurvePotential (KSDebitPreparedMargin.stateCenter v δ η x) v θ x h := by
    simpa only [facePotential, face_smul_eq_path] using he
  rw [he'.iteratedDeriv_eq 4]
  exact hf.trans (envelope_le v δ η θ)

/-- All exact unweighted diagonal/mixed stencil lines satisfy the required
fourth-derivative bound, uniformly over every prepared live face. -/
theorem lineBounds (v : Fin N → Fin d → ℂ) (hN : 0 < N) {δ η θ : ℝ}
    (hδ : 0 < δ) (hη : 0 ≤ η) (hθ : 0 < θ) {x : Fin N → ℝ} (hx : x ∈ ksCube 1)
    (hmargin : ∀ i : Live 1 x, δ ≤ 1 - |x i|) :
    KSFullManuscriptHessian.LineBounds (facePotential v δ η θ x) 0
      (queryStep N δ (budget v δ η θ)) (budget v δ η θ) := by
  have hq := queryStep_le_radius v hN hδ hη hθ
  have hs (w : KSNumericalHessian.Space (KSLiveEnumeration.count x)) (hw : ‖w‖ ≤ 2) :
      ContDiffOn ℝ 4 (fun t : ℝ => facePotential v δ η θ x (0 + t • w))
        (Icc (-queryStep N δ (budget v δ η θ)) (queryStep N δ (budget v δ η θ))) := by
    simp only [zero_add]
    apply (line_contDiffOn v (η := η) hδ hθ hx hmargin w hw).mono
    intro t ht
    constructor <;> linarith [ht.1,ht.2]
  have hb (w : KSNumericalHessian.Space (KSLiveEnumeration.count x)) (hw : ‖w‖ ≤ 2)
      (t : ℝ) (ht : t ∈ Icc (-queryStep N δ (budget v δ η θ)) (queryStep N δ (budget v δ η θ))) :
      |iteratedDeriv 4 (fun u => facePotential v δ η θ x (0 + u • w)) t| ≤ budget v δ η θ := by
    simpa only [zero_add] using line_fourth_le v hδ hη hθ hx hmargin w hw
      (abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  refine ⟨?_, ?_⟩
  · intro i
    have hi : ‖KSNumericalHessian.coordinate i‖ ≤ 2 := by rw [coordinate_norm]; norm_num
    exact ⟨hs _ hi, hb _ hi⟩
  · intro i j _
    have hp := coordinate_add_norm_le_two i j
    have hm := coordinate_sub_norm_le_two i j
    refine ⟨hs _ hp, hs _ hm, ?_, ?_⟩
    · intro t ht
      have he := hb _ hp t ht
      linarith [budget_pos v hδ hη hθ]
    · intro t ht
      have he := hb _ hm t ht
      linarith [budget_pos v hδ hη hθ]

end MatrixSpencer.KSFullManuscriptTaylor
