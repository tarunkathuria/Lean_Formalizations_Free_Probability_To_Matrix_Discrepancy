import MatrixSpencer.RectangularRidgeJointOwnerResponse
import MatrixSpencer.RectangularRidgeCoercivity
import MatrixSpencer.KSActualEnvelope

/-! Actual mixed optimized envelope along jointly moving center and covariance.
The branch is the attained global density optimizer; source ranks are arbitrary. -/
open Matrix Set Filter
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff Topology
noncomputable section
namespace MatrixSpencer.RectangularRidgeActualEnvelope
open KSFrobeniusTangent
open KSActualEnvelope (secondNorm thirdNorm fourthNorm)
set_option maxHeartbeats 300000
attribute [local irreducible] RectangularRidgePotential.optimizer
variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n] [Nonempty n]
local instance ridgeEnvelopeCStar {j : Type*} [Fintype j] [DecidableEq j] : CStarAlgebra (Matrix j j ℂ) := {}
local instance ridgeEnvelopePhysicalGroup : NormedAddCommGroup (selfAdjoint (Matrix n n ℂ)) := inferInstance
local instance ridgeEnvelopePhysicalSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance
local instance ridgeEnvelopeCoeffGroup : NormedAddCommGroup (selfAdjoint (Matrix ι ι ℝ)) := inferInstance
local instance ridgeEnvelopeCoeffSpace : NormedSpace ℝ (selfAdjoint (Matrix ι ι ℝ)) := inferInstance
local instance ridgeEnvelopeCoordGroup : NormedAddCommGroup (Coordinates n) := inferInstance
local instance ridgeEnvelopeCoordSpace : NormedSpace ℝ (Coordinates n) := inferInstance
local instance ridgeEnvelopeJointGroup : NormedAddCommGroup (ℝ × Coordinates n) := inferInstance
local instance ridgeEnvelopeJointSpace : NormedSpace ℝ (ℝ × Coordinates n) := inferInstance

/-- The original objective in the full affine trace-one Frobenius chart. -/
def objective (A : ι → Matrix n n ℂ) (m : ℕ) (θ κ : ℝ)
    (H : ℝ → selfAdjoint (Matrix n n ℂ)) (C : ℝ → selfAdjoint (Matrix ι ι ℝ))
    (P : ℝ × Coordinates n) : ℝ := RectangularRidgeCovarianceCalculus.ownerObjective m (H P.1) A (C P.1) θ κ (chart n P.2)

/-- Coordinates of the already defined canonical density optimizer. -/
def branch (A : ι → Matrix n n ℂ) (m : ℕ) (θ κ : ℝ)
    (H : ℝ → selfAdjoint (Matrix n n ℂ)) (C : ℝ → selfAdjoint (Matrix ι ι ℝ))
    (t : ℝ) : Coordinates n :=
  project n (jointRidgeOwnerDensityOptimizer A m θ κ (H t, C t))

theorem chart_branch (A : ι → Matrix n n ℂ) (m : ℕ) (θ κ : ℝ)
    (H : ℝ → selfAdjoint (Matrix n n ℂ)) (C : ℝ → selfAdjoint (Matrix ι ι ℝ)) (t : ℝ) :
    chart n (branch A m θ κ H C t) = jointRidgeOwnerDensityOptimizer A m θ κ (H t, C t) :=
  chart_project_of_trace_one n _ (RectangularRidgeCalculus.hermitianOptimizer_trace _ _ m θ κ)

theorem branch_posDef (A : ι → Matrix n n ℂ) (m : ℕ) (hm : 1 ≤ m) {θ κ : ℝ} (hθ : 0 < θ) (hκ : 0 < κ)
    (H : ℝ → selfAdjoint (Matrix n n ℂ)) (C : ℝ → selfAdjoint (Matrix ι ι ℝ)) (t : ℝ) :
    (chart n (branch A m θ κ H C t) : Matrix n n ℂ).PosDef := by
  rw [chart_branch]
  exact RectangularRidgeCalculus.hermitianOptimizer_posDef _ _ m hm θ κ hθ hκ

variable (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
  (m : ℕ) (hm : 1 ≤ m) {θ κ : ℝ} (hθ : 0 < θ) (hκ : 0 < κ)
  (H : ℝ → selfAdjoint (Matrix n n ℂ)) (C : ℝ → selfAdjoint (Matrix ι ι ℝ))
  (hH : ContDiff ℝ ∞ H) (hC : ContDiff ℝ ∞ C)

include hA hH hC

theorem objective_contDiffAt {t : ℝ} {x : Coordinates n}
    (hCt : (C t : Matrix ι ι ℝ).PosDef) (hS : (chart n x : Matrix n n ℂ).PosDef) :
    ContDiffAt ℝ ∞ (objective A m θ κ H C) (t,x) := by
  have hh : ContDiffAt ℝ ∞ (fun P : ℝ × Coordinates n => (H P.1 : Matrix n n ℂ)) (t,x) :=
    (hermitianInclusion (n := n)).contDiff.contDiffAt.comp (t,x) (hH.contDiffAt.comp (t,x) contDiffAt_fst)
  have hs : ContDiffAt ℝ ∞ (fun P : ℝ × Coordinates n => (chart n P.2 : Matrix n n ℂ)) (t,x) :=
    (hermitianInclusion (n := n)).contDiff.contDiffAt.comp (t,x) ((contDiff_chart n).contDiffAt.comp (t,x) contDiffAt_snd)
  have hl := realTraceCLM.contDiff.contDiffAt.comp (t,x) (hh.mul hs)
  have hp : ContDiffAt ℝ ∞ (fun P : ℝ × Coordinates n => (C P.1, chart n P.2)) (t,x) :=
    (hC.contDiffAt.comp (t,x) contDiffAt_fst).prodMk
      ((contDiff_chart n).contDiffAt.comp (t,x) contDiffAt_snd)
  have hj := (RectangularRidgeCovarianceCalculus.contDiffAt_jointOwnerObjective m (0 : Matrix n n ℂ) A hA θ κ (C t) (chart n x) hCt hS).comp (t,x) hp
  apply (hl.add hj).congr_of_eventuallyEq
  filter_upwards [] with P
  change RectangularRidgeCovarianceCalculus.ownerObjective m (H P.1) A (C P.1) θ κ (chart n P.2) =
    realTrace ((H P.1 : Matrix n n ℂ) * (chart n P.2 : Matrix n n ℂ)) +
      RectangularRidgeCovarianceCalculus.ownerObjective m (0 : Matrix n n ℂ) A (C P.1) θ κ (chart n P.2)
  simp only [RectangularRidgeCovarianceCalculus.ownerObjective, regularizedOwnerObjective, Matrix.zero_mul, realTrace_zero, zero_add]
  ring

include hθ hκ hm in
theorem branch_contDiffAt {t : ℝ} (hCt : (C t : Matrix ι ι ℝ).PosDef) :
    ContDiffAt ℝ ∞ (branch A m θ κ H C) t := by
  have hj : ContDiffAt ℝ ∞ (jointRidgeOwnerDensityOptimizer A m θ κ) (H t,C t) :=
    contDiffAt_jointRidgeOwnerDensityOptimizer A hA m hm θ κ hθ hκ (H t) (C t) hCt
  have hpair : ContDiffAt ℝ ∞ (fun z => (H z,C z)) t := hH.contDiffAt.prodMk hC.contDiffAt
  have hc := ContDiffAt.comp (g := jointRidgeOwnerDensityOptimizer A m θ κ) (f := fun z => (H z,C z)) t hj hpair
  exact ContDiffAt.comp (g := project n) (f := fun z => jointRidgeOwnerDensityOptimizer A m θ κ (H z,C z)) t
    (project n).contDiff.contDiffAt hc

omit hH hC in
theorem vertical_line_eq {t : ℝ} (hCt : (C t : Matrix ι ι ℝ).PosDef)
    (x u : Coordinates n) :
    (fun z : ℝ => objective A m θ κ H C ((t,x) + z • ((0 : ℝ),u))) =
      (fun z => RectangularRidgeCalculus.hermitianObjective (H t : Matrix n n ℂ) (covarianceKraus A (C t)) m θ κ
        (chart n x + z • embedding n u)) := by
  funext z
  have he : chart n (x + z • u) = chart n x + z • embedding n u := by
    simp only [chart, map_add, map_smul]
    module
  change RectangularRidgeCovarianceCalculus.ownerObjective m (H (t + z * 0)) A (C (t + z * 0)) θ κ (chart n (x + z • u)) = _
  rw [mul_zero, add_zero, he, RectangularRidgeCovarianceCalculus.ownerObjective_eq_densityObjective m _ A hA hCt.posSemidef]
  rfl

/-- The actual joint vertical derivative is the original density derivative. -/
theorem vertical_derivative {t : ℝ} (hCt : (C t : Matrix ι ι ℝ).PosDef)
    (x u : Coordinates n) (hS : (chart n x : Matrix n n ℂ).PosDef) :
    fderiv ℝ (objective A m θ κ H C) (t,x) (0,u) =
      fderiv ℝ (RectangularRidgeCalculus.hermitianObjective (H t : Matrix n n ℂ) (covarianceKraus A (C t)) m θ κ)
        (chart n x) (embedding n u) := by
  have ho := ((objective_contDiffAt A hA m (θ := θ) (κ := κ) H C hH hC hCt hS).differentiableAt (by simp)).hasFDerivAt
  have hf := ((RectangularRidgeCalculus.contDiffAt_hermitianObjective
    (H t : Matrix n n ℂ) (covarianceKraus A (C t)) m θ κ (chart n x) hS).differentiableAt (by simp)).hasFDerivAt
  have hline := ho.comp_hasDerivAt_of_eq 0
    (((hasDerivAt_id (0 : ℝ)).smul_const ((0 : ℝ),u)).const_add (t,x)) (by simp)
  have hline' := hf.comp_hasDerivAt_of_eq 0
    (((hasDerivAt_id (0 : ℝ)).smul_const (embedding n u)).const_add (chart n x)) (by simp)
  simp only [Function.comp_def, id_eq, one_smul] at hline hline'
  rw [vertical_line_eq A hA m (θ := θ) (κ := κ) H C hCt x u] at hline
  exact hline.unique hline'

/-- The actual joint vertical Hessian is the original density Hessian. -/
theorem vertical_hessian {t : ℝ} (hCt : (C t : Matrix ι ι ℝ).PosDef)
    (x u : Coordinates n) (hS : (chart n x : Matrix n n ℂ).PosDef) :
    KSEnvelopeFourth.second (objective A m θ κ H C) (t,x) (0,u) (0,u) =
      fderiv ℝ (fderiv ℝ (RectangularRidgeCalculus.hermitianObjective (H t : Matrix n n ℂ) (covarianceKraus A (C t)) m θ κ))
        (chart n x) (embedding n u) (embedding n u) := by
  rw [← KSFourthDifference.line_second (objective A m θ κ H C) (t,x) (0,u)
    ((objective_contDiffAt A hA m (θ := θ) (κ := κ) H C hH hC hCt hS).of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)))]
  rw [vertical_line_eq A hA m (θ := θ) (κ := κ) H C hCt x u]
  exact KSFourthDifference.line_second _ _ _
    ((RectangularRidgeCalculus.contDiffAt_hermitianObjective
      (H t : Matrix n n ℂ) (covarianceKraus A (C t)) m θ κ (chart n x) hS).of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)))


include hθ hκ hm

/-- Vertical stationarity of the canonical optimizer, discharged internally. -/
theorem branch_stationary {t : ℝ} (hCt : (C t : Matrix ι ι ℝ).PosDef)
    (u : Coordinates n) :
    fderiv ℝ (objective A m θ κ H C) (t,branch A m θ κ H C t) (0,u) = 0 := by
  rw [vertical_derivative A hA m H C hH hC hCt _ u (branch_posDef A m hm hθ hκ H C t), chart_branch]
  let U : densityTangent (n := n) := ⟨embedding n u, (mem_densityTangent_iff _).mpr (embedding_trace n u)⟩
  have hs := DFunLike.congr_fun (RectangularRidgeCalculus.hermitianOptimizer_stationary
    (H t : Matrix n n ℂ) (covarianceKraus A (C t)) m hm θ κ hθ hκ) U
  exact hs

/-- The actual vertical Hessian has the explicit Frobenius coercivity `κ/2`. -/
theorem branch_coercive {t : ℝ} (hCt : (C t : Matrix ι ι ℝ).PosDef)
    (u : Coordinates n) :
    κ / 2 * ‖u‖ ^ 2 ≤
      -KSEnvelopeFourth.second (objective A m θ κ H C) (t,branch A m θ κ H C t) (0,u) (0,u) := by
  rw [vertical_hessian A hA m H C hH hC hCt _ u (branch_posDef A m hm hθ hκ H C t), chart_branch]
  have hh := RectangularRidgeCalculus.negativeHessian_coercive
    (H t : Matrix n n ℂ) (covarianceKraus A (C t)) m hm hθ hκ
    (jointRidgeOwnerDensityOptimizer A m θ κ (H t,C t)) (embedding n u)
    (RectangularRidgeCalculus.hermitianOptimizer_posDef _ _ m hm θ κ hθ hκ)
    (RectangularRidgeCalculus.hermitianOptimizer_trace _ _ m θ κ)
  rw [embedding_trace_square] at hh
  exact hh

omit hθ hκ hH hC in
/-- The envelope is exactly the original supremum potential. -/
theorem value_eq {t : ℝ} (hCt : (C t : Matrix ι ι ℝ).PosDef) :
    objective A m θ κ H C (t,branch A m θ κ H C t) = RectangularRidgeCovarianceCalculus.ownerPotential m (H t) A (C t) θ κ := by
  unfold objective
  rw [chart_branch]
  exact (RectangularRidgeCovarianceResponse.ownerPotential_eq_chosenObjective m hm (H t : Matrix n n ℂ) A hA θ κ (C t) hCt.posSemidef).symm

/-- Actual optimizer, stationarity and coercivity are all instantiated here.
Only the actual joint second-through-fourth derivative caps remain hypotheses. -/
theorem potential_fourth_le {I : Set ℝ} (hI : IsOpen I)
    (hpositive : ∀ t ∈ I, (C t : Matrix ι ι ℝ).PosDef)
    {t B : ℝ} (ht : t ∈ I) (hB : 0 ≤ B)
    (h₂ : secondNorm (objective A m θ κ H C) (t,branch A m θ κ H C t) ≤ B)
    (h₃ : thirdNorm (objective A m θ κ H C) (t,branch A m θ κ H C t) ≤ B)
    (h₄ : fourthNorm (objective A m θ κ H C) (t,branch A m θ κ H C t) ≤ B) :
    |iteratedDeriv 4 (fun z => RectangularRidgeCovarianceCalculus.ownerPotential m (H z) A (C z) θ κ) t| ≤
      (B + 3 * B ^ 2 / (κ / 2)) * (1 + B / (κ / 2)) ^ 4 := by
  have hs : ContDiffOn ℝ 4 (branch A m θ κ H C) I := by
    intro z hz
    exact ((branch_contDiffAt A hA m hm hθ hκ H C hH hC (hpositive z hz)).of_le
      (WithTop.coe_le_coe.mpr (show (4 : ℕ∞) ≤ ⊤ from le_top))).contDiffWithinAt
  have hf : ∀ z ∈ I, ContDiffAt ℝ 4 (objective A m θ κ H C)
      (KSEnvelopeFourth.lift (branch A m θ κ H C) z) := by
    intro z hz
    exact (objective_contDiffAt A hA m H C hH hC (hpositive z hz) (branch_posDef A m hm hθ hκ H C z)).of_le
      (WithTop.coe_le_coe.mpr (show (4 : ℕ∞) ≤ ⊤ from le_top))
  have hstat : ∀ z ∈ I, ∀ u : Coordinates n,
      fderiv ℝ (objective A m θ κ H C) (KSEnvelopeFourth.lift (branch A m θ κ H C) z) (0,u) = 0 :=
    fun z hz u => branch_stationary A hA m hm hθ hκ H C hH hC (hpositive z hz) u
  have hh := KSEnvelopeFourth.value_fourth_le hI hs hf hstat ht
    (div_pos hκ (by norm_num)) hB h₂ h₃ h₄ (branch_coercive A hA m hm hθ hκ H C hH hC (hpositive t ht))
  have he : (fun z => objective A m θ κ H C (KSEnvelopeFourth.lift (branch A m θ κ H C) z)) =ᶠ[𝓝 t]
      (fun z => RectangularRidgeCovarianceCalculus.ownerPotential m (H z) A (C z) θ κ) := by
    filter_upwards [hI.mem_nhds ht] with z hz
    exact value_eq A hA m hm H C (hpositive z hz)
  rwa [Filter.EventuallyEq.iteratedDeriv_eq 4 he] at hh

end MatrixSpencer.RectangularRidgeActualEnvelope
