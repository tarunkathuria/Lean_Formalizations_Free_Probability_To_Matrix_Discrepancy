import MatrixSpencer.RectangularRidgeCovarianceResponse
import MatrixSpencer.RectangularRidgeCoercivity
import MatrixSpencer.KSFrobeniusTangent
import MatrixSpencer.KSEnvelopeFourth
import MatrixSpencer.KSFourthDifference

/-! Actual mixed covariance optimizer in full trace-zero Frobenius coordinates.
The center is fixed; coefficient covariances vary in their positive fixed face. -/
open Matrix Set Filter
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff Topology
noncomputable section
namespace MatrixSpencer.RectangularRidgeCovarianceEnvelope
open KSFrobeniusTangent
set_option maxHeartbeats 300000
attribute [local irreducible] RectangularRidgePotential.optimizer
variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n] [Nonempty n]
local instance ridgeCovEnvelopeCStar {j : Type*} [Fintype j] [DecidableEq j] : CStarAlgebra (Matrix j j ℂ) := {}
local instance ridgeCovEnvelopePhysicalGroup : NormedAddCommGroup (selfAdjoint (Matrix n n ℂ)) := inferInstance
local instance ridgeCovEnvelopePhysicalSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance
local instance ridgeCovEnvelopeCoeffGroup : NormedAddCommGroup (selfAdjoint (Matrix ι ι ℝ)) := inferInstance
local instance ridgeCovEnvelopeCoeffSpace : NormedSpace ℝ (selfAdjoint (Matrix ι ι ℝ)) := inferInstance
local instance ridgeCovEnvelopeCoordGroup : NormedAddCommGroup (Coordinates n) := inferInstance
local instance ridgeCovEnvelopeCoordSpace : NormedSpace ℝ (Coordinates n) := inferInstance
local instance ridgeCovEnvelopeJointGroup : NormedAddCommGroup (ℝ × Coordinates n) := inferInstance
local instance ridgeCovEnvelopeJointSpace : NormedSpace ℝ (ℝ × Coordinates n) := inferInstance

/-- The original objective in the full affine trace-one Frobenius chart. -/
def objective (A : ι → Matrix n n ℂ) (m : ℕ) (θ κ : ℝ)
    (H : selfAdjoint (Matrix n n ℂ)) (C : ℝ → selfAdjoint (Matrix ι ι ℝ))
    (P : ℝ × Coordinates n) : ℝ := RectangularRidgeCovarianceCalculus.ownerObjective m H A (C P.1) θ κ (chart n P.2)

/-- Coordinates of the already defined canonical density optimizer. -/
def branch (A : ι → Matrix n n ℂ) (m : ℕ) (θ κ : ℝ)
    (H : selfAdjoint (Matrix n n ℂ)) (C : ℝ → selfAdjoint (Matrix ι ι ℝ))
    (t : ℝ) : Coordinates n :=
  project n (RectangularRidgeCalculus.hermitianOptimizer (H : Matrix n n ℂ) (covarianceKraus A (C t)) m θ κ)

theorem chart_branch (A : ι → Matrix n n ℂ) (m : ℕ) (θ κ : ℝ)
    (H : selfAdjoint (Matrix n n ℂ)) (C : ℝ → selfAdjoint (Matrix ι ι ℝ)) (t : ℝ) :
    chart n (branch A m θ κ H C t) = RectangularRidgeCalculus.hermitianOptimizer (H : Matrix n n ℂ) (covarianceKraus A (C t)) m θ κ :=
  chart_project_of_trace_one n _ (RectangularRidgeCalculus.hermitianOptimizer_trace _ _ m θ κ)

theorem branch_posDef (A : ι → Matrix n n ℂ) (m : ℕ) (hm : 1 ≤ m) {θ κ : ℝ} (hθ : 0 < θ) (hκ : 0 < κ)
    (H : selfAdjoint (Matrix n n ℂ)) (C : ℝ → selfAdjoint (Matrix ι ι ℝ)) (t : ℝ) :
    (chart n (branch A m θ κ H C t) : Matrix n n ℂ).PosDef := by
  rw [chart_branch]
  exact RectangularRidgeCalculus.hermitianOptimizer_posDef _ _ m hm θ κ hθ hκ

variable (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
  (m : ℕ) (hm : 1 ≤ m) {θ κ : ℝ} (hθ : 0 < θ) (hκ : 0 < κ)
  (H : selfAdjoint (Matrix n n ℂ)) (C : ℝ → selfAdjoint (Matrix ι ι ℝ))
  (hC : ContDiff ℝ ∞ C)

include hA hC

theorem objective_contDiffAt {t : ℝ} {x : Coordinates n}
    (hCt : (C t : Matrix ι ι ℝ).PosDef) (hS : (chart n x : Matrix n n ℂ).PosDef) :
    ContDiffAt ℝ ∞ (objective A m θ κ H C) (t,x) := by
  have hp : ContDiffAt ℝ ∞ (fun P : ℝ × Coordinates n => (C P.1, chart n P.2)) (t,x) :=
    (hC.contDiffAt.comp (t,x) contDiffAt_fst).prodMk
      ((contDiff_chart n).contDiffAt.comp (t,x) contDiffAt_snd)
  exact (RectangularRidgeCovarianceCalculus.contDiffAt_jointOwnerObjective m
    (H : Matrix n n ℂ) A hA θ κ (C t) (chart n x) hCt hS).comp (t,x) hp

include hθ hκ hm in
theorem branch_contDiffAt {t : ℝ} (hCt : (C t : Matrix ι ι ℝ).PosDef) :
    ContDiffAt ℝ ∞ (branch A m θ κ H C) t := by
  have hj := RectangularRidgeCovarianceResponse.contDiffAt_covarianceDensityOptimizer
    m hm (H : Matrix n n ℂ) A hA hθ hκ (C t) hCt
  have hc := ContDiffAt.comp (g := fun K : selfAdjoint (Matrix ι ι ℝ) =>
    RectangularRidgeCalculus.hermitianOptimizer (H : Matrix n n ℂ) (covarianceKraus A K) m θ κ)
    (f := C) t hj hC.contDiffAt
  exact ContDiffAt.comp (g := project n) (f := fun z =>
    RectangularRidgeCalculus.hermitianOptimizer (H : Matrix n n ℂ) (covarianceKraus A (C z)) m θ κ)
    t (project n).contDiff.contDiffAt hc

omit hC in
theorem vertical_line_eq {t : ℝ} (hCt : (C t : Matrix ι ι ℝ).PosDef)
    (x u : Coordinates n) :
    (fun z : ℝ => objective A m θ κ H C ((t,x) + z • ((0 : ℝ),u))) =
      (fun z => RectangularRidgeCalculus.hermitianObjective (H : Matrix n n ℂ) (covarianceKraus A (C t)) m θ κ
        (chart n x + z • embedding n u)) := by
  funext z
  have he : chart n (x + z • u) = chart n x + z • embedding n u := by
    simp only [chart, map_add, map_smul]
    module
  change RectangularRidgeCovarianceCalculus.ownerObjective m (H : Matrix n n ℂ) A (C (t + z * 0)) θ κ (chart n (x + z • u)) = _
  rw [mul_zero, add_zero, he, RectangularRidgeCovarianceCalculus.ownerObjective_eq_densityObjective m _ A hA hCt.posSemidef]
  rfl

/-- The actual joint vertical derivative is the original density derivative. -/
theorem vertical_derivative {t : ℝ} (hCt : (C t : Matrix ι ι ℝ).PosDef)
    (x u : Coordinates n) (hS : (chart n x : Matrix n n ℂ).PosDef) :
    fderiv ℝ (objective A m θ κ H C) (t,x) (0,u) =
      fderiv ℝ (RectangularRidgeCalculus.hermitianObjective (H : Matrix n n ℂ) (covarianceKraus A (C t)) m θ κ)
        (chart n x) (embedding n u) := by
  have ho := ((objective_contDiffAt A hA m (θ := θ) (κ := κ) H C hC hCt hS).differentiableAt (by simp)).hasFDerivAt
  have hf := ((RectangularRidgeCalculus.contDiffAt_hermitianObjective
    (H : Matrix n n ℂ) (covarianceKraus A (C t)) m θ κ (chart n x) hS).differentiableAt (by simp)).hasFDerivAt
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
      fderiv ℝ (fderiv ℝ (RectangularRidgeCalculus.hermitianObjective (H : Matrix n n ℂ) (covarianceKraus A (C t)) m θ κ))
        (chart n x) (embedding n u) (embedding n u) := by
  rw [← KSFourthDifference.line_second (objective A m θ κ H C) (t,x) (0,u)
    ((objective_contDiffAt A hA m (θ := θ) (κ := κ) H C hC hCt hS).of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)))]
  rw [vertical_line_eq A hA m (θ := θ) (κ := κ) H C hCt x u]
  exact KSFourthDifference.line_second _ _ _
    ((RectangularRidgeCalculus.contDiffAt_hermitianObjective
      (H : Matrix n n ℂ) (covarianceKraus A (C t)) m θ κ (chart n x) hS).of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)))


include hθ hκ hm

/-- Vertical stationarity of the canonical optimizer, discharged internally. -/
theorem branch_stationary {t : ℝ} (hCt : (C t : Matrix ι ι ℝ).PosDef)
    (u : Coordinates n) :
    fderiv ℝ (objective A m θ κ H C) (t,branch A m θ κ H C t) (0,u) = 0 := by
  rw [vertical_derivative A hA m H C hC hCt _ u (branch_posDef A m hm hθ hκ H C t), chart_branch]
  let U : densityTangent (n := n) := ⟨embedding n u, (mem_densityTangent_iff _).mpr (embedding_trace n u)⟩
  have hs := DFunLike.congr_fun (RectangularRidgeCalculus.hermitianOptimizer_stationary
    (H : Matrix n n ℂ) (covarianceKraus A (C t)) m hm θ κ hθ hκ) U
  exact hs

/-- The actual vertical Hessian has the explicit Frobenius coercivity `θ/2`. -/
theorem branch_coercive {t : ℝ} (hCt : (C t : Matrix ι ι ℝ).PosDef)
    (u : Coordinates n) :
    κ / 2 * ‖u‖ ^ 2 ≤
      -KSEnvelopeFourth.second (objective A m θ κ H C) (t,branch A m θ κ H C t) (0,u) (0,u) := by
  rw [vertical_hessian A hA m H C hC hCt _ u (branch_posDef A m hm hθ hκ H C t), chart_branch]
  have hh := RectangularRidgeCalculus.negativeHessian_coercive
    (H : Matrix n n ℂ) (covarianceKraus A (C t)) m hm hθ hκ
    (RectangularRidgeCalculus.hermitianOptimizer (H : Matrix n n ℂ) (covarianceKraus A (C t)) m θ κ)
    (embedding n u)
    (RectangularRidgeCalculus.hermitianOptimizer_posDef _ _ m hm θ κ hθ hκ)
    (RectangularRidgeCalculus.hermitianOptimizer_trace _ _ m θ κ)
  rw [embedding_trace_square] at hh
  exact hh

omit hθ hκ hC in
/-- The envelope is exactly the original supremum potential. -/
theorem value_eq {t : ℝ} (hCt : (C t : Matrix ι ι ℝ).PosDef) :
    objective A m θ κ H C (t,branch A m θ κ H C t) = RectangularRidgeCovarianceCalculus.ownerPotential m H A (C t) θ κ := by
  unfold objective
  rw [chart_branch]
  exact (RectangularRidgeCovarianceResponse.ownerPotential_eq_chosenObjective m hm
    (H : Matrix n n ℂ) A hA θ κ (C t) hCt.posSemidef).symm

end MatrixSpencer.RectangularRidgeCovarianceEnvelope
