import MatrixSpencer.RectangularRidgeCovarianceEnvelope
import MatrixSpencer.RectangularRidgeEnvelopeSecond
import MatrixSpencer.MSManuscriptAffineJointBoundsScaled

/-! Covariance curvature of the actual mixed optimum. The covariance column
of the joint Hessian is exactly the source column, so its bound is independent
of the dyadic regularizer's density Hessian. -/
open Matrix Set Filter
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff Topology
noncomputable section
namespace MatrixSpencer.RectangularRidgeCovarianceCurvature
open KSFrobeniusTangent RectangularRidgeCovarianceEnvelope KSEnvelopeFourth
variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n] [Nonempty n]
local instance ridgeCovCurvatureCStar {j : Type*} [Fintype j] [DecidableEq j] : CStarAlgebra (Matrix j j ℂ) := {}
local instance ridgeCovCurvaturePhysicalSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance
local instance ridgeCovCurvatureCoeffSpace : NormedSpace ℝ (selfAdjoint (Matrix ι ι ℝ)) := inferInstance
local instance ridgeCovCurvatureCoordGroup : NormedAddCommGroup (Coordinates n) := inferInstance
local instance ridgeCovCurvatureCoordSpace : NormedSpace ℝ (Coordinates n) := inferInstance
local instance ridgeCovCurvatureJointGroup : NormedAddCommGroup (ℝ × Coordinates n) := inferInstance
local instance ridgeCovCurvatureJointSpace : NormedSpace ℝ (ℝ × Coordinates n) := inferInstance
set_option maxHeartbeats 300000
attribute [local irreducible] RectangularRidgePotential.optimizer

def regularizerChart (m : ℕ) (θ κ : ℝ) (x : Coordinates n) : ℝ :=
  dyadicTsallisPotential m θ (chart n x) + tsallisPotential κ (chart n x)

theorem objective_eq_source_add (A : ι → Matrix n n ℂ) (m : ℕ) (θ κ : ℝ)
    (H : selfAdjoint (Matrix n n ℂ)) (C : ℝ → selfAdjoint (Matrix ι ι ℝ)) :
    objective A m θ κ H C = fun p =>
      KSActualEnvelope.objective A 0 (fun _ => H) C p + regularizerChart m θ κ p.2 := by
  funext p
  unfold objective RectangularRidgeCovarianceCalculus.ownerObjective
    RectangularRidgeCovarianceCalculus.regularizer regularizedOwnerObjective
    KSActualEnvelope.objective MatrixSpencer.ownerObjective regularizerChart
    dyadicTsallisPotential tsallisPotential traceSqrt
  ring

theorem regularizerChart_contDiffAt (m : ℕ) (θ κ : ℝ) (x : Coordinates n)
    (hS : (chart n x : Matrix n n ℂ).PosDef) :
    ContDiffAt ℝ ∞ (regularizerChart (n := n) m θ κ) x :=
  ((contDiffAt_dyadicTsallisPotential m θ (chart n x) hS).add
    (contDiffAt_tsallisPotential κ (chart n x) hS)).comp x (contDiff_chart n).contDiffAt

/-- Density-only regularizers contribute zero to the covariance Hessian column. -/
theorem horizontal_block_eq_source (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (m : ℕ) (θ κ : ℝ) (H : selfAdjoint (Matrix n n ℂ))
    (C : ℝ → selfAdjoint (Matrix ι ι ℝ)) (hC : ContDiff ℝ ∞ C)
    {p : ℝ × Coordinates n} (hCp : (C p.1 : Matrix ι ι ℝ).PosDef)
    (hSp : (chart n p.2 : Matrix n n ℂ).PosDef) (v : ℝ × Coordinates n) :
    second (objective A m θ κ H C) p v (1,0) =
      second (KSActualEnvelope.objective A 0 (fun _ => H) C) p v (1,0) := by
  have hf := objective_contDiffAt A hA m (θ := θ) (κ := κ) H C hC hCp hSp
  have hg := KSActualEnvelope.objective_contDiffAt A hA (θ := 0) (fun _ => H) C
    contDiff_const hC hCp hSp
  apply RectangularRidgeEnvelopeSecond.second_horizontal_eq_of_first
    (hf.of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)))
    (hg.of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)))
  have hpC : ∀ᶠ q : ℝ × Coordinates n in 𝓝 p, (C q.1 : Matrix ι ι ℝ).PosDef :=
    (hC.continuous.continuousAt.comp continuousAt_fst).eventually
      (eventually_real_posDef_of_posDef (C p.1) hCp)
  have hpS : ∀ᶠ q : ℝ × Coordinates n in 𝓝 p, (chart n q.2 : Matrix n n ℂ).PosDef :=
    ((contDiff_chart n).continuous.continuousAt.comp continuousAt_snd).eventually
      (eventually_posDef_of_posDef (chart n p.2) hSp)
  filter_upwards [hpC,hpS] with q hqC hqS
  have hgd : DifferentiableAt ℝ (KSActualEnvelope.objective A 0 (fun _ => H) C) q :=
    (KSActualEnvelope.objective_contDiffAt A hA (θ := 0) (fun _ => H) C
    contDiff_const hC hqC hqS).differentiableAt (by simp)
  have hrd : DifferentiableAt ℝ (fun q : ℝ × Coordinates n => regularizerChart (n := n) m θ κ q.2) q :=
    ((regularizerChart_contDiffAt m θ κ q.2 hqS).comp q contDiffAt_snd).differentiableAt (by simp)
  rw [objective_eq_source_add]
  change (fderiv ℝ (KSActualEnvelope.objective A 0 (fun _ => H) C +
    (fun q : ℝ × Coordinates n => regularizerChart m θ κ q.2)) q) (1,0) = _
  rw [fderiv_add hgd hrd, ContinuousLinearMap.add_apply,
    RectangularRidgeEnvelopeSecond.fderiv_snd_horizontal, add_zero]

/-- Actual optimizer and actual covariance column, with a source-only numerical bound. -/
theorem potential_second_le_source (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (m : ℕ) (hm : 1 ≤ m) {θ κ : ℝ} (hθ : 0 < θ) (hκ : 0 < κ)
    (H : selfAdjoint (Matrix n n ℂ)) (C : ℝ → selfAdjoint (Matrix ι ι ℝ))
    (hC : ContDiff ℝ ∞ C) {I : Set ℝ} (hI : IsOpen I)
    (hpositive : ∀ t ∈ I, (C t : Matrix ι ι ℝ).PosDef)
    {t B : ℝ} (ht : t ∈ I) (hB : 0 ≤ B)
    (hsource : KSActualEnvelope.secondNorm (KSActualEnvelope.objective A 0 (fun _ => H) C)
      (t,branch A m θ κ H C t) ≤ B) :
    |iteratedDeriv 2 (fun z => RectangularRidgeCovarianceCalculus.ownerPotential m H A (C z) θ κ) t| ≤
      B*(1+B/(κ/2)) := by
  have hs : ContDiffOn ℝ 4 (branch A m θ κ H C) I := by
    intro z hz
    exact ((branch_contDiffAt A hA m hm hθ hκ H C hC (hpositive z hz)).of_le
      (WithTop.coe_le_coe.mpr (show (4 : ℕ∞) ≤ ⊤ from le_top))).contDiffWithinAt
  have hf : ∀ z ∈ I, ContDiffAt ℝ 4 (objective A m θ κ H C)
      (lift (branch A m θ κ H C) z) := by
    intro z hz
    exact (objective_contDiffAt A hA m H C hC (hpositive z hz)
      (branch_posDef A m hm hθ hκ H C z)).of_le
      (WithTop.coe_le_coe.mpr (show (4 : ℕ∞) ≤ ⊤ from le_top))
  have hstat : ∀ z ∈ I, ∀ u : Coordinates n,
      fderiv ℝ (objective A m θ κ H C) (lift (branch A m θ κ H C) z) (0,u) = 0 :=
    fun z hz u => branch_stationary A hA m hm hθ hκ H C hC (hpositive z hz) u
  have hh := RectangularRidgeEnvelopeSecond.value_second_le_of_horizontal_block hI hs hf hstat ht
    (div_pos hκ (by norm_num)) hB
    (second (KSActualEnvelope.objective A 0 (fun _ => H) C) (t,branch A m θ κ H C t)) hsource
    (horizontal_block_eq_source A hA m θ κ H C hC (hpositive t ht)
      (branch_posDef A m hm hθ hκ H C t))
    (branch_coercive A hA m hm hθ hκ H C hC (hpositive t ht))
  have he : (fun z => objective A m θ κ H C (lift (branch A m θ κ H C) z)) =ᶠ[𝓝 t]
      (fun z => RectangularRidgeCovarianceCalculus.ownerPotential m H A (C z) θ κ) := by
    filter_upwards [hI.mem_nhds ht] with z hz
    exact value_eq A hA m hm H C (hpositive z hz)
  rwa [Filter.EventuallyEq.iteratedDeriv_eq 2 he] at hh

end MatrixSpencer.RectangularRidgeCovarianceCurvature
