import MatrixSpencer.MSManuscriptComplexValueBound
import MatrixSpencer.KSComplexEnvelopeChart
import MatrixSpencer.KSActualEnvelope



open Matrix Set Filter Metric
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff Topology
noncomputable section
namespace MatrixSpencer.MSManuscriptAffineJointBounds
open KSFrobeniusTangent MSManuscriptComplexSourceDomain

section NormTransfer
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
local instance : NormedAddCommGroup ((ℝ × E) →L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ ((ℝ × E) →L[ℝ] ℝ) := inferInstance
local instance : NormedAddCommGroup ((ℝ × E) →L[ℝ] (ℝ × E) →L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ ((ℝ × E) →L[ℝ] (ℝ × E) →L[ℝ] ℝ) := inferInstance
local instance : NormedAddCommGroup ((ℝ × E) →L[ℝ] (ℝ × E) →L[ℝ] (ℝ × E) →L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ ((ℝ × E) →L[ℝ] (ℝ × E) →L[ℝ] (ℝ × E) →L[ℝ] ℝ) := inferInstance

theorem nested_bounds {F : (ℝ × E) → ℝ} {p : ℝ × E} {B : ℝ}
    (hb : ∀ k : ℕ, 2 ≤ k → k ≤ 4 → ‖iteratedFDeriv ℝ k F p‖ ≤ B) :
    KSActualEnvelope.secondNorm F p ≤ B ∧ KSActualEnvelope.thirdNorm F p ≤ B ∧
      KSActualEnvelope.fourthNorm F p ≤ B := by
  have h2 := hb 2 (by norm_num) (by norm_num)
  have h3 := hb 3 (by norm_num) (by norm_num)
  have h4 := hb 4 (by norm_num) (by norm_num)
  rw [← norm_iteratedFDeriv_fderiv (n := 1), ← norm_iteratedFDeriv_fderiv (n := 0),
    norm_iteratedFDeriv_zero] at h2
  rw [← norm_iteratedFDeriv_fderiv (n := 2), ← norm_iteratedFDeriv_fderiv (n := 1),
    ← norm_iteratedFDeriv_fderiv (n := 0), norm_iteratedFDeriv_zero] at h3
  rw [← norm_iteratedFDeriv_fderiv (n := 3), ← norm_iteratedFDeriv_fderiv (n := 2),
    ← norm_iteratedFDeriv_fderiv (n := 1), ← norm_iteratedFDeriv_fderiv (n := 0),
    norm_iteratedFDeriv_zero] at h4
  exact ⟨h2,h3,h4⟩
end NormTransfer
variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
local instance {k : Type*} [Fintype k] [DecidableEq k] : CStarAlgebra (Matrix k k ℂ) := {}
set_option maxHeartbeats 1000000

abbrev RealSpace (n : Type*) [Fintype n] [DecidableEq n] := ℝ × Coordinates n

local instance : NormedAddCommGroup (Coordinates n) := inferInstance
local instance : NormedSpace ℝ (Coordinates n) := inferInstance
local instance : NormedAddCommGroup (RealSpace n) := inferInstance
local instance : NormedSpace ℝ (RealSpace n) := inferInstance
local instance : NormedAddCommGroup (MSManuscriptComplexObjective.Space ι n) := inferInstance
local instance : NormedSpace ℂ (MSManuscriptComplexObjective.Space ι n) := inferInstance
local instance : NormedSpace ℝ (MSManuscriptComplexObjective.Space ι n) := inferInstance
local instance : IsScalarTower ℝ ℂ (MSManuscriptComplexObjective.Space ι n) := inferInstance

def covariance (C D : selfAdjoint (Matrix ι ι ℝ)) (t : ℝ) : selfAdjoint (Matrix ι ι ℝ) :=
  C+t•D

theorem contDiff_covariance (C D : selfAdjoint (Matrix ι ι ℝ)) : ContDiff ℝ ∞ (covariance C D) :=
  contDiff_const.add (contDiff_id.smul contDiff_const)

def coefficientEmbedding (D : Matrix ι ι ℝ) : ℝ →L[ℝ] Matrix ι ι ℂ :=
  ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) (realMatrixEmbedding D)

def jointEmbedding (D : Matrix ι ι ℝ) : RealSpace n →L[ℝ] MSManuscriptComplexObjective.Space ι n :=
  (coefficientEmbedding D).prodMap (KSComplexEnvelopeChart.densityEmbedding n)

theorem jointEmbedding_norm_le (D : Matrix ι ι ℝ) (hD : ‖realMatrixEmbedding D‖ ≤ 1) :
    ‖jointEmbedding (n := n) D‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  change max ‖z.1 • realMatrixEmbedding D‖ ‖KSComplexEnvelopeChart.densityEmbedding n z.2‖ ≤ 1*‖z‖
  rw [one_mul,norm_smul]
  apply max_le_max _ (KSComplexEnvelopeChart.densityEmbedding_apply_norm_le n z.2)
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hD (norm_nonneg z.1)

variable [Nonempty n]

def base (C : Matrix ι ι ℝ) : MSManuscriptComplexObjective.Space ι n :=
  (realMatrixEmbedding C,(center n : Matrix n n ℂ))

theorem realEmbedding_smul (t : ℝ) (D : Matrix ι ι ℝ) :
    realMatrixEmbedding (t•D)=t•realMatrixEmbedding D := by
  ext i j
  simp only [realMatrixEmbedding_apply,Matrix.smul_apply,smul_eq_mul,Complex.ofReal_mul]
  rfl

theorem base_add_jointEmbedding (C D : selfAdjoint (Matrix ι ι ℝ)) (z : RealSpace n) :
    base (n := n) C + jointEmbedding D z =
      (realMatrixEmbedding (covariance C D z.1 : Matrix ι ι ℝ),(chart n z.2 : Matrix n n ℂ)) := by
  apply Prod.ext
  · change realMatrixEmbedding (C : Matrix ι ι ℝ)+z.1•realMatrixEmbedding (D : Matrix ι ι ℝ) = _
    change realMatrixEmbedding (C : Matrix ι ι ℝ)+z.1•realMatrixEmbedding (D : Matrix ι ι ℝ) =
      realMatrixEmbedding ((C : Matrix ι ι ℝ)+z.1•(D : Matrix ι ι ℝ))
    rw [map_add,realEmbedding_smul]
  · rfl

def jointCap (ι n : Type*) [Fintype ι] [Fintype n] (R θ γ μ : ℝ) : ℝ :=
  MSManuscriptComplexValueBound.valueCap ι n R θ*(10/radius γ μ)^4

/-- A specialized chart bridge keeps the large actual objective opaque while
transporting the Cauchy estimate; the linear chart is an explicit contraction. -/
theorem chart_derivatives_le_common_cap (F : MSManuscriptComplexObjective.Space ι n → ℂ)
    (C D : Matrix ι ι ℝ) (hD : ‖realMatrixEmbedding D‖ ≤ 1)
    {p : RealSpace n} {r K : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hK : 0 ≤ K)
    (hF : ContDiffOn ℂ ∞ F (ball (base C+jointEmbedding D p) r))
    (hbound : ∀ y ∈ ball (base C+jointEmbedding D p) r, ‖F y‖ ≤ K) :
    ∀ k : ℕ, 2 ≤ k → k ≤ 4 →
      ‖iteratedFDeriv ℝ k (fun z : RealSpace n => (F (base C+jointEmbedding D z)).re) p‖ ≤ K*(10/r)^4 := by
  simpa only [Complex.reCLM_apply] using
    KSCauchyRealBridge.real_affine_chart_derivatives_le_common_cap
      (base (n := n) C) (jointEmbedding (n := n) D) Complex.reCLM hr hr1 hK
      (jointEmbedding_norm_le D hD) KSComplexEnvelopeChart.realPart_norm_le hF hbound

/-- The exact actual objective agrees locally with the complex affine chart. -/
theorem eventuallyEq_objective (H : selfAdjoint (Matrix n n ℂ))
    (A : ι → Matrix n n ℂ) (hA : ∀i, (A i).IsHermitian) (θ : ℝ)
    (C D : selfAdjoint (Matrix ι ι ℝ)) {p : RealSpace n}
    (hC : (covariance C D p.1 : Matrix ι ι ℝ).PosDef)
    (hS : (chart n p.2 : Matrix n n ℂ).PosDef) :
    (fun z : RealSpace n => (MSManuscriptComplexObjective.objective H A θ
      (base C+jointEmbedding D z)).re) =ᶠ[𝓝 p]
      KSActualEnvelope.objective A θ (fun _ => H) (covariance C D) := by
  have hc : ContinuousAt (fun z : RealSpace n => covariance C D z.1) p :=
    (contDiff_covariance C D).continuous.continuousAt.comp continuousAt_fst
  have hs : ContinuousAt (fun z : RealSpace n => chart n z.2) p :=
    (contDiff_chart n).continuous.continuousAt.comp continuousAt_snd
  filter_upwards [hc.eventually (eventually_real_posDef_of_posDef (covariance C D p.1) hC),
    hs.eventually (eventually_posDef_of_posDef (chart n p.2) hS)] with z hzC hzS
  have hH : (H : Matrix n n ℂ).IsHermitian := H.property
  rw [base_add_jointEmbedding,MSManuscriptComplexObjective.objective_real (H : Matrix n n ℂ) hH A hA θ hzC hzS]
  rfl

/-- Actual multilinear derivative bounds, on the original real objective. -/
theorem iterated_bounds (H : selfAdjoint (Matrix n n ℂ))
    (A : ι → Matrix n n ℂ) (hA : ∀i, (A i).IsHermitian) (hAnorm : ∀i, ‖A i‖ ≤ 1)
    (C D : selfAdjoint (Matrix ι ι ℝ)) (hD : ‖realMatrixEmbedding (D : Matrix ι ι ℝ)‖ ≤ 1)
    {θ R γ μ : ℝ} (hθ : 0 ≤ θ) (hR : 0 ≤ R) (hH : ‖(H : Matrix n n ℂ)‖ ≤ R)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hμ : 0 < μ) (hμ1 : μ ≤ 1) {p : RealSpace n}
    (hC : γ • (1 : Matrix ι ι ℝ) ≤ (covariance C D p.1 : Matrix ι ι ℝ))
    (hC1 : (covariance C D p.1 : Matrix ι ι ℝ) ≤ 1)
    (hS : μ • (1 : Matrix n n ℂ) ≤ (chart n p.2 : Matrix n n ℂ))
    (hS1 : ‖(chart n p.2 : Matrix n n ℂ)‖ ≤ 1) :
    ∀ k : ℕ, 2 ≤ k → k ≤ 4 →
      ‖iteratedFDeriv ℝ k (KSActualEnvelope.objective A θ (fun _ => H) (covariance C D)) p‖ ≤
        jointCap ι n R θ γ μ := by
  have hCp : (covariance C D p.1 : Matrix ι ι ℝ).PosDef := by
    simpa only [add_sub_cancel] using (Matrix.PosDef.one.smul hγ).add_posSemidef (Matrix.le_iff.mp hC)
  have hSp : (chart n p.2 : Matrix n n ℂ).PosDef := by
    simpa only [add_sub_cancel] using (Matrix.PosDef.one.smul hμ).add_posSemidef (Matrix.le_iff.mp hS)
  have hcont := MSManuscriptComplexObjective.contDiffOn_objective (H : Matrix n n ℂ) A hA θ
    hγ hγ1 hμ hμ1 hC hS
  have hb := MSManuscriptComplexValueBound.objective_norm_le_on_ball (H : Matrix n n ℂ) A hA hAnorm
    hθ hR hH hγ hγ1 hμ hμ1 hC hC1 hS hS1
  rw [← base_add_jointEmbedding C D p] at hcont hb
  have hh := chart_derivatives_le_common_cap
    (MSManuscriptComplexObjective.objective (H : Matrix n n ℂ) A θ) C D hD
    (radius_pos hγ hμ) (MSManuscriptComplexValueBound.radius_le_one hγ hγ1 hμ hμ1)
    (MSManuscriptComplexValueBound.valueCap_nonneg (ι := ι) (n := n) hR hθ) hcont hb
  have he := eventuallyEq_objective H A hA θ C D hCp hSp
  intro k hk2 hk4
  rw [← (he.iteratedFDeriv ℝ k).self_of_nhds]
  exact hh k hk2 hk4

/-- The nested Fréchet derivative norms consumed by the actual optimizer
response and fourth-order envelope theorems. Every bound is discharged. -/
theorem joint_bounds (H : selfAdjoint (Matrix n n ℂ))
    (A : ι → Matrix n n ℂ) (hA : ∀i, (A i).IsHermitian) (hAnorm : ∀i, ‖A i‖ ≤ 1)
    (C D : selfAdjoint (Matrix ι ι ℝ)) (hD : ‖realMatrixEmbedding (D : Matrix ι ι ℝ)‖ ≤ 1)
    {θ R γ μ : ℝ} (hθ : 0 ≤ θ) (hR : 0 ≤ R) (hH : ‖(H : Matrix n n ℂ)‖ ≤ R)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hμ : 0 < μ) (hμ1 : μ ≤ 1) {p : RealSpace n}
    (hC : γ • (1 : Matrix ι ι ℝ) ≤ (covariance C D p.1 : Matrix ι ι ℝ))
    (hC1 : (covariance C D p.1 : Matrix ι ι ℝ) ≤ 1)
    (hS : μ • (1 : Matrix n n ℂ) ≤ (chart n p.2 : Matrix n n ℂ))
    (hS1 : ‖(chart n p.2 : Matrix n n ℂ)‖ ≤ 1) :
    let F := KSActualEnvelope.objective A θ (fun _ => H) (covariance C D)
    KSActualEnvelope.secondNorm F p ≤ jointCap ι n R θ γ μ ∧
    KSActualEnvelope.thirdNorm F p ≤ jointCap ι n R θ γ μ ∧
    KSActualEnvelope.fourthNorm F p ≤ jointCap ι n R θ γ μ := by
  have hb := iterated_bounds H A hA hAnorm C D hD hθ hR hH hγ hγ1 hμ hμ1 hC hC1 hS hS1
  exact nested_bounds hb

end MatrixSpencer.MSManuscriptAffineJointBounds
