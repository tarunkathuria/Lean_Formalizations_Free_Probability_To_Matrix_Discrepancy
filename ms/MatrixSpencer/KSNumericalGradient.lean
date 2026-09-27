import MatrixSpencer.KSGradientQueryGeometry
import MatrixSpencer.KSNumericalOwnerObjective

/-!
# Numerical gradients from the actual finite objective report

The two objective calls in every matrix-unit direction are computed by the
certified real Jacobi routines. Their accuracy follows from the actual
density Hessian bound and an explicit floor-preserving scalar mesh.
-/

open Matrix Set Filter
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator Topology
noncomputable section
namespace MatrixSpencer.KSNumericalGradient

open KSHermitianDirections KSHermitianGradientReport KSGradientQueryGeometry
open KSFullHermitianChart KSObjectiveUpper
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}
local instance : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
local instance : NormedSpace ℝ (selfAdjoint (Matrix (Fin d) (Fin d) ℂ)) := inferInstance

def valueReport (H : Matrix (Fin d) (Fin d) ℂ) (A : ι → Matrix (Fin d) (Fin d) ℂ)
    (C : Matrix ι ι ℝ) (θ ν : ℝ) : Matrix (Fin d) (Fin d) ℂ → ℝ :=
  fun S => KSNumericalOwnerObjective.report H A C θ S ν

def reportAtMesh (H : Matrix (Fin d) (Fin d) ℂ) (A : ι → Matrix (Fin d) (Fin d) ℂ)
    (C : Matrix ι ι ℝ) (θ : ℝ) (S : Matrix (Fin d) (Fin d) ℂ) (t ν : ℝ) :
    Matrix (Fin d) (Fin d) ℂ := KSHermitianGradientReport.report (valueReport H A C θ ν) S t

/-- The queried curve has its stated half-floor and trace cap at every point. -/
theorem query_regular (S D : selfAdjoint (Matrix (Fin d) (Fin d) ℂ))
    {a t : ℝ} (ha : 0 < a) (hta : t ≤ a / 2) (htone : t ≤ 1)
    (hfloor : a • (1 : Matrix (Fin d) (Fin d) ℂ) ≤ (S : Matrix (Fin d) (Fin d) ℂ))
    (htrace : realTrace (S : Matrix (Fin d) (Fin d) ℂ) = 1)
    (henergy : realTrace ((D : Matrix (Fin d) (Fin d) ℂ) * (D : Matrix (Fin d) (Fin d) ℂ)) ≤ 1)
    (hDtrace : |realTrace (D : Matrix (Fin d) (Fin d) ℂ)| ≤ 1)
    (u : ℝ) (hu : u ∈ Icc (-t) t) :
    ((S + u • D : selfAdjoint (Matrix (Fin d) (Fin d) ℂ)) : Matrix (Fin d) (Fin d) ℂ).PosDef ∧
      (a / 2) • (1 : Matrix (Fin d) (Fin d) ℂ) ≤
        ((S + u • D : selfAdjoint (Matrix (Fin d) (Fin d) ℂ)) : Matrix (Fin d) (Fin d) ℂ) ∧
      realTrace ((S + u • D : selfAdjoint (Matrix (Fin d) (Fin d) ℂ)) :
        Matrix (Fin d) (Fin d) ℂ) ≤ 2 := by
  have huabs : |u| ≤ t := abs_le.mpr hu
  have hf := query_floor S D hfloor henergy huabs hta
  have hp := (Matrix.PosDef.one.smul (by linarith : 0 < a / 2)).add_posSemidef
    (Matrix.le_iff.mp hf)
  refine ⟨?_, hf, query_trace_le_two S D htrace hDtrace huabs htone⟩
  simpa only [add_sub_cancel] using hp

/-- Every actual two-query directional report has an error derived from
input budgets; no Taylor remainder or derivative bound is assumed. -/
theorem difference_accuracy (H : Matrix (Fin d) (Fin d) ℂ)
    (A : ι → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (θ : ℝ) (hθ : 0 < θ)
    (S D : selfAdjoint (Matrix (Fin d) (Fin d) ℂ)) {a κ t ν : ℝ}
    (ha : 0 < a) (hκ : 0 ≤ κ) (ht : 0 < t) (hν : 0 < ν)
    (hta : t ≤ a / 2) (htone : t ≤ 1)
    (hfloor : a • (1 : Matrix (Fin d) (Fin d) ℂ) ≤ (S : Matrix (Fin d) (Fin d) ℂ))
    (htrace : realTrace (S : Matrix (Fin d) (Fin d) ℂ) = 1)
    (henergy : realTrace ((D : Matrix (Fin d) (Fin d) ℂ) * (D : Matrix (Fin d) (Fin d) ℂ)) ≤ 1)
    (hDtrace : |realTrace (D : Matrix (Fin d) (Fin d) ℂ)| ≤ 1)
    (hbudget : (∑ i, (covarianceKraus A C i)ᴴ * covarianceKraus A C i) ≤
      κ • (1 : Matrix (Fin d) (Fin d) ℂ)) :
    |difference (valueReport H A C θ ν) S D t -
      fderiv ℝ (hermitianDensityObjective H (covarianceKraus A C) θ) S D| ≤
      upperCoefficient (n := Fin d) (a / 2) κ θ 2 * t / 2 + ν / t := by
  let f := hermitianDensityObjective H (covarianceKraus A C) θ
  let r := fun X : selfAdjoint (Matrix (Fin d) (Fin d) ℂ) => valueReport H A C θ ν X
  have hreg := query_regular S D ha hta htone hfloor htrace henergy hDtrace
  have hzero : (0 : ℝ) ∈ Icc (-t) t := ⟨by linarith, ht.le⟩
  have hf (u : ℝ) (hu : u ∈ Icc (-t) t) : ContDiffAt ℝ 2 f (S + u • D) :=
    (contDiffAt_hermitianDensityObjective_source_unrestricted H (covarianceKraus A C) θ
      (S + u • D) (hreg u hu).1).of_le
        (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have hcurve : ContDiffOn ℝ 2 (fun u : ℝ => f (S + u • D)) (Icc (-t) t) := by
    intro u hu
    have hline : ContDiffAt ℝ 2
        (fun u : ℝ => (S + u • D : selfAdjoint (Matrix (Fin d) (Fin d) ℂ))) u := by fun_prop
    exact ((hf u hu).comp u hline).contDiffWithinAt
  have hL : ∀ u ∈ Icc (-t) t,
      |iteratedDeriv 2 (fun w : ℝ => f (S + w • D)) u| ≤
        upperCoefficient (n := Fin d) (a / 2) κ θ 2 := by
    intro u hu
    rw [iteratedDeriv_two_affine_comp f S D u (hf u hu)]
    have hn := density_negativeHessian_nonneg H (covarianceKraus A C) θ hθ
      (S + u • D) D (hreg u hu).1
    have hb := density_negativeHessian_le_explicit H (covarianceKraus A C) θ hθ
      (S + u • D) D (hreg u hu).1 (by linarith : 0 < a / 2) hκ
      (hreg u hu).2.1 hbudget (hreg u hu).2.2
    have hcoef := upperCoefficient_nonneg (n := Fin d) (a := a / 2) (κ := κ) hθ.le
      (by norm_num : (0 : ℝ) ≤ 2)
    have hb' := hb.trans (mul_le_mul_of_nonneg_left henergy hcoef)
    change 0 ≤ -fderiv ℝ (fderiv ℝ f) (S + u • D) D D at hn
    change -fderiv ℝ (fderiv ℝ f) (S + u • D) D D ≤ _ at hb'
    rw [abs_of_nonpos (by linarith)]
    simpa only [mul_one] using hb'
  have hval (u : ℝ) (hu : u ∈ Icc (-t) t) : |r (S + u • D) - f (S + u • D)| ≤ ν := by
    have hv := KSNumericalOwnerObjective.report_accuracy H A hA hC θ (hreg u hu).1.posSemidef hν
    rwa [ownerObjective_eq_densityObjective H A hA hC θ] at hv
  have h := KSFirstDifference.directionalStencil_error f r S D ht hcurve hL
    (hval t ⟨by linarith, le_rfl⟩)
    (by simpa only [neg_smul, sub_eq_add_neg] using hval (-t) ⟨le_rfl, by linarith⟩)
  have hd := deriv_affine_comp f S D 0 ((hf 0 hzero).differentiableAt (by norm_num))
  simp only [zero_smul, add_zero] at hd
  rw [hd] at h
  exact h

def coefficient (a κ θ : ℝ) : ℝ := upperCoefficient (n := Fin d) (a / 2) κ θ 2
def entryTolerance (ε : ℝ) : ℝ := ε / (2 * ((d : ℝ) + 1))
def mesh (a κ θ ε : ℝ) : ℝ :=
  min (a / 2) (min 1 (entryTolerance (d := d) ε / (coefficient (d := d) a κ θ + 1)))
def valueTolerance (a κ θ ε : ℝ) : ℝ :=
  entryTolerance (d := d) ε * mesh (d := d) a κ θ ε / 2

/-- Every scalar parameter is a finite formula in the requested error and
the input floor/source budgets. -/
theorem mesh_parameters {a κ θ ε : ℝ} (ha : 0 < a) (hθ : 0 < θ) (hε : 0 < ε) :
    0 < mesh (d := d) a κ θ ε ∧ 0 < valueTolerance (d := d) a κ θ ε ∧
      mesh (d := d) a κ θ ε ≤ a / 2 ∧ mesh (d := d) a κ θ ε ≤ 1 ∧
      coefficient (d := d) a κ θ * mesh (d := d) a κ θ ε / 2 +
        valueTolerance (d := d) a κ θ ε / mesh (d := d) a κ θ ε ≤ entryTolerance (d := d) ε := by
  have hL : 0 ≤ coefficient (d := d) a κ θ :=
    upperCoefficient_nonneg hθ.le (by norm_num)
  have he : 0 < entryTolerance (d := d) ε := by unfold entryTolerance; positivity
  have ht : 0 < mesh (d := d) a κ θ ε := by unfold mesh; positivity
  have hta : mesh (d := d) a κ θ ε ≤ a / 2 := min_le_left _ _
  have htone : mesh (d := d) a κ θ ε ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have htd : mesh (d := d) a κ θ ε ≤
      entryTolerance (d := d) ε / (coefficient (d := d) a κ θ + 1) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hprod := (le_div_iff₀ (by linarith : 0 < coefficient (d := d) a κ θ + 1)).mp htd
  have hν : 0 < valueTolerance (d := d) a κ θ ε := by unfold valueTolerance; positivity
  have hquot : valueTolerance (d := d) a κ θ ε / mesh (d := d) a κ θ ε =
      entryTolerance (d := d) ε / 2 := by unfold valueTolerance; field_simp
  refine ⟨ht, hν, hta, htone, ?_⟩
  rw [hquot]
  nlinarith

def report (H : Matrix (Fin d) (Fin d) ℂ) (A : ι → Matrix (Fin d) (Fin d) ℂ)
    (C : Matrix ι ι ℝ) (θ : ℝ) (S : Matrix (Fin d) (Fin d) ℂ) (a κ ε : ℝ) :
    Matrix (Fin d) (Fin d) ℂ := reportAtMesh H A C θ S
      (mesh (d := d) a κ θ ε) (valueTolerance (d := d) a κ θ ε)

theorem report_isHermitian (H : Matrix (Fin d) (Fin d) ℂ)
    (A : ι → Matrix (Fin d) (Fin d) ℂ) (C : Matrix ι ι ℝ) (θ : ℝ)
    (S : Matrix (Fin d) (Fin d) ℂ) (a κ ε : ℝ) : (report H A C θ S a κ ε).IsHermitian :=
  KSHermitianGradientReport.report_isHermitian _ _ _

/-- The coordinate wrapper is for the proof; the actual calls use the
physical Hermitian entries and the explicit scalar tolerances above. -/
def coordinateReport (H : Matrix (Fin d) (Fin d) ℂ) (A : ι → Matrix (Fin d) (Fin d) ℂ)
    (C : Matrix ι ι ℝ) (θ a κ ε : ℝ) (_k : ℕ) (x : Coordinates (Fin d)) : Coordinates (Fin d) :=
  (chartEquiv (Fin d)).symm ⟨report H A C θ (chart (Fin d) x) a κ ε,
    report_isHermitian H A C θ (chart (Fin d) x) a κ ε⟩

/-- The numerical gradient error is discharged from the actual owner
input and floor budgets. There is no gradient-accuracy hypothesis. -/
theorem coordinateReport_accuracy (H : Matrix (Fin d) (Fin d) ℂ)
    (A : ι → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) {θ a κ ε : ℝ}
    (hθ : 0 < θ) (ha : 0 < a) (hκ : 0 ≤ κ) (hε : 0 < ε)
    (hbudget : (∑ i, (covarianceKraus A C i)ᴴ * covarianceKraus A C i) ≤
      κ • (1 : Matrix (Fin d) (Fin d) ℂ))
    (k : ℕ) (x : Coordinates (Fin d)) (hx : x ∈ KSObjectiveChart.densityFloor (chart (Fin d)) a) :
    ‖coordinateReport H A C θ a κ ε k x -
      gradient (KSObjectiveChart.objective H (covarianceKraus A C) θ (chart (Fin d))) x‖ ≤ ε := by
  let S := chart (Fin d) x
  let f := hermitianDensityObjective H (covarianceKraus A C) θ
  let g := KSObjectiveChart.objective H (covarianceKraus A C) θ (chart (Fin d))
  let t := mesh (d := d) a κ θ ε
  let ν := valueTolerance (d := d) a κ θ ε
  have hp := mesh_parameters (d := d) (κ := κ) ha hθ hε
  have hS : (S : Matrix (Fin d) (Fin d) ℂ).PosDef :=
    KSObjectiveChart.densityFloor_posDef (chart (Fin d)) ha hx
  have hf : DifferentiableAt ℝ f S :=
    (contDiffAt_hermitianDensityObjective_source_unrestricted H (covarianceKraus A C) θ S hS).differentiableAt
      (by simp)
  have hderiv (D : selfAdjoint (Matrix (Fin d) (Fin d) ℂ)) :
      fderiv ℝ g x ((chartEquiv (Fin d)).symm D) = fderiv ℝ f S D := by
    change fderiv ℝ (f ∘ chart (Fin d)) x ((chartEquiv (Fin d)).symm D) = _
    rw [fderiv_comp x hf (chart (Fin d)).differentiableAt, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.fderiv]
    congr 1
    exact (chartEquiv (Fin d)).apply_symm_apply D
  have hd (D : selfAdjoint (Matrix (Fin d) (Fin d) ℂ))
      (henergy : realTrace ((D : Matrix (Fin d) (Fin d) ℂ) * (D : Matrix (Fin d) (Fin d) ℂ)) ≤ 1)
      (hDtrace : |realTrace (D : Matrix (Fin d) (Fin d) ℂ)| ≤ 1) :
      |difference (valueReport H A C θ ν) S D t -
        fderiv ℝ g x ((chartEquiv (Fin d)).symm D)| ≤ entryTolerance (d := d) ε := by
    rw [hderiv]
    exact (difference_accuracy H A hA hC θ hθ S D ha hκ hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1
      hx.1 hx.2 henergy hDtrace hbudget).trans hp.2.2.2.2
  have hh := report_coordinate_error (valueReport H A C θ ν) S g x t
    (show 0 ≤ entryTolerance (d := d) ε by unfold entryTolerance; positivity)
    (fun i j => hd ⟨_, realDirection_isHermitian i j⟩
      (realDirection_trace_square_le i j) (realDirection_trace_abs_le i j))
    (fun i j => hd ⟨_, imagDirection_isHermitian i j⟩
      (imagDirection_trace_square_le i j) (imagDirection_trace_abs_le i j))
  change ‖coordinateReport H A C θ a κ ε k x - gradient g x‖ ≤ ε
  apply hh.trans
  simp only [Fintype.card_fin, entryTolerance]
  have hden : 0 < 2 * ((d : ℝ) + 1) := by positivity
  rw [← mul_div_assoc, div_le_iff₀ hden]
  nlinarith

end MatrixSpencer.KSNumericalGradient
