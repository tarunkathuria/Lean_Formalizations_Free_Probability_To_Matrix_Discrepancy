import MatrixSpencer.KSEighthTraceSource
import MatrixSpencer.KSInputJointBounds

/-!
# The eighth-cube joint objective and its actual optimizer branch

This instantiates the generic envelope with the independent two-block source.
The complex extension is identified with that same real objective. No full-cube
algorithm or compact-minimizer signing theorem is used.
-/

open Matrix Set Filter
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff Topology
noncomputable section
namespace MatrixSpencer.KSEighthAnalyticCurve

variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n] [Nonempty n]
local instance {k : Type*} [Fintype k] [DecidableEq k] : CStarAlgebra (Matrix k k ℂ) := {}
open KSEighthTraceSource KSActualEnvelope KSFrobeniusTangent

def H (Q : Matrix n n ℂ) (hQ : Q.IsHermitian) (v : ι → n → ℂ)
    (h : ι → ℝ) : ℝ → selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ) :=
  curveH (signedLift Q) (signedLift_isHermitian hQ) v h

def C (x h : ι → ℝ) (t : ℝ) : selfAdjoint (Matrix (ι × Bool) (ι × Bool) ℝ) :=
  KSEighthSmoothness.coefficientCovarianceCLM (KSEighthLocalState.curveOwners x h t)

def objective (Q : Matrix n n ℂ) (hQ : Q.IsHermitian) (v : ι → n → ℂ)
    (θ : ℝ) (x h : ι → ℝ) : ℝ × Coordinates (n ⊕ n) → ℝ :=
  KSActualEnvelope.objective (KSEighthActualState.family v) θ (H Q hQ v h) (C x h)

def branch (Q : Matrix n n ℂ) (hQ : Q.IsHermitian) (v : ι → n → ℂ)
    (θ : ℝ) (x h : ι → ℝ) : ℝ → Coordinates (n ⊕ n) :=
  KSActualEnvelope.branch (KSEighthActualState.family v) θ (H Q hQ v h) (C x h)

def density (Q : Matrix n n ℂ) (hQ : Q.IsHermitian) (v : ι → n → ℂ)
    (θ : ℝ) (x h : ι → ℝ) (t : ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℂ :=
  chart (n ⊕ n) (branch Q hQ v θ x h t)

def extension (Q : Matrix n n ℂ) (v : ι → n → ℂ) (θ : ℝ) (x h : ι → ℝ) :=
  KSComplexTraceObjective.objective (frame v) (signedLift Q)
    (KSComplexOwnerObjective.slope v h) (KSEighthActualState.family v) θ (owners x) (owners h)

theorem H_coe (Q : Matrix n n ℂ) (hQ : Q.IsHermitian) (v : ι → n → ℂ)
    (h : ι → ℝ) (t : ℝ) :
    (H Q hQ v h t : Matrix (n ⊕ n) (n ⊕ n) ℂ) = KSEighthLocalState.curveCenter Q v h t := rfl

theorem contDiff_H (Q : Matrix n n ℂ) (hQ : Q.IsHermitian) (v : ι → n → ℂ) (h : ι → ℝ) :
    ContDiff ℝ ∞ (H Q hQ v h) := contDiff_curveH _ _ _ _

theorem contDiff_C (x h : ι → ℝ) : ContDiff ℝ ∞ (C x h) :=
  (KSEighthSmoothness.coefficientCovarianceCLM (ι := ι)).contDiff.comp
    (KSEighthSmoothness.contDiff_curveOwners x h)

theorem density_posDef (Q : Matrix n n ℂ) (hQ : Q.IsHermitian) (v : ι → n → ℂ)
    {θ : ℝ} (hθ : 0 < θ) (x h : ι → ℝ) (t : ℝ) :
    (density Q hQ v θ x h t).PosDef := branch_posDef _ hθ _ _ _

theorem density_norm_le (Q : Matrix n n ℂ) (hQ : Q.IsHermitian) (v : ι → n → ℂ)
    {θ : ℝ} (hθ : 0 < θ) (x h : ι → ℝ) (t : ℝ) :
    ‖density Q hQ v θ x h t‖ ≤ 1 := by
  apply density_norm_le_one
  refine ⟨(density_posDef Q hQ v hθ x h t).posSemidef, ?_⟩
  unfold density branch
  rw [chart_branch]
  exact hermitianDensityOptimizer_trace _ _ θ

theorem extension_real (Q : Matrix n n ℂ) (hQ : Q.IsHermitian) (v : ι → n → ℂ)
    (θ : ℝ) (x h : ι → ℝ) (t : ℝ) (q : Coordinates (n ⊕ n))
    (hS : (chart (n ⊕ n) q : Matrix (n ⊕ n) (n ⊕ n) ℂ).PosDef)
    (hx : ∀ i, |x i+t*h i| < 1) :
    extension Q v θ x h ((t : ℂ),(chart (n ⊕ n) q : Matrix (n ⊕ n) (n ⊕ n) ℂ)) =
      (objective Q hQ v θ x h (t,q) : ℂ) := by
  rw [extension, KSComplexTraceObjective.objective_real (frame v) (frame_isometry v)
    (signedLift Q) (KSComplexOwnerObjective.slope v h) (signedLift_isHermitian hQ)
    (KSComplexOwnerObjective.slope_isHermitian v h) _ θ _ _ t hS
    (compressedSource_posDef v x h t hS hx) (source_reconstruct v x h t hS hx)]
  rw [source_real]
  rfl

theorem extension_eventuallyEq (Q : Matrix n n ℂ) (hQ : Q.IsHermitian) (v : ι → n → ℂ)
    (θ : ℝ) (x h : ι → ℝ) (t : ℝ) (q : Coordinates (n ⊕ n))
    (hS : (chart (n ⊕ n) q : Matrix (n ⊕ n) (n ⊕ n) ℂ).PosDef)
    (hx : ∀ i, |x i+t*h i| < 1) :
    (fun p : ℝ × Coordinates (n ⊕ n) =>
      (extension Q v θ x h ((p.1 : ℂ),(chart (n ⊕ n) p.2 : Matrix (n ⊕ n) (n ⊕ n) ℂ))).re)
      =ᶠ[𝓝 (t,q)] objective Q hQ v θ x h := by
  have hs : ∀ᶠ p : ℝ × Coordinates (n ⊕ n) in 𝓝 (t,q),
      (chart (n ⊕ n) p.2 : Matrix (n ⊕ n) (n ⊕ n) ℂ).PosDef := by
    have hc : ContinuousAt (fun p : ℝ × Coordinates (n ⊕ n) => chart (n ⊕ n) p.2) (t,q) :=
      ((contDiff_chart (n ⊕ n)).continuous.comp continuous_snd).continuousAt
    exact hc.eventually (eventually_posDef_of_posDef (chart (n ⊕ n) q) hS)
  have ho : ∀ i, ∀ᶠ p : ℝ × Coordinates (n ⊕ n) in 𝓝 (t,q), |x i+p.1*h i| < 1 := by
    intro i
    have hc : Continuous (fun p : ℝ × Coordinates (n ⊕ n) => |x i+p.1*h i|) := by fun_prop
    exact hc.continuousAt.eventually (eventually_lt_nhds (hx i))
  filter_upwards [hs, Filter.eventually_all.mpr ho] with p hp howners
  rw [extension_real Q hQ v θ x h p.1 p.2 hp howners, Complex.ofReal_re]

theorem curvePotential_fourth_le (Q : Matrix n n ℂ) (hQ : Q.IsHermitian)
    (v : ι → n → ℂ) {θ : ℝ} (hθ : 0 < θ) (x h : ι → ℝ)
    {I : Set ℝ} (hI : IsOpen I) (hpos : ∀ t ∈ I, ∀ i, |x i+t*h i| < 1)
    {t B : ℝ} (ht : t ∈ I) (hB : 0 ≤ B)
    (h₂ : secondNorm (objective Q hQ v θ x h) (t,branch Q hQ v θ x h t) ≤ B)
    (h₃ : thirdNorm (objective Q hQ v θ x h) (t,branch Q hQ v θ x h t) ≤ B)
    (h₄ : fourthNorm (objective Q hQ v θ x h) (t,branch Q hQ v θ x h t) ≤ B) :
    |iteratedDeriv 4 (KSEighthLocalState.curvePotential Q v θ x h) t| ≤
      (B + 3*B^2/(θ/2)) * (1+B/(θ/2))^4 := by
  exact potential_fourth_le _ (KSEighthActualState.family_isHermitian v) hθ
    (H Q hQ v h) (C x h) (contDiff_H Q hQ v h) (contDiff_C x h) hI
    (fun z hz => coefficient_posDef x h z (hpos z hz)) ht hB h₂ h₃ h₄

end MatrixSpencer.KSEighthAnalyticCurve
