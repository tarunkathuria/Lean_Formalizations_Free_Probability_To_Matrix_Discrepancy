import MatrixSpencer.RectangularRidgeCenterCurvature
import MatrixSpencer.KSGradientQueryGeometry

/-! The actual supporting tangent of the mixed potential can be evaluated
by two accurate convex-value queries. Its Taylor error and step/tolerance
formulas are explicit; an exact optimizer is not queried by this procedure. -/

open Matrix Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
noncomputable section
namespace MatrixSpencer.RectangularRidgeTangentValues
open RectangularRidgeCalculus KSGradientQueryGeometry
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n] [Nonempty n]
local instance ridgeTangentValuesCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance ridgeTangentValuesRealSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance

def curvature (κ R : ℝ) : ℝ := (2/κ)*R^2
def spacing (κ R ε : ℝ) : ℝ := ε/(6*(curvature κ R+1))
def precision (κ R ε : ℝ) : ℝ := ε*spacing κ R ε/6

theorem curvature_nonneg {κ R : ℝ} (hκ : 0<κ) : 0≤curvature κ R := by
  unfold curvature
  positivity

theorem spacing_pos {κ R ε : ℝ} (hκ : 0<κ) (hε : 0<ε) : 0<spacing κ R ε := by
  have := curvature_nonneg (R:=R) hκ
  unfold spacing
  positivity

theorem precision_pos {κ R ε : ℝ} (hκ : 0<κ) (hε : 0<ε) : 0<precision κ R ε := by
  have := spacing_pos (R:=R) hκ hε
  unfold precision
  positivity

theorem line_contDiff (H X : selfAdjoint (Matrix n n ℂ)) (B : ι → Matrix n n ℂ)
    (m : ℕ) (hm : 1≤m) {θ κ : ℝ} (hθ : 0<θ) (hκ : 0<κ) :
    ContDiff ℝ 2 (fun t : ℝ => hermitianPotential B m θ κ (H+t • X)) := by
  have hf : ContDiff ℝ 2 (hermitianPotential B m θ κ) := by
    apply contDiff_iff_contDiffAt.mpr
    intro K
    exact (contDiffAt_hermitianPotential K B m hm θ κ hθ hκ).of_le
      (WithTop.coe_le_coe.mpr (show (2:ℕ∞)≤⊤ from le_top))
  exact hf.comp (contDiff_const.add (contDiff_id.smul contDiff_const))

theorem line_deriv (H X : selfAdjoint (Matrix n n ℂ)) (B : ι → Matrix n n ℂ)
    (m : ℕ) (hm : 1≤m) {θ κ : ℝ} (hθ : 0<θ) (hκ : 0<κ) :
    deriv (fun t : ℝ => hermitianPotential B m θ κ (H+t • X)) 0 =
      realTrace (RectangularRidgePotential.optimizer (H : Matrix n n ℂ) B m θ κ*(X : Matrix n n ℂ)) := by
  rw [deriv_affine_comp]
  · simp only [zero_smul, add_zero]
    rw [(hasFDerivAt_hermitianPotential H B m hm θ κ hθ hκ).fderiv]
    rfl
  · exact (hasFDerivAt_hermitianPotential _ B m hm θ κ hθ hκ).differentiableAt

theorem line_second_bound (H X : selfAdjoint (Matrix n n ℂ)) (B : ι → Matrix n n ℂ)
    (m : ℕ) (hm : 1≤m) {θ κ R : ℝ} (hθ : 0<θ) (hκ : 0<κ) (hR : 0≤R)
    (hX : Real.sqrt (realTrace ((X : Matrix n n ℂ)*(X : Matrix n n ℂ)))≤R) (u : ℝ) :
    |iteratedDeriv 2 (fun t : ℝ => hermitianPotential B m θ κ (H+t • X)) u|≤curvature κ R := by
  rw [iteratedDeriv_two_affine_comp]
  · exact RectangularRidgeCenterCurvature.potential_hessian_abs_le (H+u • X) X B m hm hθ hκ hR hX
  · exact (contDiffAt_hermitianPotential _ B m hm θ κ hθ hκ).of_le
      (WithTop.coe_le_coe.mpr (show (2:ℕ∞)≤⊤ from le_top))

def report (value : selfAdjoint (Matrix n n ℂ) → ℝ) (H X : selfAdjoint (Matrix n n ℂ))
    (κ R ε : ℝ) : ℝ := KSFirstDifference.directionalStencil value H X (spacing κ R ε)

/-- Only the two convex solver value errors are hypotheses. Smoothness,
curvature and Taylor remainder for the actual optimized potential are proved. -/
theorem report_accuracy (H X : selfAdjoint (Matrix n n ℂ)) (B : ι → Matrix n n ℂ)
    (m : ℕ) (hm : 1≤m) {θ κ R ε : ℝ} (hθ : 0<θ) (hκ : 0<κ) (hR : 0≤R) (hε : 0<ε)
    (hX : Real.sqrt (realTrace ((X : Matrix n n ℂ)*(X : Matrix n n ℂ)))≤R)
    (value : selfAdjoint (Matrix n n ℂ) → ℝ)
    (hp : |value (H+spacing κ R ε • X)-hermitianPotential B m θ κ (H+spacing κ R ε • X)|≤precision κ R ε)
    (hn : |value (H-spacing κ R ε • X)-hermitianPotential B m θ κ (H-spacing κ R ε • X)|≤precision κ R ε) :
    |report value H X κ R ε-
      realTrace (RectangularRidgePotential.optimizer (H : Matrix n n ℂ) B m θ κ*(X : Matrix n n ℂ))|≤ε/3 := by
  have hb := KSFirstDifference.directionalStencil_error (hermitianPotential B m θ κ) value H X
    (spacing_pos (R:=R) hκ hε) (line_contDiff H X B m hm hθ hκ).contDiffOn
    (fun u _ => line_second_bound H X B m hm hθ hκ hR hX u) hp hn
  rw [line_deriv H X B m hm hθ hκ] at hb
  apply hb.trans
  have hc := curvature_nonneg (R:=R) hκ
  have hs := spacing_pos (R:=R) hκ hε
  have he : precision κ R ε/spacing κ R ε=ε/6 := by unfold precision; field_simp
  rw [he]
  have ht : curvature κ R*spacing κ R ε≤ε/3 := by
    unfold spacing
    rw [← mul_div_assoc, div_le_iff₀ (by positivity : 0<6*(curvature κ R+1))]
    nlinarith
  linarith

end MatrixSpencer.RectangularRidgeTangentValues
