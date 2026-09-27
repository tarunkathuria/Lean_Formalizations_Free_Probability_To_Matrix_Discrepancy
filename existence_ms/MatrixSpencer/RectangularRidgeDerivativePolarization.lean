import MatrixSpencer.RectangularRidgePolarization
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-! Adjacent symmetry for actual second-through-fourth Fréchet derivatives,
and the resulting dimension-free diagonal-to-operator-norm bounds. -/

open Filter
open scoped Topology ContDiff
noncomputable section
namespace MatrixSpencer.RectangularRidgeDerivativePolarization
open RectangularRidgePolarization
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
local instance ridgeDerivativePolarizationNormTwo : NormedAddCommGroup (Two (E:=E)) := inferInstance
local instance ridgeDerivativePolarizationSpaceTwo : NormedSpace ℝ (Two (E:=E)) := inferInstance
local instance ridgeDerivativePolarizationNormThree : NormedAddCommGroup (Three (E:=E)) := inferInstance
local instance ridgeDerivativePolarizationSpaceThree : NormedSpace ℝ (Three (E:=E)) := inferInstance
local instance ridgeDerivativePolarizationNormFour : NormedAddCommGroup (Four (E:=E)) := inferInstance

abbrev second (f : E → ℝ) := fderiv ℝ (fderiv ℝ f)
abbrev third (f : E → ℝ) := fderiv ℝ (second f)
abbrev fourth (f : E → ℝ) := fderiv ℝ (third f)

theorem fderiv_apply_const {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : E → E →L[ℝ] F} {x : E} (hg : DifferentiableAt ℝ g x) (u v : E) :
    fderiv ℝ (fun y => g y u) x v = fderiv ℝ g x v u := by
  rw [fderiv_clm_apply hg (differentiableAt_const u)]
  simp

theorem fderiv_apply_two {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : E → E →L[ℝ] E →L[ℝ] F} {x : E} (hg : DifferentiableAt ℝ g x) (u v w : E) :
    fderiv ℝ (fun y => g y u v) x w = fderiv ℝ g x w u v := by
  rw [fderiv_apply_const (hg.clm_apply (differentiableAt_const u))]
  rw [fderiv_apply_const hg]

theorem fderiv_apply_three {g : E → Three (E:=E)} {x : E}
    (hg : DifferentiableAt ℝ g x) (u v w z : E) :
    fderiv ℝ (fun y => g y u v w) x z = fderiv ℝ g x z u v w := by
  rw [fderiv_apply_const ((hg.clm_apply (differentiableAt_const u)).clm_apply (differentiableAt_const v))]
  rw [fderiv_apply_two hg]

variable {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 4 f x)
include hf

theorem second_symm (u v : E) : second f x u v = second f x v u :=
  (hf.isSymmSndFDerivAt (by norm_num)).eq u v

theorem third_symm12 (u v w : E) : third f x u v w = third f x v u w := by
  have h := ((hf.fderiv_right (by norm_num : (3:WithTop ℕ∞)+1≤4)).isSymmSndFDerivAt
    (by norm_num)).eq u v
  exact congrArg (fun L => L w) h

theorem third_symm23 (u v w : E) : third f x u v w = third f x u w v := by
  have hd : DifferentiableAt ℝ (second f) x :=
    ((hf.fderiv_right (by norm_num : (3:WithTop ℕ∞)+1≤4)).fderiv_right
      (by norm_num : (2:WithTop ℕ∞)+1≤3)).differentiableAt (by norm_num)
  have he : (fun y => second f y v w) =ᶠ[𝓝 x] (fun y => second f y w v) := by
    filter_upwards [hf.eventually (by norm_num)] with y hy
    exact second_symm hy v w
  have h := congrArg (fun L : E →L[ℝ] ℝ => L u) he.fderiv_eq
  simpa only [fderiv_apply_two hd] using h

theorem fourth_symm12 (u v w z : E) : fourth f x u v w z = fourth f x v u w z := by
  have h := (((hf.fderiv_right (by norm_num : (3:WithTop ℕ∞)+1≤4)).fderiv_right
    (by norm_num : (2:WithTop ℕ∞)+1≤3)).isSymmSndFDerivAt (by norm_num)).eq u v
  exact congrArg (fun L => L w z) h

theorem fourth_symm23 (u v w z : E) : fourth f x u v w z = fourth f x u w v z := by
  have hd : DifferentiableAt ℝ (third f) x :=
    (((hf.fderiv_right (by norm_num : (3:WithTop ℕ∞)+1≤4)).fderiv_right
      (by norm_num : (2:WithTop ℕ∞)+1≤3)).fderiv_right
      (by norm_num : (1:WithTop ℕ∞)+1≤2)).differentiableAt le_rfl
  have he : (fun y => third f y v w z) =ᶠ[𝓝 x] (fun y => third f y w v z) := by
    filter_upwards [hf.eventually (by norm_num)] with y hy
    exact third_symm12 hy v w z
  have h := congrArg (fun L : E →L[ℝ] ℝ => L u) he.fderiv_eq
  simpa only [fderiv_apply_three hd] using h

theorem fourth_symm34 (u v w z : E) : fourth f x u v w z = fourth f x u v z w := by
  have hd : DifferentiableAt ℝ (third f) x :=
    (((hf.fderiv_right (by norm_num : (3:WithTop ℕ∞)+1≤4)).fderiv_right
      (by norm_num : (2:WithTop ℕ∞)+1≤3)).fderiv_right
      (by norm_num : (1:WithTop ℕ∞)+1≤2)).differentiableAt le_rfl
  have he : (fun y => third f y v w z) =ᶠ[𝓝 x] (fun y => third f y v z w) := by
    filter_upwards [hf.eventually (by norm_num)] with y hy
    exact third_symm23 hy v w z
  have h := congrArg (fun L : E →L[ℝ] ℝ => L u) he.fderiv_eq
  simpa only [fderiv_apply_three hd] using h

theorem second_norm_le {C : ℝ} (hC : 0≤C) (hd : ∀ u, |second f x u u|≤C*‖u‖^2) :
    ‖second f x‖≤8*C :=
  second_norm_le_of_diagonal _ hC (second_symm hf) hd

theorem third_norm_le {C : ℝ} (hC : 0≤C) (hd : ∀ u, |third f x u u u|≤C*‖u‖^3) :
    ‖third f x‖≤54*C :=
  third_norm_le_of_diagonal _ hC (third_symm12 hf) (third_symm23 hf) hd

theorem fourth_norm_le {C : ℝ} (hC : 0≤C) (hd : ∀ u, |fourth f x u u u u|≤C*‖u‖^4) :
    ‖fourth f x‖≤256*C :=
  fourth_norm_le_of_diagonal _ hC (fourth_symm12 hf) (fourth_symm23 hf) (fourth_symm34 hf) hd

end MatrixSpencer.RectangularRidgeDerivativePolarization
