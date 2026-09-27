import MatrixSpencer.RectangularRidgeDerivativePolarization
import MatrixSpencer.RectangularRidgeUnitPolarization
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! Actual affine-line derivatives equal the diagonal of actual nested
Fréchet derivatives. Together with polarization, actual one-dimensional
Taylor bounds control the full second, third and fourth derivative norms. -/

open Filter
open scoped Topology ContDiff
noncomputable section
namespace MatrixSpencer.RectangularRidgeLineDerivativeBridge
open RectangularRidgePolarization RectangularRidgeDerivativePolarization
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
local instance ridgeLineBridgeNormTwo : NormedAddCommGroup (Two (E:=E)) := inferInstance
local instance ridgeLineBridgeSpaceTwo : NormedSpace ℝ (Two (E:=E)) := inferInstance
local instance ridgeLineBridgeNormThree : NormedAddCommGroup (Three (E:=E)) := inferInstance
local instance ridgeLineBridgeSpaceThree : NormedSpace ℝ (Three (E:=E)) := inferInstance
local instance ridgeLineBridgeNormFour : NormedAddCommGroup (Four (E:=E)) := inferInstance

def point (x u : E) (t : ℝ) : E := x+t • u

theorem hasDerivAt_point (x u : E) (t : ℝ) : HasDerivAt (point x u) u t := by
  simpa only [point, zero_add, one_smul] using
    (hasDerivAt_const t x).add ((hasDerivAt_id t).smul_const u)

theorem smooth_eventually {f : E → ℝ} {x u : E} {t : ℝ}
    (hf : ContDiffAt ℝ 4 f (point x u t)) :
    ∀ᶠ z in 𝓝 t, ContDiffAt ℝ 4 f (point x u z) :=
  (hasDerivAt_point x u t).continuousAt.tendsto.eventually (hf.eventually (by norm_num))

theorem first_line {f : E → ℝ} {x u : E} {t : ℝ}
    (hf : ContDiffAt ℝ 4 f (point x u t)) :
    deriv (fun z => f (point x u z)) t = fderiv ℝ f (point x u t) u :=
  (((hf.differentiableAt (by norm_num)).hasFDerivAt).comp_hasDerivAt t
    (hasDerivAt_point x u t)).deriv

theorem second_line {f : E → ℝ} {x u : E} {t : ℝ}
    (hf : ContDiffAt ℝ 4 f (point x u t)) :
    iteratedDeriv 2 (fun z => f (point x u z)) t = second f (point x u t) u u := by
  have he : deriv (fun z => f (point x u z)) =ᶠ[𝓝 t]
      (fun z => fderiv ℝ f (point x u z) u) := by
    filter_upwards [smooth_eventually hf] with z hz
    exact first_line hz
  have hd := (((hf.fderiv_right (by norm_num : (3:WithTop ℕ∞)+1≤4)).differentiableAt
    (by norm_num)).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_point x u t)).clm_apply
      (hasDerivAt_const t u)
  rw [show (2:ℕ)=1+1 by omega, iteratedDeriv_succ, iteratedDeriv_one, he.deriv_eq]
  simpa only [map_zero, add_zero] using hd.deriv

theorem third_line {f : E → ℝ} {x u : E} {t : ℝ}
    (hf : ContDiffAt ℝ 4 f (point x u t)) :
    iteratedDeriv 3 (fun z => f (point x u z)) t = third f (point x u t) u u u := by
  have he : iteratedDeriv 2 (fun z => f (point x u z)) =ᶠ[𝓝 t]
      (fun z => second f (point x u z) u u) := by
    filter_upwards [smooth_eventually hf] with z hz
    exact second_line hz
  have hd := ((((hf.fderiv_right (by norm_num : (3:WithTop ℕ∞)+1≤4)).fderiv_right
    (by norm_num : (2:WithTop ℕ∞)+1≤3)).differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt
      t (hasDerivAt_point x u t))
  have h := (hd.clm_apply (hasDerivAt_const t u)).clm_apply (hasDerivAt_const t u)
  rw [show (3:ℕ)=2+1 by omega, iteratedDeriv_succ, he.deriv_eq]
  simpa only [ContinuousLinearMap.add_apply, map_zero, add_zero] using h.deriv

theorem fourth_line {f : E → ℝ} {x u : E} {t : ℝ}
    (hf : ContDiffAt ℝ 4 f (point x u t)) :
    iteratedDeriv 4 (fun z => f (point x u z)) t = fourth f (point x u t) u u u u := by
  have he : iteratedDeriv 3 (fun z => f (point x u z)) =ᶠ[𝓝 t]
      (fun z => third f (point x u z) u u u) := by
    filter_upwards [smooth_eventually hf] with z hz
    exact third_line hz
  have hd := (((((hf.fderiv_right (by norm_num : (3:WithTop ℕ∞)+1≤4)).fderiv_right
    (by norm_num : (2:WithTop ℕ∞)+1≤3)).fderiv_right
      (by norm_num : (1:WithTop ℕ∞)+1≤2)).differentiableAt le_rfl).hasFDerivAt.comp_hasDerivAt
      t (hasDerivAt_point x u t))
  have h := ((hd.clm_apply (hasDerivAt_const t u)).clm_apply (hasDerivAt_const t u)).clm_apply
    (hasDerivAt_const t u)
  conv_lhs => rw [show (4:ℕ)=3+1 by omega, iteratedDeriv_succ]
  rw [he.deriv_eq]
  simpa only [ContinuousLinearMap.add_apply, map_zero, add_zero] using h.deriv

theorem second_norm_le {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 4 f x)
    {C : ℝ} (hC : 0≤C)
    (hline : ∀ u, |iteratedDeriv 2 (fun t : ℝ => f (x+t • u)) 0|≤C*‖u‖^2) :
    ‖second f x‖≤8*C := by
  apply RectangularRidgeDerivativePolarization.second_norm_le hf hC
  intro u
  have he := second_line (x:=x) (u:=u) (t:=0) (by simpa [point] using hf)
  simp only [point, zero_smul, add_zero] at he
  rw [← he]
  exact hline u

theorem third_norm_le {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 4 f x)
    {C : ℝ} (hC : 0≤C)
    (hline : ∀ u, |iteratedDeriv 3 (fun t : ℝ => f (x+t • u)) 0|≤C*‖u‖^3) :
    ‖third f x‖≤54*C := by
  apply RectangularRidgeDerivativePolarization.third_norm_le hf hC
  intro u
  have he := third_line (x:=x) (u:=u) (t:=0) (by simpa [point] using hf)
  simp only [point, zero_smul, add_zero] at he
  rw [← he]
  exact hline u

theorem fourth_norm_le {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 4 f x)
    {C : ℝ} (hC : 0≤C)
    (hline : ∀ u, |iteratedDeriv 4 (fun t : ℝ => f (x+t • u)) 0|≤C*‖u‖^4) :
    ‖fourth f x‖≤256*C := by
  apply RectangularRidgeDerivativePolarization.fourth_norm_le hf hC
  intro u
  have he := fourth_line (x:=x) (u:=u) (t:=0) (by simpa [point] using hf)
  simp only [point, zero_smul, add_zero] at he
  rw [← he]
  exact hline u

theorem second_norm_le_unit {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 4 f x)
    {C : ℝ} (hC : 0≤C)
    (hline : ∀ u, ‖u‖≤1 → |iteratedDeriv 2 (fun t : ℝ => f (x+t • u)) 0|≤C) :
    ‖second f x‖≤8*C := by
  apply RectangularRidgeUnitPolarization.second_norm_le hf hC
  intro u hu
  have he := second_line (x:=x) (u:=u) (t:=0) (by simpa [point] using hf)
  simp only [point, zero_smul, add_zero] at he
  rw [← he]
  exact hline u hu

theorem third_norm_le_unit {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 4 f x)
    {C : ℝ} (hC : 0≤C)
    (hline : ∀ u, ‖u‖≤1 → |iteratedDeriv 3 (fun t : ℝ => f (x+t • u)) 0|≤C) :
    ‖third f x‖≤54*C := by
  apply RectangularRidgeUnitPolarization.third_norm_le hf hC
  intro u hu
  have he := third_line (x:=x) (u:=u) (t:=0) (by simpa [point] using hf)
  simp only [point, zero_smul, add_zero] at he
  rw [← he]
  exact hline u hu

theorem fourth_norm_le_unit {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 4 f x)
    {C : ℝ} (hC : 0≤C)
    (hline : ∀ u, ‖u‖≤1 → |iteratedDeriv 4 (fun t : ℝ => f (x+t • u)) 0|≤C) :
    ‖fourth f x‖≤256*C := by
  apply RectangularRidgeUnitPolarization.fourth_norm_le hf hC
  intro u hu
  have he := fourth_line (x:=x) (u:=u) (t:=0) (by simpa [point] using hf)
  simp only [point, zero_smul, add_zero] at he
  rw [← he]
  exact hline u hu

end MatrixSpencer.RectangularRidgeLineDerivativeBridge
