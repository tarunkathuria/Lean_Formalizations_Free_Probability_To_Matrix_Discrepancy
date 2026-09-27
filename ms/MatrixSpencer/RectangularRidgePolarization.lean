import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic

/-! Dimension-free polarization bounds for scalar second, third and fourth
derivatives in nested continuous-linear-map coordinates. These are generic
calculus lemmas; symmetry and diagonal bounds for the actual potential must
be proved when they are instantiated. -/

noncomputable section
namespace MatrixSpencer.RectangularRidgePolarization
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

abbrev Two := E →L[ℝ] E →L[ℝ] ℝ
abbrev Three := E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ
abbrev Four := E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ
local instance ridgePolarizationNormTwo : NormedAddCommGroup (Two (E:=E)) := inferInstance
local instance ridgePolarizationSpaceTwo : NormedSpace ℝ (Two (E:=E)) := inferInstance
local instance ridgePolarizationNormThree : NormedAddCommGroup (Three (E:=E)) := inferInstance
local instance ridgePolarizationSpaceThree : NormedSpace ℝ (Three (E:=E)) := inferInstance
local instance ridgePolarizationNormFour : NormedAddCommGroup (Four (E:=E)) := inferInstance

theorem second_identity (B : Two (E:=E)) (hs : ∀ x y, B x y = B y x) (x y : E) :
    2*B x y = B (x+y) (x+y)-B x x-B y y := by
  simp only [map_add, ContinuousLinearMap.add_apply, hs]
  ring

theorem third_identity (B : Three (E:=E))
    (h12 : ∀ x y z, B x y z = B y x z)
    (h23 : ∀ x y z, B x y z = B x z y) (x y z : E) :
    6*B x y z = B (x+y+z) (x+y+z) (x+y+z)-B (x+y) (x+y) (x+y)-
      B (x+z) (x+z) (x+z)-B (y+z) (y+z) (y+z)+B x x x+B y y y+B z z z := by
  simp only [map_add, ContinuousLinearMap.add_apply, h12, h23]
  ring

set_option maxHeartbeats 1200000 in
theorem fourth_identity (B : Four (E:=E))
    (h12 : ∀ x y z w, B x y z w = B y x z w)
    (h23 : ∀ x y z w, B x y z w = B x z y w)
    (h34 : ∀ x y z w, B x y z w = B x y w z) (x y z w : E) :
    24*B x y z w =
      B (x+y+z+w) (x+y+z+w) (x+y+z+w) (x+y+z+w)-
      B (x+y+z) (x+y+z) (x+y+z) (x+y+z)-
      B (x+y+w) (x+y+w) (x+y+w) (x+y+w)-
      B (x+z+w) (x+z+w) (x+z+w) (x+z+w)-
      B (y+z+w) (y+z+w) (y+z+w) (y+z+w)+
      B (x+y) (x+y) (x+y) (x+y)+B (x+z) (x+z) (x+z) (x+z)+
      B (x+w) (x+w) (x+w) (x+w)+B (y+z) (y+z) (y+z) (y+z)+
      B (y+w) (y+w) (y+w) (y+w)+B (z+w) (z+w) (z+w) (z+w)-
      B x x x x-B y y y y-B z z z z-B w w w w := by
  simp only [map_add, ContinuousLinearMap.add_apply]
  simp only [h12, h23, h34]
  ring

private lemma norm_sum_two {x y : E} (hx : ‖x‖≤1) (hy : ‖y‖≤1) : ‖x+y‖≤2 := by
  exact (norm_add_le x y).trans (by linarith)

private lemma norm_sum_three {x y z : E} (hx : ‖x‖≤1) (hy : ‖y‖≤1) (hz : ‖z‖≤1) :
    ‖x+y+z‖≤3 := by
  have h := norm_sum_two hx hy
  exact (norm_add_le (x+y) z).trans (by linarith)

private lemma norm_sum_four {x y z w : E}
    (hx : ‖x‖≤1) (hy : ‖y‖≤1) (hz : ‖z‖≤1) (hw : ‖w‖≤1) : ‖x+y+z+w‖≤4 := by
  have h := norm_sum_three hx hy hz
  exact (norm_add_le (x+y+z) w).trans (by linarith)

theorem second_norm_le_of_ball (B : Two (E:=E)) {C : ℝ} (hC : 0≤C)
    (hs : ∀ x y, B x y = B y x) (hd : ∀ x, ‖x‖≤2 → |B x x|≤C) : ‖B‖≤2*C := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro x hx
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro y hy
  have h1 := abs_le.mp (hd x (by linarith))
  have h2 := abs_le.mp (hd y (by linarith))
  have h3 := abs_le.mp (hd (x+y) (norm_sum_two hx.le hy.le))
  have he := second_identity B hs x y
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor <;> linarith

theorem third_norm_le_of_ball (B : Three (E:=E)) {C : ℝ} (hC : 0≤C)
    (h12 : ∀ x y z, B x y z = B y x z)
    (h23 : ∀ x y z, B x y z = B x z y)
    (hd : ∀ x, ‖x‖≤3 → |B x x x|≤C) : ‖B‖≤2*C := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro x hx
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro y hy
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro z hz
  have h1 := abs_le.mp (hd x (by linarith))
  have h2 := abs_le.mp (hd y (by linarith))
  have h3 := abs_le.mp (hd z (by linarith))
  have h4 := abs_le.mp (hd (x+y) ((norm_sum_two hx.le hy.le).trans (by norm_num)))
  have h5 := abs_le.mp (hd (x+z) ((norm_sum_two hx.le hz.le).trans (by norm_num)))
  have h6 := abs_le.mp (hd (y+z) ((norm_sum_two hy.le hz.le).trans (by norm_num)))
  have h7 := abs_le.mp (hd (x+y+z) (norm_sum_three hx.le hy.le hz.le))
  have he := third_identity B h12 h23 x y z
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor <;> linarith

theorem fourth_norm_le_of_ball (B : Four (E:=E)) {C : ℝ} (hC : 0≤C)
    (h12 : ∀ x y z w, B x y z w = B y x z w)
    (h23 : ∀ x y z w, B x y z w = B x z y w)
    (h34 : ∀ x y z w, B x y z w = B x y w z)
    (hd : ∀ x, ‖x‖≤4 → |B x x x x|≤C) : ‖B‖≤C := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hC
  intro x hx
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hC
  intro y hy
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hC
  intro z hz
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hC
  intro w hw
  have h1 := abs_le.mp (hd x (by linarith))
  have h2 := abs_le.mp (hd y (by linarith))
  have h3 := abs_le.mp (hd z (by linarith))
  have h4 := abs_le.mp (hd w (by linarith))
  have h5 := abs_le.mp (hd (x+y) ((norm_sum_two hx.le hy.le).trans (by norm_num)))
  have h6 := abs_le.mp (hd (x+z) ((norm_sum_two hx.le hz.le).trans (by norm_num)))
  have h7 := abs_le.mp (hd (x+w) ((norm_sum_two hx.le hw.le).trans (by norm_num)))
  have h8 := abs_le.mp (hd (y+z) ((norm_sum_two hy.le hz.le).trans (by norm_num)))
  have h9 := abs_le.mp (hd (y+w) ((norm_sum_two hy.le hw.le).trans (by norm_num)))
  have h10 := abs_le.mp (hd (z+w) ((norm_sum_two hz.le hw.le).trans (by norm_num)))
  have h11 := abs_le.mp (hd (x+y+z) ((norm_sum_three hx.le hy.le hz.le).trans (by norm_num)))
  have h12b := abs_le.mp (hd (x+y+w) ((norm_sum_three hx.le hy.le hw.le).trans (by norm_num)))
  have h13 := abs_le.mp (hd (x+z+w) ((norm_sum_three hx.le hz.le hw.le).trans (by norm_num)))
  have h14 := abs_le.mp (hd (y+z+w) ((norm_sum_three hy.le hz.le hw.le).trans (by norm_num)))
  have h15 := abs_le.mp (hd (x+y+z+w) (norm_sum_four hx.le hy.le hz.le hw.le))
  have he := fourth_identity B h12 h23 h34 x y z w
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor <;> linarith

theorem second_norm_le_of_diagonal (B : Two (E:=E)) {C : ℝ} (hC : 0≤C)
    (hs : ∀ x y, B x y = B y x) (hd : ∀ x, |B x x|≤C*‖x‖^2) : ‖B‖≤8*C := by
  have h := second_norm_le_of_ball B (mul_nonneg hC (by norm_num : (0:ℝ)≤4)) hs
    (fun x hx => (hd x).trans (mul_le_mul_of_nonneg_left
      (by nlinarith [norm_nonneg x] : ‖x‖^2≤4) hC))
  linarith

theorem third_norm_le_of_diagonal (B : Three (E:=E)) {C : ℝ} (hC : 0≤C)
    (h12 : ∀ x y z, B x y z = B y x z)
    (h23 : ∀ x y z, B x y z = B x z y)
    (hd : ∀ x, |B x x x|≤C*‖x‖^3) : ‖B‖≤54*C := by
  have h := third_norm_le_of_ball B (mul_nonneg hC (by norm_num : (0:ℝ)≤27)) h12 h23
    (fun x hx => (hd x).trans (mul_le_mul_of_nonneg_left
      (by convert pow_le_pow_left₀ (norm_nonneg x) hx 3 using 1 <;> norm_num : ‖x‖^3≤27) hC))
  linarith

theorem fourth_norm_le_of_diagonal (B : Four (E:=E)) {C : ℝ} (hC : 0≤C)
    (h12 : ∀ x y z w, B x y z w = B y x z w)
    (h23 : ∀ x y z w, B x y z w = B x z y w)
    (h34 : ∀ x y z w, B x y z w = B x y w z)
    (hd : ∀ x, |B x x x x|≤C*‖x‖^4) : ‖B‖≤256*C := by
  have h := fourth_norm_le_of_ball B (mul_nonneg hC (by norm_num : (0:ℝ)≤256)) h12 h23 h34
    (fun x hx => (hd x).trans (mul_le_mul_of_nonneg_left
      (by convert pow_le_pow_left₀ (norm_nonneg x) hx 4 using 1 <;> norm_num : ‖x‖^4≤256) hC))
  linarith

end MatrixSpencer.RectangularRidgePolarization
