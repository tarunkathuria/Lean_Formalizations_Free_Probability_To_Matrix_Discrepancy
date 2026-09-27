import MatrixSpencer.RectangularRidgeDerivativePolarization

/-! Operator norm bounds from unit-ball diagonal derivative bounds. Fixed
scalar rescaling is proved using actual multilinearity, so callers do not
need to supply homogeneous bounds for arbitrary directions. -/

noncomputable section
namespace MatrixSpencer.RectangularRidgeUnitPolarization
open RectangularRidgePolarization RectangularRidgeDerivativePolarization
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
local instance ridgeUnitPolarizationNormTwo : NormedAddCommGroup (Two (E:=E)) := inferInstance
local instance ridgeUnitPolarizationSpaceTwo : NormedSpace ℝ (Two (E:=E)) := inferInstance
local instance ridgeUnitPolarizationNormThree : NormedAddCommGroup (Three (E:=E)) := inferInstance
local instance ridgeUnitPolarizationSpaceThree : NormedSpace ℝ (Three (E:=E)) := inferInstance
local instance ridgeUnitPolarizationNormFour : NormedAddCommGroup (Four (E:=E)) := inferInstance

theorem second_norm_le {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 4 f x)
    {C : ℝ} (hC : 0≤C) (hd : ∀ u, ‖u‖≤1 → |second f x u u|≤C) : ‖second f x‖≤8*C := by
  have hb : ∀ u, ‖u‖≤2 → |second f x u u|≤4*C := by
    intro u hu
    have hn : ‖(1/2:ℝ) • u‖≤1 := by rw [norm_smul]; norm_num; linarith
    have h := hd ((1/2:ℝ) • u) hn
    simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul, abs_mul] at h
    norm_num at h
    linarith
  have h := second_norm_le_of_ball _ (by positivity : (0:ℝ)≤4*C) (second_symm hf) hb
  linarith

theorem third_norm_le {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 4 f x)
    {C : ℝ} (hC : 0≤C) (hd : ∀ u, ‖u‖≤1 → |third f x u u u|≤C) : ‖third f x‖≤54*C := by
  have hb : ∀ u, ‖u‖≤3 → |third f x u u u|≤27*C := by
    intro u hu
    have hn : ‖(1/3:ℝ) • u‖≤1 := by rw [norm_smul]; norm_num; linarith
    have h := hd ((1/3:ℝ) • u) hn
    simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul, abs_mul] at h
    norm_num at h
    linarith
  have h := third_norm_le_of_ball _ (by positivity : (0:ℝ)≤27*C)
    (third_symm12 hf) (third_symm23 hf) hb
  linarith

theorem fourth_norm_le {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 4 f x)
    {C : ℝ} (hC : 0≤C) (hd : ∀ u, ‖u‖≤1 → |fourth f x u u u u|≤C) : ‖fourth f x‖≤256*C := by
  have hb : ∀ u, ‖u‖≤4 → |fourth f x u u u u|≤256*C := by
    intro u hu
    have hn : ‖(1/4:ℝ) • u‖≤1 := by rw [norm_smul]; norm_num; linarith
    have h := hd ((1/4:ℝ) • u) hn
    simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul, abs_mul] at h
    norm_num at h
    linarith
  exact fourth_norm_le_of_ball _ (by positivity : (0:ℝ)≤256*C)
    (fourth_symm12 hf) (fourth_symm23 hf) (fourth_symm34 hf) hb

end MatrixSpencer.RectangularRidgeUnitPolarization
