import MatrixSpencer.KSComplexOwnerPerturbation

/-!
# An arithmetic radius for simultaneous coefficient and density perturbations

The time direction may have coordinate magnitude two. A perturbation of the
complex time by this radius therefore changes each coefficient by at most
twice the radius. Together with the density floor, the actual relative
source error is below 1/16, independently of its least positive eigenvalue.
-/

noncomputable section
namespace MatrixSpencer.KSComplexPerturbationRadius

def radius (μ ρ : ℝ) : ℝ := min 1 (min μ ρ) / 1000

theorem radius_pos {μ ρ : ℝ} (hμ : 0 < μ) (hρ : 0 < ρ) : 0 < radius μ ρ := by
  unfold radius
  positivity

theorem radius_le_one (μ ρ : ℝ) : radius μ ρ ≤ 1 := by
  have h := min_le_left (1 : ℝ) (min μ ρ)
  unfold radius
  linarith

theorem radius_le_density (μ ρ : ℝ) : radius μ ρ ≤ μ / 1000 := by
  exact div_le_div_of_nonneg_right ((min_le_right (1 : ℝ) (min μ ρ)).trans (min_le_left μ ρ))
    (by norm_num)

theorem radius_le_margin (μ ρ : ℝ) : radius μ ρ ≤ ρ / 1000 := by
  exact div_le_div_of_nonneg_right ((min_le_right (1 : ℝ) (min μ ρ)).trans (min_le_right μ ρ))
    (by norm_num)

theorem density_relative_le {μ ρ : ℝ} (hμ : 0 < μ) :
    radius μ ρ / μ ≤ 1 / 1000 := by
  apply (div_le_iff₀ hμ).mpr
  simpa only [div_eq_mul_inv, one_mul, mul_comm] using radius_le_density μ ρ

theorem owner_relative_le {μ ρ : ℝ} (hμ : 0 < μ) (hρ : 0 < ρ) :
    (2 * (2 * radius μ ρ) + (2 * radius μ ρ) ^ 2) / ρ ≤ 1 / 64 := by
  have hp := (radius_pos hμ hρ).le
  have hr := radius_le_one μ ρ
  have hm := radius_le_margin μ ρ
  have hs := mul_le_mul_of_nonneg_left hr hp
  apply (div_le_iff₀ hρ).mpr
  nlinarith

/-- The actual combined-error formula from the owner perturbation proof
fits the fixed relative source ball used by the spectral-domain argument. -/
theorem combinedCap_le {μ ρ : ℝ} (hμ : 0 < μ) (hρ : 0 < ρ) :
    KSComplexOwnerPerturbation.combinedCap ρ μ (2 * radius μ ρ) (radius μ ρ) ≤ 1 / 16 := by
  have ho := owner_relative_le hμ hρ
  have hd := density_relative_le (ρ := ρ) hμ
  have hp := (radius_pos hμ hρ).le
  unfold KSComplexOwnerPerturbation.combinedCap
  have hh := mul_le_mul (add_le_add_left ho 1) (add_le_add_left hd 1)
    (by positivity : 0 ≤ 1 + radius μ ρ / μ) (by norm_num : (0 : ℝ) ≤ 1 + 1 / 64)
  linarith

end MatrixSpencer.KSComplexPerturbationRadius
