import SeamlessKS.SourceComplex
import MatrixSpencer.KSComplexOwnerPerturbation

/-!
The numerical complex radius and relative scalar-owner/density estimates.
The radius depends on the density floor and cube margin, never a nonzero
source eigenvalue. This module connects the explicit new source to the
existing positive-partition contraction theorem.
-/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace SeamlessKS
namespace NumericalRegularity
open MatrixSpencer

/-- A fully explicit complex perturbation radius. -/
def radius (μ ρ ζ : ℝ) : ℝ := min 1 (min μ (min ρ ζ)) / 10000

theorem radius_pos {μ ρ ζ : ℝ} (hμ : 0 < μ) (hρ : 0 < ρ) (hζ : 0 < ζ) :
    0 < radius μ ρ ζ := by unfold radius; positivity

theorem radius_le_one (μ ρ ζ : ℝ) : radius μ ρ ζ ≤ 1 / 10000 :=
  div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)

theorem radius_le_density (μ ρ ζ : ℝ) : radius μ ρ ζ ≤ μ / 10000 :=
  div_le_div_of_nonneg_right ((min_le_right _ _).trans (min_le_left _ _)) (by norm_num)

theorem radius_le_margin (μ ρ ζ : ℝ) : radius μ ρ ζ ≤ ρ / 10000 :=
  div_le_div_of_nonneg_right ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))) (by norm_num)

theorem radius_le_smoothing (μ ρ ζ : ℝ) : radius μ ρ ζ ≤ ζ / 10000 :=
  div_le_div_of_nonneg_right ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))) (by norm_num)

theorem owner_error_le {u μ ρ ζ x h : ℝ} (hu : 0 < u) (hμ : 0 < μ)
    (hρ : 0 < ρ) (hζ : 0 < ζ) (hx : |x| ≤ 1 - ρ) (hh : |h| ≤ 2)
    (z : ℂ) (hz : ‖z‖ ≤ radius μ ρ ζ) :
    ‖Source.complexError u ζ x (z * (h : ℂ))‖ ≤ 1 / 100 := by
  have hr := radius_pos hμ hρ hζ
  have h₁ := radius_le_one μ ρ ζ
  have h₂ := radius_le_smoothing μ ρ ζ
  have h₃ := radius_le_margin μ ρ ζ
  have hz' : ‖z * (h : ℂ)‖ ≤ 2 * radius μ ρ ζ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    nlinarith [mul_le_mul hz hh (abs_nonneg h) hr.le]
  have hb := Source.norm_complexError_le hu hζ hρ hx
    (show 0 ≤ 2 * radius μ ρ ζ by positivity)
    (show 2 * radius μ ρ ζ ≤ 2 by linarith)
    (show 2 * radius μ ρ ζ ≤ ζ / 2 by linarith) (z * (h : ℂ)) hz'
  apply hb.trans
  apply (div_le_iff₀ hρ).mpr
  linarith

variable {n : Type*} [Fintype n] [DecidableEq n]
local instance {k : Type*} [Fintype k] [DecidableEq k] : CStarAlgebra (Matrix k k ℂ) := {}

def combinedError (u ζ x : ℝ) (z : ℂ) (P S Δ : Matrix n n ℂ) : ℂ :=
  (1 + Source.complexError u ζ x z) *
    (1 + KSComplexOwnerPerturbation.traceError P S Δ) - 1

theorem combinedError_le (P S Δ : Matrix n n ℂ) (hP : P.PosSemidef)
    {u μ ρ ζ x h : ℝ} (hu : 0 < u) (hμ : 0 < μ)
    (hfloor : μ • (1 : Matrix n n ℂ) ≤ S) (hρ : 0 < ρ) (hζ : 0 < ζ)
    (hx : |x| ≤ 1 - ρ) (hh : |h| ≤ 2) (z : ℂ)
    (hz : ‖z‖ ≤ radius μ ρ ζ) (hΔ : ‖Δ‖ ≤ radius μ ρ ζ) :
    ‖combinedError u ζ x (z * (h : ℂ)) P S Δ‖ ≤ 1 / 16 := by
  have hc := owner_error_le hu hμ hρ hζ hx hh z hz
  have hp : ‖KSComplexOwnerPerturbation.traceError P S Δ‖ ≤ 1 / 100 := by
    have hb := KSComplexOwnerPerturbation.traceError_bound P S Δ hP hμ hfloor hΔ
    apply hb.trans
    apply (div_le_iff₀ hμ).mpr
    have hr := radius_le_density μ ρ ζ
    linarith
  have hm := KSComplexOwnerPerturbation.product_error_bound
    (Source.complexError u ζ x (z * (h : ℂ)))
    (KSComplexOwnerPerturbation.traceError P S Δ)
    (by norm_num : (0 : ℝ) ≤ 1 / 100) (by norm_num : (0 : ℝ) ≤ 1 / 100) hc hp
  exact hm.trans (by norm_num)

theorem coefficient_eq_base_mul_error (P S Δ : Matrix n n ℂ) (hP : P.PosSemidef)
    {u μ ρ ζ x : ℝ} (hu : 0 < u) (hμ : 0 < μ)
    (hfloor : μ • (1 : Matrix n n ℂ) ≤ S) (hρ : 0 < ρ)
    (hx : |x| ≤ 1 - ρ) (z : ℂ) :
    Source.complexWeight u ζ ((x : ℂ) + z) * Matrix.trace (P * (S + Δ)) =
      ((Source.weight u ζ x * realTrace (P * S) : ℝ) : ℂ) *
        (1 + combinedError u ζ x z P S Δ) := by
  rw [Source.complexWeight_eq_base_mul_error hu hρ hx z,
    KSComplexOwnerPerturbation.trace_eq_base_mul_error P S Δ hP hμ hfloor]
  unfold combinedError
  push_cast
  ring

end NumericalRegularity
end SeamlessKS
