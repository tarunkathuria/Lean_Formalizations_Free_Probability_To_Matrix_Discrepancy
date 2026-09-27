import MatrixSpencer.KSComplexSpinSource

/-!
# Source norm bounds without normalization or source eigenvalue gaps

The same explicit dilation used for a positive partition of identity also
bounds an arbitrary positive source. This gives an absolute norm bound for
the actual complex spin source from the norm of its unperturbed value.
-/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSComplexSourceNorm

variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
local instance {k : Type*} [Fintype k] [DecidableEq k] : CStarAlgebra (Matrix k k ℂ) := {}
open KSComplexRelativeSource

theorem positive_sum_contraction (E : ι → Matrix n n ℂ)
    (hE : ∀ i, (E i).PosSemidef) (a : ι → ℂ) {R : ℝ}
    (hR : 0 ≤ R) (ha : ∀ i, ‖a i‖ ≤ R) :
    ‖∑ i, a i • E i‖ ≤ R * ‖∑ i, E i‖ := by
  have hg := Matrix.l2_opNorm_conjTranspose_mul_self (dilation E)
  rw [dilation_gram E hE] at hg
  rw [← dilation_factorization E hE a]
  calc _ ≤ ‖(dilation E)ᴴ * coefficientDiagonal (n := n) a‖ * ‖dilation E‖ :=
      Matrix.l2_opNorm_mul _ _
    _ ≤ (‖(dilation E)ᴴ‖ * ‖coefficientDiagonal (n := n) a‖) * ‖dilation E‖ :=
      mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
    _ = ‖coefficientDiagonal (n := n) a‖ * ‖∑ i, E i‖ := by
      rw [Matrix.l2_opNorm_conjTranspose, hg]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (coefficientDiagonal_norm_le a hR ha) (norm_nonneg _)

open KSComplexSpinSource

/-- The exact complex source on the explicit perturbation ball has norm
at most 17/16 times its real base source norm. -/
theorem source_norm_le (v : ι → n → ℂ) (x h : ι → ℝ)
    (S Δ : Matrix (n ⊕ n) (n ⊕ n) ℂ) {μ ρ : ℝ}
    (hμ : 0 < μ) (hfloor : μ • (1 : Matrix (n ⊕ n) (n ⊕ n) ℂ) ≤ S)
    (hρ : 0 < ρ) (hx : ∀ i, |x i| ≤ 1 - ρ) (hh : ∀ i, |h i| ≤ 2)
    (z : ℂ) (hz : ‖z‖ ≤ KSComplexPerturbationRadius.radius μ ρ)
    (hΔ : ‖Δ‖ ≤ KSComplexPerturbationRadius.radius μ ρ) :
    ‖source v x h (z, S + Δ)‖ ≤ (17 / 16 : ℝ) * ‖source v x h (0, S)‖ := by
  have hS := KSComplexOwnerPerturbation.density_posSemidef hμ hfloor
  rw [source_perturb_eq v x h S Δ hμ hfloor hρ hx z,
    source_zero_eq_pieces v x h hS.isHermitian]
  apply positive_sum_contraction (basePiece v x S) (basePiece_posSemidef v x hS hρ hx) _ (by norm_num)
  intro i
  have hp := (KSComplexPerturbationRadius.radius_pos hμ hρ).le
  have hz' : ‖z * (h i : ℂ)‖ ≤ 2 * KSComplexPerturbationRadius.radius μ ρ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    simpa only [mul_comm] using mul_le_mul hz (hh i) (abs_nonneg _) hp
  have he := (KSComplexOwnerPerturbation.combinedError_bound (atom v i) S Δ
    (atom_posSemidef v i) hμ hfloor hρ (hx i) (by positivity) (z * (h i : ℂ)) hz' hΔ).trans
    (KSComplexPerturbationRadius.combinedCap_le hμ hρ)
  have hnorm := norm_add_le (1 : ℂ) (KSComplexOwnerPerturbation.combinedError
    (x i) (z * (h i : ℂ)) (atom v i) S Δ)
  simp only [norm_one] at hnorm
  exact hnorm.trans (by linarith)

end MatrixSpencer.KSComplexSourceNorm
