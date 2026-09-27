import MatrixSpencer.KSComplexRootTraceBound
import MatrixSpencer.KSCauchyDerivatives
import Mathlib.Analysis.Analytic.Binomial

/-!
# Bounds for dyadic power traces without an order-dependent exponent

The first layer is purely algebraic. Any complex matrix `Q` satisfying
`Q ^ p = S ^ (p - 1)` has trace bounded by `card n * max 1 ‖S‖`, independently
of `p > 0`. No normality or choice of root branch is assumed. This is the
uniform value estimate needed after constructing an analytic power branch.
It is not, by itself, a derivative theorem for the actual potential.
-/

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.RectangularRidgeTracePowerAnalytic
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Any characteristic root of a `(p-1)/p` matrix power has a uniform cap. -/
theorem characteristic_root_norm_le [Nonempty n] {p : ℕ} (hp : 0 < p)
    {Q S : Matrix n n ℂ} (hQ : Q ^ p = S ^ (p - 1))
    {z : ℂ} (hz : z ∈ Q.charpoly.roots) : ‖z‖ ≤ max 1 ‖S‖ := by
  have hs : z ∈ spectrum ℂ Q :=
    Matrix.mem_spectrum_of_isRoot_charpoly
      ((Polynomial.mem_roots Q.charpoly_monic.ne_zero).mp hz)
  have hpow := spectrum.norm_le_norm_of_mem (spectrum.pow_mem_pow Q p hs)
  rw [hQ, norm_pow] at hpow
  have hnorm : ‖S ^ (p - 1)‖ ≤ ‖S‖ ^ (p - 1) := norm_pow_le _ _
  have hbase : 0 ≤ max (1 : ℝ) ‖S‖ := le_trans zero_le_one (le_max_left _ _)
  have hbound : ‖S‖ ^ (p - 1) ≤ (max 1 ‖S‖) ^ p := by
    exact (pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) _).trans
      (pow_le_pow_right₀ (le_max_left _ _) (Nat.sub_le _ _))
  exact (pow_le_pow_iff_left₀ (norm_nonneg z) hbase (Nat.ne_of_gt hp)).mp (hpow.trans (hnorm.trans hbound))

/-- Uniform trace cap, including empty matrices and nonnormal root branches. -/
theorem trace_norm_le {p : ℕ} (hp : 0 < p) {Q S : Matrix n n ℂ}
    (hQ : Q ^ p = S ^ (p - 1)) :
    ‖Matrix.trace Q‖ ≤ (Fintype.card n : ℝ) * max 1 ‖S‖ := by
  rcases isEmpty_or_nonempty n with he | hn
  · simp [Matrix.trace, Fintype.card_eq_zero]
  · rw [Matrix.trace_eq_sum_roots_charpoly]
    apply (norm_multiset_sum_le _).trans
    have h := Multiset.sum_le_card_nsmul (Q.charpoly.roots.map (fun z => ‖z‖))
      (max 1 ‖S‖) (by
        intro r hr
        obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hr
        exact characteristic_root_norm_le hp hQ hz)
    have hc : (Q.charpoly.roots.card : ℝ) ≤ (Fintype.card n : ℝ) := by
      exact_mod_cast (Polynomial.card_roots' Q.charpoly).trans_eq Q.charpoly_natDegree_eq_dim
    have hh : (Q.charpoly.roots.map (fun z => ‖z‖)).sum ≤
        (Q.charpoly.roots.card : ℝ) * max 1 ‖S‖ := by
      simpa only [Multiset.card_map, nsmul_eq_mul] using h
    exact hh.trans
      (mul_le_mul_of_nonneg_right hc (le_trans zero_le_one (le_max_left _ _)))

end MatrixSpencer.RectangularRidgeTracePowerAnalytic
