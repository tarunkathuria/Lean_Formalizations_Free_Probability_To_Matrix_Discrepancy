import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Multiset

/-!
# Trace bounds for arbitrary complex matrix square roots

Only the square identity is needed. The root need not be Hermitian, normal,
or the principal branch. Each characteristic root has squared modulus at
most the operator norm of the square; their sum is the trace. This controls
the complex trace without bounding the norm of a nonnormal matrix root.
-/

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSComplexRootTraceBound

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The square relation bounds every characteristic root, including multiplicity. -/
theorem root_norm_le_sqrt [Nonempty n] {Q X : Matrix n n ℂ} (hQ : Q * Q = X)
    {z : ℂ} (hz : z ∈ Q.charpoly.roots) : ‖z‖ ≤ Real.sqrt ‖X‖ := by
  have hs : z ∈ spectrum ℂ Q :=
    Matrix.mem_spectrum_of_isRoot_charpoly ((Polynomial.mem_roots Q.charpoly_monic.ne_zero).mp hz)
  have hp := spectrum.pow_mem_pow Q 2 hs
  rw [pow_two, hQ] at hp
  have hn := spectrum.norm_le_norm_of_mem hp
  rw [norm_pow] at hn
  nlinarith [Real.sq_sqrt (norm_nonneg X), Real.sqrt_nonneg ‖X‖, norm_nonneg z]

/-- Complex trace bound for any square root of any finite matrix. -/
theorem trace_norm_le_card_sqrt_norm {Q X : Matrix n n ℂ} (hQ : Q * Q = X) :
    ‖Matrix.trace Q‖ ≤ (Fintype.card n : ℝ) * Real.sqrt ‖X‖ := by
  rcases isEmpty_or_nonempty n with he | hn
  · simp [Matrix.trace, Fintype.card_eq_zero]
  · rw [Matrix.trace_eq_sum_roots_charpoly]
    apply (norm_multiset_sum_le _).trans
    have hs : (Q.charpoly.roots.map (fun z => ‖z‖)).sum ≤
        (Q.charpoly.roots.card : ℝ) * Real.sqrt ‖X‖ := by
      have h := Multiset.sum_le_card_nsmul (Q.charpoly.roots.map (fun z => ‖z‖))
        (Real.sqrt ‖X‖) (by
          intro r hr
          obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hr
          exact root_norm_le_sqrt hQ hz)
      simpa only [Multiset.card_map, nsmul_eq_mul] using h
    apply hs.trans
    apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
    exact_mod_cast (Polynomial.card_roots' Q.charpoly).trans_eq Q.charpoly_natDegree_eq_dim

/-- Product-source version, with no positivity or normality assumptions. -/
theorem trace_norm_le_card_sqrt_norm_mul {Q S M : Matrix n n ℂ} (hQ : Q * Q = S * M) :
    ‖Matrix.trace Q‖ ≤ (Fintype.card n : ℝ) * Real.sqrt (‖S‖ * ‖M‖) :=
  (trace_norm_le_card_sqrt_norm hQ).trans
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (norm_mul_le S M)) (Nat.cast_nonneg _))

/-- Scalar input caps can be substituted directly in the holomorphic value bound. -/
theorem trace_norm_le_card_sqrt_caps {Q S M : Matrix n n ℂ} {s m : ℝ}
    (hQ : Q * Q = S * M) (hS : ‖S‖ ≤ s) (hM : ‖M‖ ≤ m) :
    ‖Matrix.trace Q‖ ≤ (Fintype.card n : ℝ) * Real.sqrt (s * m) :=
  (trace_norm_le_card_sqrt_norm_mul hQ).trans
    (mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (mul_le_mul hS hM (norm_nonneg _) ((norm_nonneg _).trans hS)))
      (Nat.cast_nonneg _))

end MatrixSpencer.KSComplexRootTraceBound
