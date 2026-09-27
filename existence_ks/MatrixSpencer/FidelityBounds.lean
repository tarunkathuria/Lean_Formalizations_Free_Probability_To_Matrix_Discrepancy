import MatrixSpencer.FidelityContinuity
import Mathlib.Algebra.QuadraticDiscriminant

/-!
# Dimension-free fidelity trace budget

The faithful transport inequality is extended by continuity, then tested
against scalar identities. The discriminant of the resulting scalar
quadratic yields the trace Cauchy--Schwarz bound, including zero traces.
-/

open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix Filter Topology

noncomputable section

namespace MatrixSpencer

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Every positive definite comparison point bounds fidelity on the full PSD cone. -/
theorem fidelity_le_transportCost {S M Z : Matrix n n ℂ}
    (hS : S.PosSemidef) (hM : M.PosSemidef) (hZ : Z.PosDef) :
    2 * fidelity S M ≤ transportCost S M Z := by
  have hcost : Continuous (fun p : Matrix n n ℂ × Matrix n n ℂ => transportCost p.1 p.2 Z) := by
    unfold transportCost
    exact (continuous_realTrace.comp (continuous_fst.mul continuous_const)).add
      (continuous_realTrace.comp (continuous_snd.mul continuous_const))
  have hlim := hcost.continuousAt.tendsto.comp
    ((regularize_tendsto S).prodMk_nhds (regularize_tendsto M))
  apply le_of_tendsto_of_tendsto ((fidelity_regularize_tendsto hS hM).const_mul 2) hlim
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (fidelity_variational_posDef (regularize_posDef hS hr)
    (regularize_posDef hM hr)).choose_spec.2.2 Z hZ

/-- A scalar comparison point gives the full family of arithmetic mean bounds. -/
theorem fidelity_scalar_bound {S M : Matrix n n ℂ}
    (hS : S.PosSemidef) (hM : M.PosSemidef) {t : ℝ} (ht : 0 < t) :
    2 * fidelity S M ≤ t⁻¹ * realTrace S + t * realTrace M := by
  have hi : (t • (1 : Matrix n n ℂ))⁻¹ = t⁻¹ • (1 : Matrix n n ℂ) := by
    apply Matrix.inv_eq_left_inv
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul,
      mul_inv_cancel₀ ht.ne', one_smul]
  have h := fidelity_le_transportCost hS hM (Matrix.PosDef.one.smul ht)
  simpa only [transportCost, hi,
    Matrix.mul_smul, Matrix.mul_one, realTrace_smul] using h

/-- Squared fidelity is bounded by the product of unnormalized traces. -/
theorem fidelity_sq_le_trace_mul {S M : Matrix n n ℂ}
    (hS : S.PosSemidef) (hM : M.PosSemidef) :
    fidelity S M ^ 2 ≤ realTrace S * realTrace M := by
  have hpoly : ∀ t : ℝ, 0 ≤ realTrace M * (t * t) + (-2 * fidelity S M) * t + realTrace S := by
    intro t
    by_cases ht : 0 < t
    · have h := mul_le_mul_of_nonneg_left (fidelity_scalar_bound hS hM ht) ht.le
      have hcancel : t * (t⁻¹ * realTrace S + t * realTrace M) =
          realTrace S + t * t * realTrace M := by
        rw [mul_add, ← mul_assoc, mul_inv_cancel₀ ht.ne', one_mul]
        ring
      rw [hcancel] at h
      nlinarith
    · have ht' : t ≤ 0 := le_of_not_gt ht
      have hterm : 0 ≤ (-2 * fidelity S M) * t :=
        mul_nonneg_of_nonpos_of_nonpos (by nlinarith [fidelity_nonneg S M]) ht'
      have hsq := mul_nonneg (realTrace_nonneg hM) (mul_self_nonneg t)
      linarith [realTrace_nonneg hS]
  have hd := discrim_le_zero hpoly
  unfold discrim at hd
  nlinarith

/-- The dimension-free trace Cauchy--Schwarz bound for fidelity. -/
theorem fidelity_le_sqrt_trace_mul {S M : Matrix n n ℂ}
    (hS : S.PosSemidef) (hM : M.PosSemidef) :
    fidelity S M ≤ Real.sqrt (realTrace S * realTrace M) := by
  exact (Real.le_sqrt (fidelity_nonneg S M)
    (mul_nonneg (realTrace_nonneg hS) (realTrace_nonneg hM))).mpr
    (fidelity_sq_le_trace_mul hS hM)

end MatrixSpencer
