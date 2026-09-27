import MatrixSpencer.KSRationalTraceRoots
import MatrixSpencer.KSScalarHolomorphicRoot
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Algebra.Order.BigOperators.Group.Multiset

/-!
# Compact resolvent trace as a scalar-root sum

Characteristic roots retain algebraic multiplicity. All resolvent integration
parameters are real; matrices and their characteristic roots may be complex.
No normality or diagonalizability is assumed.
-/

open Matrix Set MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSCompactTraceRoots
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A finite multiset sum commutes with interval integration. -/
theorem integral_multiset_sum {α : Type*} (s : Multiset α) (f : α → ℝ → ℂ)
    (a b : ℝ) (hf : ∀ z ∈ s, IntervalIntegrable (f z) volume a b) :
    (∫ t in a..b, (s.map (fun z => f z t)).sum) =
      (s.map (fun z => ∫ t in a..b, f z t)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons z s ih =>
    have hz := hf z (Multiset.mem_cons_self _ _)
    have hs : ∀ z ∈ s, IntervalIntegrable (f z) volume a b :=
      fun z h => hf z (Multiset.mem_cons_of_mem h)
    have hsi : IntervalIntegrable (fun t => (s.map (fun z => f z t)).sum) volume a b := by
      clear ih hf hz
      induction s using Multiset.induction_on with
      | empty => simpa using (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0 : ℂ)) volume a b)
      | @cons y s ih =>
        simp only [Multiset.map_cons, Multiset.sum_cons]
        exact (hs y (Multiset.mem_cons_self _ _)).add
          (ih (fun z h => hs z (Multiset.mem_cons_of_mem h)))
    simp only [Multiset.map_cons, Multiset.sum_cons]
    rw [intervalIntegral.integral_add hz hsi, ih hs]

/-- The principal half-power has the expected modulus, including at zero. -/
theorem norm_half_power (z : ℂ) : ‖z ^ (1 / 2 : ℂ)‖ = Real.sqrt ‖z‖ := by
  have he : (z ^ (1 / 2 : ℂ)) ^ (2 : ℕ) = z := by
    rw [← Complex.cpow_mul_nat]
    norm_num
  have hn := congrArg norm he
  rw [norm_pow] at hn
  nlinarith [norm_nonneg (z ^ (1 / 2 : ℂ)), Real.sqrt_nonneg ‖z‖,
    Real.sq_sqrt (norm_nonneg z)]

/-- Every characteristic root has modulus at most the operator norm. -/
theorem characteristic_root_norm_le [Nonempty n] (M : Matrix n n ℂ)
    {z : ℂ} (hz : z ∈ M.charpoly.roots) : ‖z‖ ≤ ‖M‖ := by
  apply spectrum.norm_le_norm_of_mem
  exact Matrix.mem_spectrum_of_isRoot_charpoly
    ((Polynomial.mem_roots M.charpoly_monic.ne_zero).mp hz)

/-- A bound for the principal-root sum of an arbitrary complex matrix. -/
theorem root_sum_norm_le (M : Matrix n n ℂ) :
    ‖(M.charpoly.roots.map (fun z => z ^ (1 / 2 : ℂ))).sum‖ ≤
      (Fintype.card n : ℝ) * Real.sqrt ‖M‖ := by
  rcases isEmpty_or_nonempty n with he | hn
  · simp [Fintype.card_eq_zero]
  · apply (norm_multiset_sum_le _).trans
    have hcap : ∀ r ∈ (M.charpoly.roots.map (fun z => ‖z ^ (1 / 2 : ℂ)‖)),
        r ≤ Real.sqrt ‖M‖ := by
      intro r hr
      obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hr
      rw [norm_half_power]
      exact Real.sqrt_le_sqrt (characteristic_root_norm_le M hz)
    have hh := Multiset.sum_le_card_nsmul _ (Real.sqrt ‖M‖) hcap
    simpa only [Multiset.map_map, Function.comp_def, Multiset.card_map,
      KSRationalTraceRoots.roots_card, nsmul_eq_mul] using hh

open KSCompactResolvent KSScalarHolomorphicRoot

/-- Characteristic roots of a matrix in the slit-spectrum domain lie in the slit plane. -/
theorem root_mem_slitPlane {M : Matrix n n ℂ} (hM : Domain M)
    {z : ℂ} (hz : z ∈ M.charpoly.roots) : z ∈ Complex.slitPlane :=
  hM (Matrix.mem_spectrum_of_isRoot_charpoly
    ((Polynomial.mem_roots M.charpoly_monic.ne_zero).mp hz))

theorem scalar_kernel_intervalIntegrable {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    IntervalIntegrable (fun t : ℝ => z / ((t : ℂ)^2 + (1-(t : ℂ))^2*z)) volume 0 1 := by
  have hc : Continuous (fun t : ℝ => z / ((t : ℂ)^2 + (1-(t : ℂ))^2*z)) :=
    continuous_const.div (by fun_prop) (fun t => denominator_ne_zero hz t)
  exact hc.intervalIntegrable 0 1

/-- The normalized scalar integral in exactly the rational form used by the matrix trace. -/
theorem scalar_kernel_integral {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    (2 / (Real.pi : ℂ)) *
      (∫ t in (0 : ℝ)..1, z / ((t : ℂ)^2 + (1-(t : ℂ))^2*z)) = principalRoot z := by
  have he := integral_eq_principalRoot hz
  rw [rootIntegral_eq_interval ℂ (functionDenominator_isUnit hz)] at he
  simpa only [smul_eq_mul, mul_one, Ring.inverse_eq_inv, Complex.ofReal_div,
    Complex.ofReal_ofNat, Complex.ofReal_mul, Complex.ofReal_inv, div_eq_mul_inv] using he

/-- The constructed complex trace extension is the sum of the principal characteristic roots.
This proves the identity for nonnormal matrices without defining a matrix square root. -/
theorem traceRoot_eq_sum_roots {M : Matrix n n ℂ} (hM : Domain M) :
    traceRoot M = (M.charpoly.roots.map principalRoot).sum := by
  rw [traceRoot_eq_integral hM]
  calc
    _ = (2 / (Real.pi : ℂ)) * (∫ t in (0 : ℝ)..1,
        (M.charpoly.roots.map (fun z => z / ((t : ℂ)^2 + (1-(t : ℂ))^2*z))).sum) := by
      congr 1
      apply intervalIntegral.integral_congr
      intro t ht
      have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using ht
      exact KSRationalTraceRoots.trace_interval_kernel_eq_sum_roots M t
        (denominator_isUnit hM ht')
    _ = (2 / (Real.pi : ℂ)) * (M.charpoly.roots.map (fun z =>
        ∫ t in (0 : ℝ)..1, z / ((t : ℂ)^2 + (1-(t : ℂ))^2*z))).sum := by
      rw [integral_multiset_sum _ _ 0 1
        (fun z hz => scalar_kernel_intervalIntegrable (root_mem_slitPlane hM hz))]
    _ = (M.charpoly.roots.map principalRoot).sum := by
      rw [← Multiset.sum_map_mul_left]
      apply congrArg Multiset.sum
      exact Multiset.map_congr rfl (fun z hz => scalar_kernel_integral (root_mem_slitPlane hM hz))

/-- Source-gap-free trace cap for the actual constructed analytic extension. -/
theorem traceRoot_norm_le {M : Matrix n n ℂ} (hM : Domain M) :
    ‖traceRoot M‖ ≤ (Fintype.card n : ℝ) * Real.sqrt ‖M‖ := by
  rw [traceRoot_eq_sum_roots hM]
  exact root_sum_norm_le M

/-- Product norm version of the analytic trace cap. -/
theorem traceRoot_product_norm_le {S M : Matrix n n ℂ} (hSM : Domain (S * M)) :
    ‖traceRoot (S * M)‖ ≤ (Fintype.card n : ℝ) * Real.sqrt (‖S‖ * ‖M‖) :=
  (traceRoot_norm_le hSM).trans
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (norm_mul_le S M)) (Nat.cast_nonneg _))

/-- Explicit scalar input caps can be substituted in the trace-extension bound. -/
theorem traceRoot_product_caps {S M : Matrix n n ℂ} (hSM : Domain (S * M))
    {s m : ℝ} (hS : ‖S‖ ≤ s) (hM : ‖M‖ ≤ m) :
    ‖traceRoot (S * M)‖ ≤ (Fintype.card n : ℝ) * Real.sqrt (s * m) :=
  (traceRoot_product_norm_le hSM).trans
    (mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (mul_le_mul hS hM (norm_nonneg _) ((norm_nonneg _).trans hS)))
      (Nat.cast_nonneg _))

end MatrixSpencer.KSCompactTraceRoots
