import MatrixSpencer.TraceGeometry
import MatrixSpencer.Realignment
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# The compact density domain

Physical density matrices use positive-semidefinite matrix order and
unnormalized real trace one. All norms here are Euclidean operator norms.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix

noncomputable section

namespace MatrixSpencer

variable {n : Type*} [Fintype n] [DecidableEq n]

local instance densityCStarAlgebra : CStarAlgebra (Matrix n n ℂ) := {}

theorem realTrace_eq_sum_eigenvalues {S : Matrix n n ℂ} (hS : S.IsHermitian) :
    realTrace S = ∑ i, hS.eigenvalues i := by
  simp only [realTrace, hS.trace_eq_sum_eigenvalues, map_sum, RCLike.ofReal_re]

/-- A positive matrix is bounded above by its unnormalized trace times the identity. -/
theorem posSemidef_le_trace_identity {S : Matrix n n ℂ} (hS : S.PosSemidef) :
    S ≤ algebraMap ℝ (Matrix n n ℂ) (realTrace S) := by
  rw [le_algebraMap_iff_spectrum_le hS.isHermitian,
    hS.isHermitian.spectrum_real_eq_range_eigenvalues]
  rintro r ⟨i, rfl⟩
  rw [realTrace_eq_sum_eigenvalues hS.isHermitian]
  exact Finset.single_le_sum (fun j _ => hS.eigenvalues_nonneg j) (Finset.mem_univ i)

/-- The operator norm of a positive matrix is at most its unnormalized trace. -/
theorem posSemidef_norm_le_realTrace {S : Matrix n n ℂ} (hS : S.PosSemidef) :
    ‖S‖ ≤ realTrace S := by
  exact (CStarAlgebra.norm_le_iff_le_algebraMap S (realTrace_nonneg hS) hS.nonneg).mpr
    (posSemidef_le_trace_identity hS)

/-- The physical density domain; its positivity condition uses Loewner order. -/
def densitySet : Set (Matrix n n ℂ) := {S | S.PosSemidef ∧ realTrace S = 1}

theorem density_norm_le_one {S : Matrix n n ℂ} (hS : S ∈ densitySet) : ‖S‖ ≤ 1 := by
  simpa only [hS.2] using posSemidef_norm_le_realTrace hS.1

omit [DecidableEq n] in
theorem continuous_realTrace : Continuous (realTrace : Matrix n n ℂ → ℝ) := by
  unfold realTrace Matrix.trace
  fun_prop

theorem isClosed_densitySet : IsClosed (densitySet : Set (Matrix n n ℂ)) := by
  have hpos : IsClosed {S : Matrix n n ℂ | S.PosSemidef} := by
    simpa only [Matrix.nonneg_iff_posSemidef] using
      (isClosed_le continuous_const continuous_id : IsClosed {S : Matrix n n ℂ | 0 ≤ S})
  exact hpos.inter (isClosed_eq continuous_realTrace continuous_const)

/-- Compactness is proved for the actual density domain, including singular matrices. -/
theorem isCompact_densitySet : IsCompact (densitySet : Set (Matrix n n ℂ)) := by
  apply (isCompact_closedBall (0 : Matrix n n ℂ) 1).of_isClosed_subset isClosed_densitySet
  intro S hS
  simpa only [Metric.mem_closedBall, dist_zero_right] using density_norm_le_one hS

/-- The explicit faithful density used to witness nonemptiness. -/
def maximallyMixed : Matrix n n ℂ := (Fintype.card n : ℝ)⁻¹ • 1

theorem maximallyMixed_posDef [Nonempty n] : (maximallyMixed : Matrix n n ℂ).PosDef := by
  apply Matrix.PosDef.one.smul
  exact inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)

theorem maximallyMixed_mem_densitySet [Nonempty n] :
    (maximallyMixed : Matrix n n ℂ) ∈ densitySet := by
  refine ⟨maximallyMixed_posDef.posSemidef, ?_⟩
  have hn : (Fintype.card n : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr Fintype.card_pos)
  change realTrace ((Fintype.card n : ℝ)⁻¹ • (1 : Matrix n n ℂ)) = 1
  rw [realTrace_smul]
  simp only [realTrace, Matrix.trace_one, RCLike.natCast_re]
  exact inv_mul_cancel₀ hn

theorem densitySet_nonempty [Nonempty n] : (densitySet : Set (Matrix n n ℂ)).Nonempty :=
  ⟨maximallyMixed, maximallyMixed_mem_densitySet⟩

theorem densitySet_convex : Convex ℝ (densitySet : Set (Matrix n n ℂ)) := by
  intro S hS T hT a b ha hb hab
  refine ⟨?_, ?_⟩
  · exact (add_nonneg (smul_nonneg ha hS.1.nonneg) (smul_nonneg hb hT.1.nonneg)).posSemidef
  · simpa only [realTrace_add, realTrace_smul, hS.2, hT.2, mul_one] using hab

omit [DecidableEq n] in
/-- Entrywise Cauchy--Schwarz gives a dimension-dependent trace bound. -/
theorem realTrace_sq_le_card_mul_entryEnergy (A : Matrix n n ℂ) :
    (realTrace A) ^ 2 ≤ (Fintype.card n : ℝ) * entryEnergy A := by
  have ht : realTrace A = ∑ i, (A i i).re := by
    simp only [realTrace, Matrix.trace, Matrix.diag, map_sum, RCLike.re_eq_complex_re]
  have hcs : (realTrace A) ^ 2 ≤ (Fintype.card n : ℝ) * ∑ i, (A i i).re ^ 2 := by
    rw [ht]
    simpa using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun _ : n => (1 : ℝ)) (fun i => (A i i).re)
  have hd : (∑ i, (A i i).re ^ 2) ≤ entryEnergy A := by
    apply Finset.sum_le_sum
    intro i _
    have hentry : (A i i).re ^ 2 ≤ Complex.normSq (A i i) := by
      rw [Complex.normSq_apply]
      nlinarith [sq_nonneg (A i i).im]
    exact hentry.trans (Finset.single_le_sum
      (fun j _ => Complex.normSq_nonneg (A i j)) (Finset.mem_univ i))
  exact hcs.trans (mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg _))

/-- The square-root trace budget on the whole positive cone, including the boundary. -/
theorem trace_sqrt_sq_le_card_mul_trace {S : Matrix n n ℂ} (hS : S.PosSemidef) :
    (realTrace (CFC.sqrt S)) ^ 2 ≤ (Fintype.card n : ℝ) * realTrace S := by
  have h := realTrace_sq_le_card_mul_entryEnergy (CFC.sqrt S)
  rwa [entryEnergy_eq_realTrace_adjoint_mul, (CFC.sqrt_nonneg S).posSemidef.isHermitian.eq,
    CFC.sqrt_mul_sqrt_self S hS.nonneg] at h

theorem density_trace_sqrt_sq_le_card {S : Matrix n n ℂ} (hS : S ∈ densitySet) :
    (realTrace (CFC.sqrt S)) ^ 2 ≤ (Fintype.card n : ℝ) := by
  simpa only [hS.2, mul_one] using trace_sqrt_sq_le_card_mul_trace hS.1

end MatrixSpencer
