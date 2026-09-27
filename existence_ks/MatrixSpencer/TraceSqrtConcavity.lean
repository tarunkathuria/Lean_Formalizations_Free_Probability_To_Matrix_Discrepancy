import MatrixSpencer.SqrtCompression
import MatrixSpencer.DensityDomain
import Mathlib.Analysis.Convex.Function
import Mathlib.Tactic.Module

/-!
# Strict concavity of the trace square root

An algebraic square identity proves operator concavity. Equality of traces
forces equality of the positive matrix gap, and hence equality of both square
roots. This proves strictness directly on the full positive semidefinite cone;
no strict inequality is inferred from a limiting argument.
-/

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

namespace MatrixSpencer

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- The real trace is faithful on positive semidefinite matrices. -/
theorem posSemidef_eq_zero_of_realTrace_eq_zero {A : Matrix n n ℂ}
    (hA : A.PosSemidef) (htrace : realTrace A = 0) : A = 0 := by
  apply hA.trace_eq_zero_iff.mp
  apply RCLike.ext
  · simpa only [realTrace, map_zero] using htrace
  · simpa only [map_zero] using (RCLike.nonneg_iff.mp hA.trace_nonneg).2

omit [DecidableEq n] in
/-- Equality of traces detects equality in Loewner order. -/
theorem matrix_eq_of_le_of_realTrace_eq {A B : Matrix n n ℂ}
    (hAB : A ≤ B) (htrace : realTrace A = realTrace B) : A = B := by
  have hz : realTrace (B - A) = 0 := by rw [realTrace_sub, htrace, sub_self]
  exact (sub_eq_zero.mp
    (posSemidef_eq_zero_of_realTrace_eq_zero (Matrix.le_iff.mp hAB) hz)).symm

omit [DecidableEq n] in
/-- The exact noncommutative gap in the square of a convex combination. -/
theorem matrix_convex_square_gap (X Y : Matrix n n ℂ)
    {a b : ℝ} (hab : a + b = 1) :
    a • (X * X) + b • (Y * Y) - (a • X + b • Y) * (a • X + b • Y) =
      (a * b) • ((X - Y) * (X - Y)) := by
  have hb : b = 1 - a := by linarith
  rw [hb]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.sub_mul, Matrix.mul_sub]
  module

/-- Operator concavity of the positive square root, including singular endpoints. -/
theorem matrix_sqrt_concave {S T : Matrix n n ℂ}
    (hS : S.PosSemidef) (hT : T.PosSemidef)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a • CFC.sqrt S + b • CFC.sqrt T ≤ CFC.sqrt (a • S + b • T) := by
  letI : CStarAlgebra (Matrix n n ℂ) := {}
  let Q := a • CFC.sqrt S + b • CFC.sqrt T
  have hQ : Q.PosSemidef :=
    (add_nonneg (smul_nonneg ha (CFC.sqrt_nonneg S))
      (smul_nonneg hb (CFC.sqrt_nonneg T))).posSemidef
  have hD : (CFC.sqrt S - CFC.sqrt T).IsHermitian :=
    (CFC.sqrt_nonneg S).posSemidef.isHermitian.sub
      (CFC.sqrt_nonneg T).posSemidef.isHermitian
  have hgap := matrix_convex_square_gap (CFC.sqrt S) (CFC.sqrt T) hab
  rw [CFC.sqrt_mul_sqrt_self S hS.nonneg, CFC.sqrt_mul_sqrt_self T hT.nonneg] at hgap
  have hsquare : Q ^ 2 ≤ a • S + b • T := by
    apply Matrix.le_iff.mpr
    rw [pow_two]
    change (a • S + b • T -
      (a • CFC.sqrt S + b • CFC.sqrt T) *
        (a • CFC.sqrt S + b • CFC.sqrt T)).PosSemidef
    rw [hgap]
    have hpos := Matrix.posSemidef_conjTranspose_mul_self (CFC.sqrt S - CFC.sqrt T)
    rw [hD.eq] at hpos
    exact (smul_nonneg (mul_nonneg ha hb) hpos.nonneg).posSemidef
  have h := CFC.sqrt_le_sqrt (Q ^ 2) (a • S + b • T) hsquare
  simpa only [CFC.sqrt_sq Q hQ.nonneg] using h

/-- The scalar trace square-root concavity inequality. -/
theorem trace_sqrt_concave {S T : Matrix n n ℂ}
    (hS : S.PosSemidef) (hT : T.PosSemidef)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a * realTrace (CFC.sqrt S) + b * realTrace (CFC.sqrt T) ≤
      realTrace (CFC.sqrt (a • S + b • T)) := by
  have h := realTrace_nonneg (Matrix.le_iff.mp (matrix_sqrt_concave hS hT ha hb hab))
  rw [realTrace_sub, realTrace_add, realTrace_smul, realTrace_smul] at h
  linarith

/-- Equality in trace square-root concavity with positive weights forces equal inputs. -/
theorem eq_of_trace_sqrt_concavity_eq {S T : Matrix n n ℂ}
    (hS : S.PosSemidef) (hT : T.PosSemidef)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
    (heq : a * realTrace (CFC.sqrt S) + b * realTrace (CFC.sqrt T) =
      realTrace (CFC.sqrt (a • S + b • T))) : S = T := by
  have hQeq : a • CFC.sqrt S + b • CFC.sqrt T = CFC.sqrt (a • S + b • T) := by
    apply matrix_eq_of_le_of_realTrace_eq (matrix_sqrt_concave hS hT ha.le hb.le hab)
    simpa only [realTrace_add, realTrace_smul] using heq
  have hmix : (a • S + b • T).PosSemidef :=
    (add_nonneg (smul_nonneg ha.le hS.nonneg) (smul_nonneg hb.le hT.nonneg)).posSemidef
  have hgap := matrix_convex_square_gap (CFC.sqrt S) (CFC.sqrt T) hab
  rw [CFC.sqrt_mul_sqrt_self S hS.nonneg, CFC.sqrt_mul_sqrt_self T hT.nonneg,
    hQeq, CFC.sqrt_mul_sqrt_self (a • S + b • T) hmix.nonneg, sub_self] at hgap
  have hDsq : (CFC.sqrt S - CFC.sqrt T) * (CFC.sqrt S - CFC.sqrt T) = 0 :=
    (smul_eq_zero.mp hgap.symm).resolve_left (mul_ne_zero ha.ne' hb.ne')
  have hD : (CFC.sqrt S - CFC.sqrt T).IsHermitian :=
    (CFC.sqrt_nonneg S).posSemidef.isHermitian.sub
      (CFC.sqrt_nonneg T).posSemidef.isHermitian
  have hroots : CFC.sqrt S = CFC.sqrt T := by
    apply sub_eq_zero.mp
    apply (realTrace_conjTranspose_mul_self_eq_zero_iff (CFC.sqrt S - CFC.sqrt T)).mp
    rw [hD.eq, hDsq, realTrace_zero]
  calc
    S = CFC.sqrt S * CFC.sqrt S := (CFC.sqrt_mul_sqrt_self S hS.nonneg).symm
    _ = CFC.sqrt T * CFC.sqrt T := by rw [hroots]
    _ = T := CFC.sqrt_mul_sqrt_self T hT.nonneg

/-- Strictness holds for all distinct PSD inputs, including singular endpoints. -/
theorem trace_sqrt_strict_concave {S T : Matrix n n ℂ}
    (hS : S.PosSemidef) (hT : T.PosSemidef) (hne : S ≠ T)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    a * realTrace (CFC.sqrt S) + b * realTrace (CFC.sqrt T) <
      realTrace (CFC.sqrt (a • S + b • T)) := by
  apply lt_of_le_of_ne (trace_sqrt_concave hS hT ha.le hb.le hab)
  intro heq
  exact hne (eq_of_trace_sqrt_concavity_eq hS hT ha hb hab heq)

/-- Strict concavity packaged on the entire positive semidefinite cone. -/
theorem strictConcaveOn_trace_sqrt :
    StrictConcaveOn ℝ {S : Matrix n n ℂ | S.PosSemidef}
      (fun S => realTrace (CFC.sqrt S)) := by
  refine ⟨?_, ?_⟩
  · intro S hS T hT a b ha hb _
    exact (add_nonneg (smul_nonneg ha hS.nonneg) (smul_nonneg hb hT.nonneg)).posSemidef
  · intro S hS T hT hne a b ha hb hab
    exact trace_sqrt_strict_concave hS hT hne ha hb hab

/-- In particular the actual trace square root is strictly concave on all densities. -/
theorem strictConcaveOn_density_trace_sqrt :
    StrictConcaveOn ℝ (densitySet : Set (Matrix n n ℂ))
      (fun S => realTrace (CFC.sqrt S)) := by
  exact strictConcaveOn_trace_sqrt.subset (fun _ hS => hS.1) densitySet_convex

end MatrixSpencer
