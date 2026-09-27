import MatrixSpencer.Statement

/-!
# The two Kadison–Singer signing targets

These are target propositions, not assertions of a completed proof. The
input atoms are explicitly outer products of complex vectors, including
zero vectors. The Parseval condition uses the unnormalized identity and
every norm is the Euclidean operator norm from `Statement`.

The two constants belong to two different proof routes: truncated owners
on the cube of radius 1/8, and spin-coupled natural owners on the unit cube.
-/

open scoped BigOperators Matrix

namespace MatrixSpencer

/-- An explicitly specified rank-at-most-one positive atom. -/
def KSIsRankOneAtom {d : ℕ} (A : CMatrix d) : Prop :=
  ∃ v : Fin d → ℂ, ∀ a b, A a b = v a * star (v b)

/-- Full Kadison–Singer signing, with a prescribed numerical constant.
There is no matrix-count/dimension restriction and no lower atom-size bound. -/
def ksStatementWithConstant (C : ℝ) : Prop :=
  ∀ (N d : ℕ) (ε : ℝ), 0 < ε →
    ∀ A : Fin N → CMatrix d,
      (∀ i, KSIsRankOneAtom (A i)) →
      (∑ i, A i) = 1 →
      (∀ i, spectralNorm (A i) ≤ ε) →
      ∃ s : Fin N → ℝ, IsFullSigning s ∧
        spectralNorm (signedSum A s) ≤ C * Real.sqrt ε

/-- Target of the rescaled-cube result, whose terminal coefficients are multiplied by eight. -/
def ksEighthStatement : Prop := ksStatementWithConstant 144

/-- Target of the augmented-covariance proof with genuine unit-cube endpoints. -/
def ksSpinMixedStatement : Prop :=
  ksStatementWithConstant (16 * Real.sqrt 2 + 2)

theorem ksIsRankOneAtom_isHermitian {d : ℕ} {A : CMatrix d}
    (hA : KSIsRankOneAtom A) : A.IsHermitian := by
  obtain ⟨v, hv⟩ := hA
  ext a b
  simp only [Matrix.conjTranspose_apply, hv, star_mul, star_star]

theorem ksSpinMixedConstant_pos : 0 < 16 * Real.sqrt 2 + 2 := by
  positivity

theorem ksSpinMixedConstant_le_eighthConstant : 16 * Real.sqrt 2 + 2 ≤ 144 := by
  have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have h0 := Real.sqrt_nonneg (2 : ℝ)
  nlinarith

end MatrixSpencer
