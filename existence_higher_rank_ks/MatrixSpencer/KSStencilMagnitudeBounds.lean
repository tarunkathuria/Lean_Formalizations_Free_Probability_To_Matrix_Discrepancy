import MatrixSpencer.KSFullManuscriptHessian
import MatrixSpencer.KSJacobiIteration

/-! Magnitude and iteration bounds for the actual finite Hessian stencils.
These intermediate inequalities connect bounded query values and mesh
reciprocals to the numerical Jacobi cutoff. They do not assume bounds on an
unknown exact Hessian, and they do not constitute a whole-walk runtime claim. -/

open Matrix
open scoped BigOperators
noncomputable section
namespace MatrixSpencer.KSStencilMagnitudeBounds

theorem three_value_bound {a b c V t : ℝ}
    (ha : |a| ≤ V) (hb : |b| ≤ V) (hc : |c| ≤ V) :
    |(a-2*b+c)/t^2| ≤ 4*V/t^2 := by
  have hn : |a-2*b+c| ≤ 4*V := by
    rw [abs_le] at ha hb hc ⊢
    constructor <;> linarith
  rw [abs_div, abs_of_nonneg (sq_nonneg t)]
  exact div_le_div_of_nonneg_right hn (sq_nonneg t)

theorem four_value_bound {a b c e V t : ℝ}
    (ha : |a| ≤ V) (hb : |b| ≤ V) (hc : |c| ≤ V) (he : |e| ≤ V) :
    |(a-b-c+e)/(4*t^2)| ≤ V/t^2 := by
  have hn : |a-b-c+e| ≤ 4*V := by
    rw [abs_le] at ha hb hc he ⊢
    constructor <;> linarith
  rw [abs_div, abs_of_nonneg (mul_nonneg (by norm_num) (sq_nonneg t))]
  have h := div_le_div_of_nonneg_right hn
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (sq_nonneg t))
  convert h using 1 <;> ring

theorem offDiagonalEnergy_le_of_entries {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℝ) {V : ℝ} (hV : 0 ≤ V)
    (hA : ∀ i j, |A i j| ≤ V) :
    KSJacobiStep.offDiagonalEnergy A ≤ (d : ℝ)^2*V^2 := by
  calc
    _ ≤ ∑ _i : Fin d, ∑ _j : Fin d, V^2 := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      split_ifs
      · positivity
      · have h := hA i j
        nlinarith [sq_abs (A i j), abs_nonneg (A i j),
          mul_nonneg (sub_nonneg.mpr h) (add_nonneg hV (abs_nonneg (A i j)))]
    _ = _ := by simp; ring

theorem iterationCount_le_of_entries {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℝ) {V τ R : ℝ}
    (hV : 0 ≤ V) (hA : ∀ i j, |A i j| ≤ V)
    (hτ : 1/τ^2 ≤ R) :
    (KSJacobiIteration.iterationCount A τ : ℝ) ≤
      ((d : ℝ)^2+1)*(d : ℝ)^2*V^2*R+1 := by
  have hE := offDiagonalEnergy_le_of_entries A hV hA
  have hden : 0 ≤ KSJacobiIteration.denominator d :=
    (KSJacobiIteration.denominator_pos d).le
  have hnum : 0 ≤ KSJacobiIteration.denominator d * KSJacobiStep.offDiagonalEnergy A :=
    mul_nonneg hden (KSJacobiStep.offDiagonalEnergy_nonneg A)
  have hceil := Nat.ceil_lt_add_one
    (div_nonneg hnum (sq_nonneg τ))
  have hbound : KSJacobiIteration.denominator d * KSJacobiStep.offDiagonalEnergy A / τ^2 ≤
      ((d : ℝ)^2+1)*(d : ℝ)^2*V^2*R := by
    calc
      _ = KSJacobiIteration.denominator d * KSJacobiStep.offDiagonalEnergy A * (1/τ^2) := by ring
      _ ≤ KSJacobiIteration.denominator d * ((d : ℝ)^2*V^2) * R :=
        mul_le_mul (mul_le_mul_of_nonneg_left hE hden) hτ (by positivity) (by positivity)
      _ = _ := by dsimp only [KSJacobiIteration.denominator]; ring
  exact hceil.le.trans (add_le_add_right hbound 1)

end MatrixSpencer.KSStencilMagnitudeBounds
