import HigherRankKSRuntime.Tangent.Frame
import HigherRankKSRuntime.Tangent.RestrictedEVD

/-! Scalar and matrix formulas for evaluating the radial frame and compression. -/
open Matrix
open scoped BigOperators
noncomputable section
namespace HigherRankKSRuntime.Tangent.FrameFormula
open RadialBasis (Space)
variable {m r : ℕ}

def columns (U : Space r →ₗᵢ[ℝ] Space m) : Matrix (Fin m) (Fin r) ℝ :=
  fun i j => U (EuclideanSpace.single j 1) i

theorem reconstruct (v : Space r) :
    (∑ j, v j • EuclideanSpace.single j 1) = v := by
  simpa using (EuclideanSpace.basisFun (Fin r) ℝ).sum_repr v

theorem apply_columns (U : Space r →ₗᵢ[ℝ] Space m) (v : Space r) :
    U v = WithLp.toLp 2 (columns U *ᵥ WithLp.ofLp v) := by
  conv_lhs => rw [← reconstruct v]
  rw [map_sum]
  simp only [map_smul]
  ext i
  change (PiLp.projₗ (𝕜 := ℝ) 2 (fun _ : Fin m => ℝ) i)
    (∑ j, v j • U (EuclideanSpace.single j 1)) = _
  rw [map_sum]
  simp [Matrix.mulVec, dotProduct, columns, mul_comm]

theorem entry_inner (A : Matrix (Fin m) (Fin m) ℝ) (i j : Fin m) :
    A i j = inner ℝ (EuclideanSpace.single i 1)
      (Matrix.toEuclideanCLM (𝕜 := ℝ) A (EuclideanSpace.single j 1)) := by
  rw [EuclideanSpace.inner_single_left]
  simp only [starRingEnd_apply, star_trivial, one_mul]
  change A i j = (A *ᵥ Pi.single j 1) i
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

theorem compression_entries (U : Space r →ₗᵢ[ℝ] Space m)
    (A : Matrix (Fin m) (Fin m) ℝ) (i j : Fin r) :
    RestrictedEVD.compression U A i j =
      ∑ a, columns U a i * ∑ b, A a b * columns U b j := by
  rw [entry_inner (RestrictedEVD.compression U A) i j, RestrictedEVD.compression,
    StarAlgEquiv.apply_symm_apply]
  simp only [ContinuousLinearMap.comp_apply]
  rw [U.toContinuousLinearMap.adjoint_inner_right]
  simp only [PiLp.inner_apply, RCLike.inner_apply', Matrix.toEuclideanCLM_toLp,
    Matrix.mulVec, dotProduct, columns]
  rfl

theorem compression_matrix (U : Space r →ₗᵢ[ℝ] Space m)
    (A : Matrix (Fin m) (Fin m) ℝ) :
    RestrictedEVD.compression U A = (columns U)ᵀ * A * columns U := by
  ext i j
  rw [compression_entries]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum, mul_assoc]

theorem householder_denominator (q : Space (m + 1)) (hq : ‖q‖ = 1) :
    2 ≤ ‖q - RadialBasis.target q‖ ^ 2 := by
  rw [norm_sub_sq_real, hq, RadialBasis.target_norm]
  rw [RadialBasis.target, EuclideanSpace.inner_single_right]
  simp only [starRingEnd_apply, star_trivial]
  unfold RadialBasis.sign
  split_ifs with h <;> nlinarith

theorem householder_apply (q : Space (m + 1)) (v : Space m) (i : Fin (m + 1)) :
    RadialBasis.embedding q v i = RadialBasis.pad v i -
      (2 * (∑ j, (q j - RadialBasis.target q j) * RadialBasis.pad v j) /
        (∑ j, (q j - RadialBasis.target q j) ^ 2)) * (q i - RadialBasis.target q i) := by
  change RadialBasis.reflection q (RadialBasis.pad v) i = _
  rw [RadialBasis.reflection_formula]
  simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
    EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs, PiLp.inner_apply,
    RCLike.inner_apply, starRingEnd_apply, star_trivial, mul_comm]

end HigherRankKSRuntime.Tangent.FrameFormula
