import MatrixSpencer.DyadicTsallisBounds
import MatrixSpencer.DyadicInverseKernelBound

/-! Positivity and a compression-compatible bound for the actual Hessian;
strict concavity in the positive cone and concavity at singular endpoints. -/
open Matrix Set
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
namespace MatrixSpencer
noncomputable section
variable {n : Type*} [Fintype n] [DecidableEq n]
local instance dyadicConcavityCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance dyadicConcavitySpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance

theorem inverse_negativeDyadicTsallisHessian_quadratic_pos (m : ℕ) (θ : ℝ) (hθ : 0 < θ)
    (S B : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef) (hB : B ≠ 0) :
    0 < realTrace ((B : Matrix n n ℂ) *
      ((negativeDyadicTsallisHessianEquiv m θ hθ.ne' S hS).symm B : Matrix n n ℂ)) := by
  rw [negativeDyadicTsallisHessianEquiv_symm_apply, Matrix.mul_smul, realTrace_smul]
  apply mul_pos (inv_pos.mpr hθ)
  have hB' : (B : Matrix n n ℂ) ≠ 0 := fun h => hB (Subtype.ext h)
  have h := DyadicInverseKernelBound.polynomialInverse_quadratic_pos
    (pow_pos (by norm_num : (0 : ℕ) < 2) m) (dyadicRoot_posDef m hS) hB'
  simpa only [show (B : Matrix n n ℂ)ᴴ = B from B.property,
    DyadicInverseKernelBound.polynomialInverse] using h

theorem negativeDyadicTsallisHessian_quadratic_pos (m : ℕ) (θ : ℝ) (hθ : 0 < θ)
    (S X : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef) (hX : X ≠ 0) :
    0 < realTrace ((X : Matrix n n ℂ) *
      (negativeDyadicTsallisHessianEquiv m θ hθ.ne' S hS X : Matrix n n ℂ)) := by
  have hB : negativeDyadicTsallisHessianEquiv m θ hθ.ne' S hS X ≠ 0 := by
    intro he
    apply hX
    exact (negativeDyadicTsallisHessianEquiv m θ hθ.ne' S hS).injective
      (he.trans (map_zero _).symm)
  have h := inverse_negativeDyadicTsallisHessian_quadratic_pos m θ hθ S
    (negativeDyadicTsallisHessianEquiv m θ hθ.ne' S hS X) hS hB
  rw [ContinuousLinearEquiv.symm_apply_apply, realTrace_mul_comm] at h
  exact h

/-- The actual inverse Hessian is bounded by the explicit model with coefficient p/(2θ). -/
theorem inverse_negativeDyadicTsallisHessian_le_model (m : ℕ) (θ : ℝ) (hθ : 0 < θ)
    (S B : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef) :
    realTrace ((B : Matrix n n ℂ) *
      ((negativeDyadicTsallisHessianEquiv m θ hθ.ne' S hS).symm B : Matrix n n ℂ)) ≤
      realTrace ((B : Matrix n n ℂ) * DyadicCurvatureCompression.inverseModel m
        ((2 ^ m : ℝ) / (2 * θ)) (S : Matrix n n ℂ) B) := by
  rw [negativeDyadicTsallisHessianEquiv_symm_apply, Matrix.mul_smul, realTrace_smul]
  have h := mul_le_mul_of_nonneg_left
    (DyadicInverseKernelBound.dyadic_polynomialInverse_le_model m hS.posSemidef B.property)
    (inv_nonneg.mpr hθ.le)
  convert h using 1
  simp only [DyadicCurvatureCompression.inverseModel, Matrix.mul_smul, realTrace_smul,
    Nat.cast_pow, Nat.cast_ofNat]
  ring

theorem fderiv_fderiv_dyadicTsallisPotential_quadratic_neg (m : ℕ) (hm : 1 ≤ m)
    (θ : ℝ) (hθ : 0 < θ) (S X : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) (hX : X ≠ 0) :
    fderiv ℝ (fderiv ℝ (dyadicTsallisPotential m θ)) S X X < 0 := by
  rw [fderiv_fderiv_dyadicTsallisPotential_apply m hm θ hθ.ne' S X X hS,
    realTrace_mul_comm]
  exact neg_neg_of_pos (negativeDyadicTsallisHessian_quadratic_pos m θ hθ S X hS hX)

theorem strictConcaveOn_dyadicTsallisPotential_posDef (m : ℕ) (hm : 1 ≤ m)
    (θ : ℝ) (hθ : 0 < θ) :
    StrictConcaveOn ℝ hermitianPositiveCone (dyadicTsallisPotential (n := n) m θ) := by
  apply strictConcaveOn_of_fderiv2_neg convex_hermitianPositiveCone isOpen_hermitianPositiveCone
  · intro S hS
    exact (contDiffAt_dyadicTsallisPotential m θ S hS).differentiableAt (by simp)
  · intro S hS
    have hd : ContDiffAt ℝ ∞ (fun T => fderiv ℝ (dyadicTsallisPotential m θ) T) S :=
      (contDiffAt_dyadicTsallisPotential m θ S hS).fderiv_right (by simp)
    exact hd.differentiableAt (by simp)
  · intro S hS X hX
    exact fderiv_fderiv_dyadicTsallisPotential_quadratic_neg m hm θ hθ S X hS hX

theorem concaveOn_dyadicTsallisPotential (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (hθ : 0 < θ) :
    ConcaveOn ℝ hermitianSemidefiniteCone (dyadicTsallisPotential (n := n) m θ) :=
  concaveOn_hermitianSemidefiniteCone_of_posDef (continuousOn_dyadicTsallisPotential m θ)
    (strictConcaveOn_dyadicTsallisPotential_posDef m hm θ hθ).concaveOn

theorem dyadicTsallisRegularizer_concave (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (hθ : 0 < θ)
    {S T : Matrix n n ℂ} (hS : S.PosSemidef) (hT : T.PosSemidef)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a * dyadicTsallisRegularizer m θ S + b * dyadicTsallisRegularizer m θ T ≤
      dyadicTsallisRegularizer m θ (a • S + b • T) :=
  (concaveOn_dyadicTsallisPotential m hm θ hθ).2
    (x := ⟨S, hS.isHermitian⟩) (y := ⟨T, hT.isHermitian⟩) hS hT ha hb hab

theorem dyadicTsallisRegularizer_strict_concave_posDef (m : ℕ) (hm : 1 ≤ m)
    (θ : ℝ) (hθ : 0 < θ) {S T : Matrix n n ℂ} (hS : S.PosDef) (hT : T.PosDef)
    (hne : S ≠ T) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    a * dyadicTsallisRegularizer m θ S + b * dyadicTsallisRegularizer m θ T <
      dyadicTsallisRegularizer m θ (a • S + b • T) := by
  apply (strictConcaveOn_dyadicTsallisPotential_posDef m hm θ hθ).2
    (x := ⟨S, hS.isHermitian⟩) (y := ⟨T, hT.isHermitian⟩) hS hT _ ha hb hab
  intro he
  exact hne (congrArg Subtype.val he)

theorem concaveOn_dyadicTsallisRegularizer (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (hθ : 0 < θ) :
    ConcaveOn ℝ {S : Matrix n n ℂ | S.PosSemidef} (dyadicTsallisRegularizer m θ) := by
  constructor
  · intro S hS T hT a b ha hb _
    exact posSemidef_weighted_add hS hT ha hb
  · intro S hS T hT a b ha hb hab
    exact dyadicTsallisRegularizer_concave m hm θ hθ hS hT ha hb hab

end
end MatrixSpencer
