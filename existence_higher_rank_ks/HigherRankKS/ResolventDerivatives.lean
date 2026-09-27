import MatrixSpencer.KSMovingOwnerHessian
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Resolvent derivatives and their pointwise Gram representation

The inverse is differentiated as an actual matrix function. The Gram
identities allow rectangular output maps. Passing these identities through
the power integral requires separate integrability and differentiation
arguments.
-/

open Matrix MatrixSpencer
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

noncomputable section
namespace HigherRankKS

variable {n m : Type*} [Fintype n] [DecidableEq n]
local instance resolventDerivativeCStar : CStarAlgebra (Matrix n n ℂ) := {}

def resolvent (M : Matrix n n ℂ) (t : ℝ) : Matrix n n ℂ :=
  (M + t • (1 : Matrix n n ℂ))⁻¹

def resolventKernel (M : Matrix n n ℂ) (t : ℝ) : Matrix n n ℂ :=
  1 - t • resolvent M t

theorem resolvent_posDef {M : Matrix n n ℂ} (hM : M.PosDef)
    {t : ℝ} (ht : 0 ≤ t) : (resolvent M t).PosDef :=
  (hM.add_posSemidef (smul_nonneg ht (Matrix.PosDef.one.posSemidef.nonneg)).posSemidef).inv

theorem resolventKernel_eq_mul {M : Matrix n n ℂ} (hM : M.PosDef)
    {t : ℝ} (ht : 0 ≤ t) :
    resolventKernel M t = M * resolvent M t := by
  have hQ := hM.add_posSemidef
    (smul_nonneg ht (Matrix.PosDef.one.posSemidef.nonneg)).posSemidef
  letI : Invertible (M + t • (1 : Matrix n n ℂ)) := hQ.isUnit.invertible
  have h := Matrix.mul_inv_of_invertible (M + t • (1 : Matrix n n ℂ))
  simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul] at h
  dsimp [resolventKernel, resolvent]
  exact sub_eq_iff_eq_add.mpr h.symm

theorem hasDerivAt_resolvent_curve {M : Matrix n n ℂ} (hM : M.PosDef)
    (U : Matrix n n ℂ) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun s : ℝ => resolvent (M + s • U) t)
      (-(resolvent M t * U * resolvent M t)) 0 := by
  have hQ := hM.add_posSemidef
    (smul_nonneg ht (Matrix.PosDef.one.posSemidef.nonneg)).posSemidef
  have h := KSMovingOwnerHessian.hasDerivAt_inverseLine
    (M + t • (1 : Matrix n n ℂ)) U 0
    (by simpa [KSMovingOwnerHessian.transportLine] using hQ.isUnit)
  unfold KSMovingOwnerHessian.inverseLine KSMovingOwnerHessian.transportLine at h
  simpa only [resolvent, zero_smul, add_zero, add_right_comm] using h

theorem hasDerivAt_resolventKernel_curve {M : Matrix n n ℂ} (hM : M.PosDef)
    (U : Matrix n n ℂ) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun s : ℝ => resolventKernel (M + s • U) t)
      (t • (resolvent M t * U * resolvent M t)) 0 := by
  have h := ((hasDerivAt_resolvent_curve hM U ht).const_smul t).const_sub
    (1 : Matrix n n ℂ)
  simpa [resolventKernel] using h

theorem iteratedDeriv_two_resolventKernel_curve
    {M : Matrix n n ℂ} (hM : M.PosDef)
    (U : Matrix n n ℂ) {t : ℝ} (ht : 0 ≤ t) :
    iteratedDeriv 2 (fun s : ℝ => resolventKernel (M + s • U) t) 0 =
      (-2 * t) • (resolvent M t * U * resolvent M t * U * resolvent M t) := by
  let Q := M + t • (1 : Matrix n n ℂ)
  have hQ : Q.PosDef := hM.add_posSemidef
    (smul_nonneg ht (Matrix.PosDef.one.posSemidef.nonneg)).posSemidef
  have heq : (fun s : ℝ => resolventKernel (M + s • U) t) =
      fun s => 1 - t • KSMovingOwnerHessian.inverseLine Q U s := by
    funext s
    simp [resolventKernel, resolvent, KSMovingOwnerHessian.inverseLine,
      KSMovingOwnerHessian.transportLine, Q, add_right_comm]
  rw [heq, iteratedDeriv_const_sub (by norm_num), iteratedDeriv_neg]
  change -(iteratedDeriv 2 (t • KSMovingOwnerHessian.inverseLine Q U) 0) = _
  rw [iteratedDeriv_const_smul
    ((KSMovingOwnerHessian.contDiffAt_inverseLine Q U hQ.isUnit).of_le (by
      change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
      exact WithTop.coe_le_coe.mpr le_top)),
    KSMovingOwnerHessian.iteratedDeriv_two_inverseLine Q U hQ.isUnit]
  simp only [smul_smul, ← neg_smul]
  congr 1
  ring

/-- An unweighted resolvent column with an arbitrary rectangular output map. -/
def resolventColumn (K : Matrix m n ℂ) (R U : Matrix n n ℂ) : Matrix m n ℂ :=
  K * R * U * CFC.sqrt R

theorem resolventColumn_product (K : Matrix m n ℂ)
    {R U V : Matrix n n ℂ} (hR : R.PosSemidef)
    (hV : V.IsHermitian) :
    resolventColumn K R U * (resolventColumn K R V)ᴴ =
      K * R * U * R * V * R * Kᴴ := by
  simp only [resolventColumn, Matrix.conjTranspose_mul, hV.eq, hR.isHermitian.eq,
    (CFC.sqrt_nonneg R).posSemidef.isHermitian.eq]
  calc
    _ = K * R * U * (CFC.sqrt R * CFC.sqrt R) * V * R * Kᴴ := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [CFC.sqrt_mul_sqrt_self R hR.nonneg]

theorem resolventColumn_crossGram (K : Matrix m n ℂ)
    {R U V : Matrix n n ℂ} (hR : R.PosSemidef)
    (hU : U.IsHermitian) (hV : V.IsHermitian) :
    resolventColumn K R U * (resolventColumn K R V)ᴴ +
      resolventColumn K R V * (resolventColumn K R U)ᴴ =
      K * R * (U * R * V + V * R * U) * R * Kᴴ := by
  rw [resolventColumn_product K hR hV, resolventColumn_product K hR hU]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]

end HigherRankKS
