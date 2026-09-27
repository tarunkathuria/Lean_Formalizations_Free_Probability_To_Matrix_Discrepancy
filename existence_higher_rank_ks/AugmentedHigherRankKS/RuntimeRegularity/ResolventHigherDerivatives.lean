import HigherRankKS.PowerIntegralDerivatives

/-! All finite derivatives of the actual affine matrix resolvent. These
formulas feed the already proved Bochner-integral formula for matrix powers. -/

open Matrix MatrixSpencer Filter
open scoped Topology BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

noncomputable section
namespace HigherRankKSRuntime.ResolventHigherDerivatives
open MatrixSpencer.KSMovingOwnerHessian

variable {n : Type*} [Fintype n] [DecidableEq n]
local instance : CStarAlgebra (Matrix n n ℂ) := {}

def word (R U : Matrix n n ℂ) : ℕ → Matrix n n ℂ
  | 0 => R
  | k + 1 => word R U k * U * R

theorem word_eq (R U : Matrix n n ℂ) (k : ℕ) : word R U k = (R * U) ^ k * R := by
  induction k with
  | zero => simp [word]
  | succ k ih => rw [word, ih, pow_succ]; simp only [Matrix.mul_assoc]

theorem hasDerivAt_word {f : ℝ → Matrix n n ℂ} {U : Matrix n n ℂ} {t : ℝ}
    (hf : HasDerivAt f (-(f t * U * f t)) t) (k : ℕ) :
    HasDerivAt (fun s => word (f s) U k)
      (-((k : ℝ) + 1) • word (f t) U (k + 1)) t := by
  induction k with
  | zero => simpa [word] using hf
  | succ k ih =>
    have hd := (ih.mul_const U).mul hf
    convert hd using 1
    simp only [word, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_neg,
      Matrix.mul_assoc, Nat.cast_add, Nat.cast_one]
    module

theorem iteratedDeriv_inverseLine (Z U : Matrix n n ℂ) (k : ℕ) (t : ℝ)
    (hZ : IsUnit (transportLine Z U t)) :
    iteratedDeriv k (inverseLine Z U) t =
      ((-1 : ℝ) ^ k * (k.factorial : ℝ)) • word (inverseLine Z U t) U k := by
  induction k generalizing t with
  | zero => simp [word]
  | succ k ih =>
    have hevent : ∀ᶠ s in 𝓝 t, IsUnit (transportLine Z U s) :=
      (hasDerivAt_transportLine Z U t).continuousAt.eventually (Units.isOpen.mem_nhds hZ)
    have heq : iteratedDeriv k (inverseLine Z U) =ᶠ[𝓝 t]
        (fun s => ((-1 : ℝ) ^ k * (k.factorial : ℝ)) • word (inverseLine Z U s) U k) := by
      filter_upwards [hevent] with s hs
      exact ih s hs
    rw [iteratedDeriv_succ, heq.deriv_eq]
    have hd := (hasDerivAt_word (hasDerivAt_inverseLine Z U t hZ) k).const_smul
      ((-1 : ℝ) ^ k * (k.factorial : ℝ))
    change deriv (((-1 : ℝ) ^ k * (k.factorial : ℝ)) •
      (fun s => word (inverseLine Z U s) U k)) t = _
    rw [hd.deriv, smul_smul]
    congr 1
    simp only [pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    ring

theorem iteratedDeriv_resolvent (M U : Matrix n n ℂ) (k : ℕ)
    {t : ℝ} (hM : M.PosDef) (ht : 0 ≤ t) :
    iteratedDeriv k (fun s : ℝ => HigherRankKS.resolvent (M + s • U) t) 0 =
      ((-1 : ℝ) ^ k * (k.factorial : ℝ)) • word (HigherRankKS.resolvent M t) U k := by
  have hQ := hM.add_posSemidef
    (smul_nonneg ht (Matrix.PosDef.one.posSemidef.nonneg)).posSemidef
  have he : (fun s : ℝ => HigherRankKS.resolvent (M + s • U) t) =
      inverseLine (M + t • (1 : Matrix n n ℂ)) U := by
    funext s
    simp [HigherRankKS.resolvent, inverseLine, transportLine, add_right_comm]
  rw [he, iteratedDeriv_inverseLine _ _ _ _ (by simpa [transportLine] using hQ.isUnit)]
  simp [inverseLine, transportLine, HigherRankKS.resolvent]

theorem iteratedDeriv_resolventKernel (M U : Matrix n n ℂ) (k : ℕ)
    {t : ℝ} (hM : M.PosDef) (ht : 0 ≤ t) (hk : 0 < k) :
    iteratedDeriv k (fun s : ℝ => HigherRankKS.resolventKernel (M + s • U) t) 0 =
      ((-1 : ℝ) ^ (k + 1) * (k.factorial : ℝ) * t) •
        word (HigherRankKS.resolvent M t) U k := by
  have hQ := hM.add_posSemidef
    (smul_nonneg ht (Matrix.PosDef.one.posSemidef.nonneg)).posSemidef
  have hf : ContDiffAt ℝ k (fun s : ℝ => HigherRankKS.resolvent (M + s • U) t) 0 := by
    have h := (contDiffAt_inverseLine (M + t • (1 : Matrix n n ℂ)) U hQ.isUnit).of_le
      (WithTop.coe_le_coe.mpr (show (k : ℕ∞) ≤ ⊤ from le_top))
    change ContDiffAt ℝ k (fun s : ℝ => (M + t • 1 + s • U)⁻¹) 0 at h
    convert h using 1
    funext s
    unfold HigherRankKS.resolvent
    congr 1
    abel
  change iteratedDeriv k
    (fun s : ℝ => (1 : Matrix n n ℂ) - t • HigherRankKS.resolvent (M + s • U) t) 0 = _
  rw [iteratedDeriv_const_sub hk, iteratedDeriv_neg]
  change -iteratedDeriv k (t • (fun s : ℝ => HigherRankKS.resolvent (M + s • U) t)) 0 = _
  rw [iteratedDeriv_const_smul hf, iteratedDeriv_resolvent M U k hM ht]
  rw [smul_smul, ← neg_smul]
  congr 1
  rw [pow_succ]
  ring

end HigherRankKSRuntime.ResolventHigherDerivatives
