import HigherRankKSRuntime.Tangent.RuntimeMatrix
import HigherRankKSRuntime.RuntimeSDPValue
import SeamlessKS.ExactEVD
import MatrixSpencer.KSJacobiTraceSqrt

/-! Input square roots use the permitted exact real EVD, scalar square
roots, and the counted matrix multiplication circuits. Complex atoms are
realified as whole matrices and decoded after taking their positive root. -/
open Matrix MatrixSpencer
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace HigherRankKSRuntime.InputFactors
open RealRAM
open RealRAM.JacobiIteration (Counted)
open SeamlessKS.ExactEVD
variable {d : ℕ}
local instance factorCStar {j : Type*} [Fintype j] [DecidableEq j] :
    CStarAlgebra (Matrix j j ℂ) := {}

def rootEntry (i j : Fin d) : Expr (Fin d × Fin d) :=
  if i=j then .sqrt (.input (i,i)) else .constant 0

def diagonalRoot (A : Matrix (Fin d) (Fin d) ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j => (rootEntry i j).eval (fun p => A p.1 p.2)

theorem diagonalRoot_eq (A : Matrix (Fin d) (Fin d) ℝ) :
    diagonalRoot A = Matrix.diagonal (fun i => Real.sqrt (A i i)) := by
  ext i j
  by_cases hij : i = j <;> simp [diagonalRoot,rootEntry,Expr.eval,Matrix.diagonal,hij]

theorem rootEntry_cost (i j : Fin d) : (rootEntry i j).cost ≤ 2 := by
  unfold rootEntry
  split_ifs <;> norm_num [Expr.cost]

theorem rootEntry_executes (A : Matrix (Fin d) (Fin d) ℝ)
    (hdiag : ∀ i,0 ≤ A i i) (i j : Fin d) :
    Expr.Executes (fun p : Fin d × Fin d => A p.1 p.2) (rootEntry i j)
      (diagonalRoot A i j) (rootEntry i j).cost := by
  apply Expr.executes_of_valid
  unfold rootEntry
  split_ifs
  · exact ⟨trivial,hdiag i⟩
  · trivial

def realRoot (A : Matrix (Fin d) (Fin d) ℝ) : Counted (Matrix (Fin d) (Fin d) ℝ) :=
  let e := SeamlessKS.ExactEVD.compute A
  let left := Tangent.RuntimeMatrix.product e.value.2 (diagonalRoot e.value.1)
  let result := Tangent.RuntimeMatrix.product left.value e.value.2ᵀ
  ⟨result.value,e.cost+3*d^2+left.cost+result.cost+3*d^2+1⟩

theorem diagonal_posSemidef (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.PosSemidef) :
    (SeamlessKS.ExactEVD.diagonal A).PosSemidef := by
  simpa only [SeamlessKS.ExactEVD.diagonal,Matrix.conjTranspose,star_trivial] using
    hA.conjTranspose_mul_mul_same (SeamlessKS.ExactEVD.basis A)

theorem realRoot_value (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.PosSemidef) :
    (realRoot A).value = CFC.sqrt A := by
  have hD := diagonal_posSemidef A hA
  have hdiag : ∀ i,0 ≤ SeamlessKS.ExactEVD.diagonal A i i := by
    intro i
    have hh := hD.2 (Pi.single i 1)
    simpa [Matrix.mulVec,dotProduct,Pi.single_apply] using hh
  have hd : CFC.sqrt (SeamlessKS.ExactEVD.diagonal A) =
      diagonalRoot (SeamlessKS.ExactEVD.diagonal A) := by
    conv_lhs => rw [← SeamlessKS.ExactEVD.diagonal_exact A hA.isHermitian]
    rw [KSJacobiRayleigh.diagonalPart,KSJacobiTraceSqrt.sqrt_diagonal _ hdiag,
      diagonalRoot_eq]
  have hs := KSJacobiTraceSqrt.sqrt_orthogonal_conjugation A
    (SeamlessKS.ExactEVD.basis A) hA (SeamlessKS.ExactEVD.basis_right A)
  change CFC.sqrt (SeamlessKS.ExactEVD.diagonal A) =
    (SeamlessKS.ExactEVD.basis A)ᵀ*CFC.sqrt A*SeamlessKS.ExactEVD.basis A at hs
  simp only [realRoot,Tangent.RuntimeMatrix.product_value,SeamlessKS.ExactEVD.compute]
  rw [← hd,hs]
  simp only [Matrix.mul_assoc,← Matrix.mul_assoc (SeamlessKS.ExactEVD.basis A)
    (SeamlessKS.ExactEVD.basis A)ᵀ,SeamlessKS.ExactEVD.basis_right,Matrix.one_mul,
    ← Matrix.mul_assoc,SeamlessKS.ExactEVD.basis_right,Matrix.mul_one]
  rw [Matrix.mul_assoc,SeamlessKS.ExactEVD.basis_right,Matrix.mul_one]

theorem realRoot_cost (A : Matrix (Fin d) (Fin d) ℝ) :
    (realRoot A).cost ≤ 40*(d+1)^3 := by
  have hp := Tangent.RuntimeMatrix.product_cost
    (SeamlessKS.ExactEVD.basis A) (diagonalRoot (SeamlessKS.ExactEVD.diagonal A))
    (b := d+1) (by omega) (by omega) (by omega) (by omega)
  have hq := Tangent.RuntimeMatrix.product_cost
    (Tangent.RuntimeMatrix.product (SeamlessKS.ExactEVD.basis A)
      (diagonalRoot (SeamlessKS.ExactEVD.diagonal A))).value
    (SeamlessKS.ExactEVD.basis A)ᵀ
    (b := d+1) (by omega) (by omega) (by omega) (by omega)
  have hsq : d^2 ≤ (d+1)^3 := by
    calc
      d^2 ≤ (d+1)^2 := Nat.pow_le_pow_left (by omega) 2
      _ ≤ (d+1)^3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hone : 1 ≤ (d+1)^3 := Nat.one_le_pow 3 (d+1) (by omega)
  dsimp only [realRoot,SeamlessKS.ExactEVD.compute]
  omega

def decodeRoot (B : Matrix (Fin (d+d)) (Fin (d+d)) ℝ) : SDPValue.Mat d :=
  fun i j => ⟨B (finSumFinEquiv (.inl i)) (finSumFinEquiv (.inl j)),
    B (finSumFinEquiv (.inr i)) (finSumFinEquiv (.inl j))⟩

def factor (A : SDPValue.Mat d) : Counted (SDPValue.Mat d) :=
  let r := realRoot (KSComplexTraceSqrt.realificationFin A)
  ⟨decodeRoot r.value,r.cost+20*d^2+2⟩

theorem factor_value (A : SDPValue.Mat d) (hA : A.PosSemidef) :
    (factor A).value = CFC.sqrt A := by
  have hr := realRoot_value (KSComplexTraceSqrt.realificationFin A)
    (KSComplexTraceSqrt.realificationFin_posSemidef A hA)
  simp only [factor,hr]
  rw [KSComplexTraceSqrt.realificationFin,KSComplexTraceSqrt.sqrt_submatrix_equiv
    _ (KSComplexTraceSqrt.realification_posSemidef A hA),
    KSComplexTraceSqrt.realification_sqrt A hA]
  ext i j
  simp only [decodeRoot,Matrix.submatrix,Matrix.of_apply,Equiv.symm_apply_apply,
    KSComplexTraceSqrt.realification_inl_inl,KSComplexTraceSqrt.realification_inr_inl]

theorem factor_cost (A : SDPValue.Mat d) :
    (factor A).cost ≤ 1000*(d+1)^3 := by
  have hh := realRoot_cost (KSComplexTraceSqrt.realificationFin A)
  have hhpow : (d+d+1)^3 ≤ (2*(d+1))^3 := Nat.pow_le_pow_left (by omega) 3
  have hsq : d^2 ≤ (d+1)^3 := by
    calc
      d^2 ≤ (d+1)^2 := Nat.pow_le_pow_left (by omega) 2
      _ ≤ (d+1)^3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hone : 1 ≤ (d+1)^3 := Nat.one_le_pow 3 (d+1) (by omega)
  rw [mul_pow] at hhpow
  norm_num at hhpow
  dsimp only [factor]
  omega

def factors {N : ℕ} (A : Fin N → SDPValue.Mat d) : Counted (Fin N → SDPValue.Mat d) :=
  ⟨fun i => (factor (A i)).value,∑ i, (factor (A i)).cost+1⟩

theorem factors_value {N : ℕ} (A : Fin N → SDPValue.Mat d) (hA : ∀ i,(A i).PosSemidef) :
    (factors A).value = fun i => CFC.sqrt (A i) := by
  funext i
  exact factor_value (A i) (hA i)

theorem factors_cost {N : ℕ} (A : Fin N → SDPValue.Mat d) :
    (factors A).cost ≤ 1000*N*(d+1)^3+1 := by
  have hh : (∑ i : Fin N,(factor (A i)).cost) ≤ N*(1000*(d+1)^3) := by
    simpa using Finset.sum_le_sum (s := Finset.univ) (fun i _ => factor_cost (A i))
  dsimp only [factors]
  nlinarith

/-- Reuse the EVD factors already computed for the input. -/
def cachedQuery (O : SDPValue.Solver) {N : ℕ} (B : Fin N → SDPValue.Mat d)
    (k : ℕ) (H : SDPValue.Full d) (c : Fin N → ℝ) (θ ν : ℝ) : Counted ℝ :=
  O.report (k := k) ⟨B,H,c,θ⟩ ν

theorem cachedQuery_eq (O : SDPValue.Solver) {N : ℕ} (A : Fin N → SDPValue.Mat d)
    (hA : ∀ i,(A i).PosSemidef) (k : ℕ) (H : SDPValue.Full d)
    (c : Fin N → ℝ) (θ ν : ℝ) :
    cachedQuery O (factors A).value k H c θ ν = SDPValue.query O A k H c θ ν := by
  rw [factors_value A hA]
  rfl

theorem cachedQuery_accuracy (O : SDPValue.Solver) {N : ℕ}
    (A : Fin N → SDPValue.Mat d) (hA : ∀ i,(A i).PosSemidef)
    (k : ℕ) (H : SDPValue.Full d) (hd : 0 < d) (hk : 1 ≤ k)
    {c : Fin N → ℝ} (hc : ∀ i,0 ≤ c i) {θ ν : ℝ}
    (hθ : 0 < θ) (hν : 0 < ν) :
    |(cachedQuery O (factors A).value k H c θ ν).value -
      AugmentedHigherRankKS.potential H A ((1:ℝ)/2^k) c θ| ≤ ν := by
  rw [cachedQuery_eq O A hA]
  exact SDPValue.query_accuracy O A k H hd hk hc hθ hν

theorem cachedQuery_cost (O : SDPValue.Solver) {N : ℕ} (B : Fin N → SDPValue.Mat d)
    (k : ℕ) (H : SDPValue.Full d) (c : Fin N → ℝ) (θ : ℝ)
    {ν : ℝ} (hν : 0 < ν) :
    (cachedQuery O B k H c θ ν).cost ≤
      O.coefficient*(SDPValue.dataSize N d k+⌈ν⁻¹⌉₊+1)^O.degree :=
  O.work_bound _ _ hν

end HigherRankKSRuntime.InputFactors

