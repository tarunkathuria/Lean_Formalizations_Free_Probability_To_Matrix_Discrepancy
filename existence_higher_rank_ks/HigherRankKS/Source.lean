import HigherRankKS.CarrierPower
import MatrixSpencer.SignedLift

/-!
# The actual higher-rank two-spin source

The two density blocks are added before the nonlinear power is applied.
There is exactly one source term and one scalar coefficient per original
input matrix. No rank-one decomposition creates extra signing decisions.
-/

open Matrix MatrixSpencer
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

noncomputable section
namespace HigherRankKS

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
local instance sourceCStar {k : Type*} [Fintype k] [DecidableEq k] :
    CStarAlgebra (Matrix k k ℂ) := {}

/-- Physical density obtained by tracing out the two-valued spin. -/
def marginal (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) : Matrix n n ℂ :=
  S.toBlocks₁₁ + S.toBlocks₂₂

omit [DecidableEq n] in
theorem marginal_posSemidef {S : Matrix (n ⊕ n) (n ⊕ n) ℂ}
    (hS : S.PosSemidef) : (marginal S).PosSemidef := by
  exact (hS.submatrix Sum.inl).add (hS.submatrix Sum.inr)

/-- Carrier matrix in the full physical space; it vanishes off the input's range. -/
def carrier (A : Matrix n n ℂ) (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) :
    Matrix n n ℂ :=
  CFC.sqrt A * marginal S * CFC.sqrt A

theorem carrier_posSemidef (A : Matrix n n ℂ)
    {S : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hS : S.PosSemidef) :
    (carrier A S).PosSemidef := by
  simpa only [carrier, (CFC.sqrt_nonneg A).posSemidef.isHermitian.eq] using
    (marginal_posSemidef hS).conjTranspose_mul_mul_same (CFC.sqrt A)

/-- One physical output block, before duplication over the two spins. -/
def sourceBlock (β : ℝ) (A : Matrix n n ℂ)
    (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) : Matrix n n ℂ :=
  CFC.sqrt A * carrierPower β (carrier A S) * CFC.sqrt A

theorem sourceBlock_posSemidef (β : ℝ) (A : Matrix n n ℂ)
    {S : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hS : S.PosSemidef) :
    (sourceBlock β A S).PosSemidef := by
  simpa only [sourceBlock, (CFC.sqrt_nonneg A).posSemidef.isHermitian.eq] using
    (carrierPower_posSemidef β (carrier_posSemidef A hS)).conjTranspose_mul_mul_same
      (CFC.sqrt A)

/-- The unweighted source belonging to a single original matrix. -/
def sourceTerm (β : ℝ) (A : Matrix n n ℂ)
    (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) : Matrix (n ⊕ n) (n ⊕ n) ℂ :=
  Matrix.fromBlocks (sourceBlock β A S) 0 0 (sourceBlock β A S)

theorem sourceTerm_posSemidef (β : ℝ) (A : Matrix n n ℂ)
    {S : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hS : S.PosSemidef) :
    (sourceTerm β A S).PosSemidef :=
  posSemidef_fromBlocks_diagonal (sourceBlock_posSemidef β A hS)
    (sourceBlock_posSemidef β A hS)

/-- The total source for scalar weights indexed by original matrix labels. -/
def source (A : ι → Matrix n n ℂ) (β : ℝ) (c : ι → ℝ)
    (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) : Matrix (n ⊕ n) (n ⊕ n) ℂ :=
  ∑ i, c i • sourceTerm β (A i) S

theorem source_posSemidef (A : ι → Matrix n n ℂ) (β : ℝ)
    {c : ι → ℝ} (hc : ∀ i, 0 ≤ c i)
    {S : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hS : S.PosSemidef) :
    (source A β c S).PosSemidef := by
  apply Matrix.nonneg_iff_posSemidef.mp
  exact Finset.sum_nonneg (fun i _ =>
    smul_nonneg (hc i) (sourceTerm_posSemidef β (A i) hS).nonneg)

@[simp] theorem source_zero_weights (A : ι → Matrix n n ℂ) (β : ℝ)
    (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) :
    source A β (fun _ => 0) S = 0 := by
  simp [source]

omit [Fintype n] [DecidableEq n] in
theorem continuous_marginal : Continuous
    (marginal : Matrix (n ⊕ n) (n ⊕ n) ℂ → Matrix n n ℂ) := by
  change Continuous (fun S : Matrix (n ⊕ n) (n ⊕ n) ℂ =>
    fun i j => S (Sum.inl i) (Sum.inl j) + S (Sum.inr i) (Sum.inr j))
  fun_prop

theorem continuous_carrier (A : Matrix n n ℂ) : Continuous (carrier A) := by
  exact (continuous_const.mul continuous_marginal).mul continuous_const

theorem continuous_sourceBlock_of_psd {X : Type*} [TopologicalSpace X]
    (A : Matrix n n ℂ) {S : X → Matrix (n ⊕ n) (n ⊕ n) ℂ}
    (hS : Continuous S) (hpos : ∀ x, (S x).PosSemidef)
    {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1) :
    Continuous (fun x => sourceBlock β A (S x)) := by
  have hp := continuous_carrierPower_of_psd ((continuous_carrier A).comp hS)
    (fun x => carrier_posSemidef A (hpos x)) hβ hβ1
  exact (continuous_const.mul hp).mul continuous_const

theorem continuous_sourceTerm_of_psd {X : Type*} [TopologicalSpace X]
    (A : Matrix n n ℂ) {S : X → Matrix (n ⊕ n) (n ⊕ n) ℂ}
    (hS : Continuous S) (hpos : ∀ x, (S x).PosSemidef)
    {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1) :
    Continuous (fun x => sourceTerm β A (S x)) := by
  have hb := continuous_sourceBlock_of_psd A hS hpos hβ hβ1
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      change Continuous (fun x => sourceBlock β A (S x) i j)
      exact (continuous_apply j).comp ((continuous_apply i).comp hb)
    | inr j => exact continuous_const
  | inr i =>
    cases j with
    | inl j => exact continuous_const
    | inr j =>
      change Continuous (fun x => sourceBlock β A (S x) i j)
      exact (continuous_apply j).comp ((continuous_apply i).comp hb)

theorem continuous_source_of_psd {X : Type*} [TopologicalSpace X]
    (A : ι → Matrix n n ℂ) {S : X → Matrix (n ⊕ n) (n ⊕ n) ℂ}
    (hS : Continuous S) (hpos : ∀ x, (S x).PosSemidef)
    {c : X → ι → ℝ} (hc : ∀ i, Continuous (fun x => c x i))
    {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1) :
    Continuous (fun x => source A β (c x) (S x)) := by
  exact continuous_finset_sum _ (fun i _ =>
    (hc i).smul (continuous_sourceTerm_of_psd (A i) hS hpos hβ hβ1))

end HigherRankKS
