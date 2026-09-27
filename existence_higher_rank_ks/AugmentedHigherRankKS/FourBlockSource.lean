import HigherRankKS.SourceSmoothness
import HigherRankKS.Optimizer

/-!
# The concrete four-block independent-reserve source

The outer partial trace is taken before invoking the established two-block
source. Its own partial trace then adds all four physical density blocks.
The resulting source is duplicated once more. This is exactly four copies
of one owner power, not separate powers or signing choices for four copies.
-/

open Matrix MatrixSpencer
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff

noncomputable section
namespace AugmentedHigherRankKS

abbrev FourSpin (n : Type*) := (n ⊕ n) ⊕ (n ⊕ n)

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
local instance fourSourceCStar {j : Type*} [Fintype j] [DecidableEq j] :
    CStarAlgebra (Matrix j j ℂ) := {}

/-- Partial trace of all four physical density blocks. -/
def marginal (S : Matrix (FourSpin n) (FourSpin n) ℂ) : Matrix n n ℂ :=
  HigherRankKS.marginal (HigherRankKS.marginal S)

theorem marginal_posSemidef {S : Matrix (FourSpin n) (FourSpin n) ℂ}
    (hS : S.PosSemidef) : (marginal S).PosSemidef :=
  HigherRankKS.marginal_posSemidef (HigherRankKS.marginal_posSemidef hS)

theorem marginal_posDef {S : Matrix (FourSpin n) (FourSpin n) ℂ}
    (hS : S.PosDef) : (marginal S).PosDef :=
  HigherRankKS.marginal_posDef (HigherRankKS.marginal_posDef hS)

/-- One physical owner block; all four density blocks enter its power. -/
def sourceBlock (β : ℝ) (A : Matrix n n ℂ)
    (S : Matrix (FourSpin n) (FourSpin n) ℂ) : Matrix n n ℂ :=
  HigherRankKS.sourceBlock β A (HigherRankKS.marginal S)

/-- Four equal output copies for one original matrix. -/
def sourceTerm (β : ℝ) (A : Matrix n n ℂ)
    (S : Matrix (FourSpin n) (FourSpin n) ℂ) :
    Matrix (FourSpin n) (FourSpin n) ℂ :=
  HigherRankKS.spinDuplicateCLM (HigherRankKS.sourceTerm β A (HigherRankKS.marginal S))

/-- Scalar reserves are independent of the coefficient positions. -/
def source (A : ι → Matrix n n ℂ) (β : ℝ) (c : ι → ℝ)
    (S : Matrix (FourSpin n) (FourSpin n) ℂ) :
    Matrix (FourSpin n) (FourSpin n) ℂ :=
  ∑ i, c i • sourceTerm β (A i) S

theorem sourceTerm_posSemidef (β : ℝ) (A : Matrix n n ℂ)
    {S : Matrix (FourSpin n) (FourSpin n) ℂ} (hS : S.PosSemidef) :
    (sourceTerm β A S).PosSemidef :=
  posSemidef_fromBlocks_diagonal
    (HigherRankKS.sourceTerm_posSemidef β A (HigherRankKS.marginal_posSemidef hS))
    (HigherRankKS.sourceTerm_posSemidef β A (HigherRankKS.marginal_posSemidef hS))

theorem source_posSemidef (A : ι → Matrix n n ℂ) (β : ℝ)
    {c : ι → ℝ} (hc : ∀ i, 0 ≤ c i)
    {S : Matrix (FourSpin n) (FourSpin n) ℂ} (hS : S.PosSemidef) :
    (source A β c S).PosSemidef := by
  apply Matrix.nonneg_iff_posSemidef.mp
  exact Finset.sum_nonneg (fun i _ =>
    smul_nonneg (hc i) (sourceTerm_posSemidef β (A i) hS).nonneg)

@[simp] theorem source_zero_weights (A : ι → Matrix n n ℂ) (β : ℝ)
    (S : Matrix (FourSpin n) (FourSpin n) ℂ) :
    source A β (fun _ => 0) S = 0 := by simp [source]

theorem source_eq_duplicate (A : ι → Matrix n n ℂ) (β : ℝ) (c : ι → ℝ)
    (S : Matrix (FourSpin n) (FourSpin n) ℂ) :
    source A β c S = HigherRankKS.spinDuplicateCLM
      (HigherRankKS.source A β c (HigherRankKS.marginal S)) := by
  simp only [source, HigherRankKS.source, map_sum, map_smul]
  rfl

theorem continuous_sourceTerm_of_psd {X : Type*} [TopologicalSpace X]
    (A : Matrix n n ℂ) {S : X → Matrix (FourSpin n) (FourSpin n) ℂ}
    (hS : Continuous S) (hpos : ∀ x, (S x).PosSemidef)
    {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1) :
    Continuous (fun x => sourceTerm β A (S x)) :=
  HigherRankKS.spinDuplicateCLM.continuous.comp
    (HigherRankKS.continuous_sourceTerm_of_psd A
      (HigherRankKS.continuous_marginal.comp hS)
      (fun x => HigherRankKS.marginal_posSemidef (hpos x)) hβ hβ1)

theorem continuous_source_of_psd {X : Type*} [TopologicalSpace X]
    (A : ι → Matrix n n ℂ) {S : X → Matrix (FourSpin n) (FourSpin n) ℂ}
    (hS : Continuous S) (hpos : ∀ x, (S x).PosSemidef)
    {c : X → ι → ℝ} (hc : ∀ i, Continuous (fun x => c x i))
    {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1) :
    Continuous (fun x => source A β (c x) (S x)) :=
  continuous_finset_sum _ (fun i _ =>
    (hc i).smul (continuous_sourceTerm_of_psd (A i) hS hpos hβ hβ1))

theorem sourceTerm_weighted_add_le (A : Matrix n n ℂ)
    {β : ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    {S T : Matrix (FourSpin n) (FourSpin n) ℂ}
    (hS : S.PosSemidef) (hT : T.PosSemidef)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a • sourceTerm β A S + b • sourceTerm β A T ≤
      sourceTerm β A (a • S + b • T) := by
  have hd := Matrix.le_iff.mp (HigherRankKS.sourceTerm_weighted_add_le A hβ hβ1
    (HigherRankKS.marginal_posSemidef hS) (HigherRankKS.marginal_posSemidef hT) ha hb)
  have h := posSemidef_fromBlocks_diagonal hd hd
  apply Matrix.le_iff.mpr
  convert h using 1
  ext i j
  cases i <;> cases j <;>
    simp [sourceTerm, HigherRankKS.spinDuplicateCLM,
      HigherRankKS.marginal_weighted_add]

theorem source_weighted_add_le (A : ι → Matrix n n ℂ)
    {β : ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    {c : ι → ℝ} (hc : ∀ i, 0 ≤ c i)
    {S T : Matrix (FourSpin n) (FourSpin n) ℂ}
    (hS : S.PosSemidef) (hT : T.PosSemidef)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a • source A β c S + b • source A β c T ≤
      source A β c (a • S + b • T) := by
  simp only [source, Finset.smul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _hi
  have h := smul_le_smul_of_nonneg_left
    (sourceTerm_weighted_add_le (A i) hβ hβ1 hS hT ha hb) (hc i)
  simpa only [smul_add, smul_comm (c i) a, smul_comm (c i) b] using h

theorem contDiffAt_sourceTerm (A : Matrix n n ℂ) (k : ℕ) (hk : 1 ≤ k)
    (S : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ))
    (hS : (S : Matrix (FourSpin n) (FourSpin n) ℂ).PosDef) :
    ContDiffAt ℝ ∞ (fun X : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ) =>
      sourceTerm ((1 : ℝ) / (2 : ℝ) ^ k) A (X : Matrix _ _ ℂ)) S := by
  have hinner := HigherRankKS.contDiffAt_sourceTerm A k hk
    (HigherRankKS.hermitianMarginalCLM S) (HigherRankKS.marginal_posDef hS)
  exact HigherRankKS.spinDuplicateCLM.contDiff.contDiffAt.comp S
    (hinner.comp S (HigherRankKS.hermitianMarginalCLM (n := n ⊕ n)).contDiff.contDiffAt)

theorem contDiffAt_jointSource (A : ι → Matrix n n ℂ)
    (k : ℕ) (hk : 1 ≤ k) (c : ι → ℝ)
    (S : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ))
    (hS : (S : Matrix (FourSpin n) (FourSpin n) ℂ).PosDef) :
    ContDiffAt ℝ ∞ (fun P : (ι → ℝ) ×
        selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ) =>
      source A ((1 : ℝ) / (2 : ℝ) ^ k) P.1 (P.2 : Matrix _ _ ℂ)) (c, S) := by
  apply ContDiffAt.sum
  intro i hi
  have hc : ContDiffAt ℝ ∞
      (fun P : (ι → ℝ) × selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ) => P.1 i)
      (c, S) :=
    (contDiff_apply ℝ ℝ i).contDiffAt.comp (c, S) (f := Prod.fst) contDiffAt_fst
  have hs := (contDiffAt_sourceTerm (A i) k hk S hS).comp (c, S)
    (f := Prod.snd) contDiffAt_snd
  exact hc.smul hs

end AugmentedHigherRankKS
