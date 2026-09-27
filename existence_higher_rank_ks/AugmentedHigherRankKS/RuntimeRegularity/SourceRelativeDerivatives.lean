import AugmentedHigherRankKS.RuntimeRegularity.RelativeProductDerivatives
import AugmentedHigherRankKS.FourBlockSource

/-! Relative derivatives of the actual supported source owners. Fixed carrier
compression includes singular input matrices without an eigenvalue hypothesis. -/

open Matrix MatrixSpencer HigherRankKS Set Filter
open scoped Topology BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff

noncomputable section
set_option maxHeartbeats 200000
namespace HigherRankKSRuntime.SourceRelativeDerivatives

variable {n : Type*} [Fintype n] [DecidableEq n]
local instance {m : Type*} [Fintype m] [DecidableEq m] : CStarAlgebra (Matrix m m ℂ) := {}

theorem selfAdjoint_add (S X : selfAdjoint (Matrix n n ℂ)) :
    (↑(S + X) : Matrix n n ℂ) = (S : Matrix n n ℂ) + (X : Matrix n n ℂ) := rfl

theorem selfAdjoint_sub (S X : selfAdjoint (Matrix n n ℂ)) :
    (↑(S - X) : Matrix n n ℂ) = (S : Matrix n n ℂ) - (X : Matrix n n ℂ) := rfl

theorem matrixExtension_mono {m : Type*} [Fintype m] [DecidableEq m]
    (V : Matrix n m ℂ) : Monotone (matrixExtensionCLM V) := by
  intro X Y hXY
  apply Matrix.le_iff.mpr
  simpa only [map_sub, matrixExtensionCLM_apply, Matrix.mul_sub, Matrix.sub_mul] using
    (Matrix.le_iff.mp hXY).mul_mul_conjTranspose_same V

theorem spinDuplicate_mono : Monotone (spinDuplicateCLM (n := n)) := by
  intro X Y hXY
  apply Matrix.le_iff.mpr
  have hp := posSemidef_fromBlocks_diagonal (Matrix.le_iff.mp hXY) (Matrix.le_iff.mp hXY)
  change (spinDuplicateCLM Y - spinDuplicateCLM X).PosSemidef
  rw [← map_sub]
  exact hp

def ownerOutput (A : Matrix n n ℂ) : Matrix (AtomCarrierIndex A) (AtomCarrierIndex A) ℂ →L[ℝ]
    Matrix (n ⊕ n) (n ⊕ n) ℂ :=
  spinDuplicateCLM.comp (matrixExtensionCLM (CFC.sqrt A * atomEmbedding A))

theorem ownerOutput_mono (A : Matrix n n ℂ) : Monotone (ownerOutput A) :=
  spinDuplicate_mono.comp (matrixExtension_mono _)

theorem sourceTerm_eq_ownerOutput (A : Matrix n n ℂ) (q : ℕ) (hq : 1 ≤ q)
    {S : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hS : S.PosSemidef) :
    sourceTerm ((1 : ℝ) / (2 : ℝ) ^ q) A S =
      ownerOutput A (carrierPower ((1 : ℝ) / (2 : ℝ) ^ q) (compressedCarrier A S)) := by
  have hs := (CFC.sqrt_nonneg A).posSemidef.isHermitian
  change spinDuplicateCLM (sourceBlock _ A S) = _
  rw [sourceBlock, carrierPower_reconstruct A hS q hq]
  simp only [ownerOutput, ContinuousLinearMap.comp_apply, matrixExtensionCLM_apply,
    Matrix.conjTranspose_mul, hs.eq, Matrix.mul_assoc]

theorem compressedCarrier_relative (A : Matrix n n ℂ)
    {S X : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ)} {b : ℝ}
    (hlo : (-b) • (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) ≤ (X : Matrix (n ⊕ n) (n ⊕ n) ℂ))
    (hhi : (X : Matrix (n ⊕ n) (n ⊕ n) ℂ) ≤ b • (S : Matrix (n ⊕ n) (n ⊕ n) ℂ)) :
    (-b) • (compressedCarrierCLM A S : Matrix (AtomCarrierIndex A) (AtomCarrierIndex A) ℂ) ≤
        (compressedCarrierCLM A X : Matrix (AtomCarrierIndex A) (AtomCarrierIndex A) ℂ) ∧
      (compressedCarrierCLM A X : Matrix (AtomCarrierIndex A) (AtomCarrierIndex A) ℂ) ≤
        b • (compressedCarrierCLM A S : Matrix (AtomCarrierIndex A) (AtomCarrierIndex A) ℂ) := by
  constructor
  · apply Matrix.le_iff.mpr
    have hh := compressedCarrier_posSemidef A (Matrix.le_iff.mp hlo)
    have he : (compressedCarrierCLM A (X - (-b) • S) : Matrix (AtomCarrierIndex A) (AtomCarrierIndex A) ℂ) =
        (compressedCarrierCLM A X : Matrix (AtomCarrierIndex A) (AtomCarrierIndex A) ℂ) -
          (-b) • (compressedCarrierCLM A S : Matrix (AtomCarrierIndex A) (AtomCarrierIndex A) ℂ) := by
      simp only [map_sub, map_smul, selfAdjoint_sub, selfAdjoint.val_smul]
    rw [compressedCarrierCLM_coe] at he
    exact he ▸ hh
  · apply Matrix.le_iff.mpr
    have hh := compressedCarrier_posSemidef A (Matrix.le_iff.mp hhi)
    have he : (compressedCarrierCLM A (b • S - X) : Matrix (AtomCarrierIndex A) (AtomCarrierIndex A) ℂ) =
        b • (compressedCarrierCLM A S : Matrix (AtomCarrierIndex A) (AtomCarrierIndex A) ℂ) -
          (compressedCarrierCLM A X : Matrix (AtomCarrierIndex A) (AtomCarrierIndex A) ℂ) := by
      simp only [map_sub, map_smul, selfAdjoint_sub, selfAdjoint.val_smul]
    rw [compressedCarrierCLM_coe] at he
    exact he ▸ hh

attribute [local irreducible] HigherRankKS.compressedCarrierCLM HigherRankKS.atomEmbedding ownerOutput

theorem weighted_sourceTerm_derivative_relative (A : Matrix n n ℂ)
    (q : ℕ) (hq : 1 ≤ q)
    {S X : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ)}
    (hS : (S : Matrix (n ⊕ n) (n ⊕ n) ℂ).PosDef) {b : ℝ} (hb : 0 ≤ b)
    (hlo : (-b) • (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) ≤ (X : Matrix (n ⊕ n) (n ⊕ n) ℂ))
    (hhi : (X : Matrix (n ⊕ n) (n ⊕ n) ℂ) ≤ b • (S : Matrix (n ⊕ n) (n ⊕ n) ℂ))
    {f : ℝ → ℝ} {k : ℕ} {c d : ℝ} (hf : ContDiffAt ℝ k f 0)
    (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hfbound : ∀ i ≤ k, ‖iteratedDeriv i f 0‖ ≤ (i.factorial : ℝ) * d ^ i * c) :
    -((k.factorial : ℝ) * (d + 2 * b) ^ k) •
        (c • sourceTerm ((1 : ℝ) / (2 : ℝ) ^ q) A (S : Matrix (n ⊕ n) (n ⊕ n) ℂ)) ≤
      iteratedDeriv k (fun t : ℝ => f t • sourceTerm ((1 : ℝ) / (2 : ℝ) ^ q) A
        ((S : Matrix (n ⊕ n) (n ⊕ n) ℂ) + t • (X : Matrix (n ⊕ n) (n ⊕ n) ℂ))) 0 ∧
    iteratedDeriv k (fun t : ℝ => f t • sourceTerm ((1 : ℝ) / (2 : ℝ) ^ q) A
        ((S : Matrix (n ⊕ n) (n ⊕ n) ℂ) + t • (X : Matrix (n ⊕ n) (n ⊕ n) ℂ))) 0 ≤
      ((k.factorial : ℝ) * (d + 2 * b) ^ k) •
        (c • sourceTerm ((1 : ℝ) / (2 : ℝ) ^ q) A (S : Matrix (n ⊕ n) (n ⊕ n) ℂ)) := by
  let β : ℝ := 1 / (2 : ℝ) ^ q
  let M := (compressedCarrierCLM A S : Matrix (AtomCarrierIndex A) (AtomCarrierIndex A) ℂ)
  let U := (compressedCarrierCLM A X : Matrix (AtomCarrierIndex A) (AtomCarrierIndex A) ℂ)
  have hM : M.PosDef := by
    simpa only [M, compressedCarrierCLM_coe] using compressedCarrier_posDef A hS
  have hU : U.IsHermitian := (compressedCarrierCLM A X).property
  have hβ : β ∈ Ioo 0 1 := by
    constructor
    · dsimp [β]; positivity
    · dsimp [β]; apply (div_lt_one (by positivity)).mpr
      exact one_lt_pow₀ (by norm_num) (Nat.ne_of_gt hq)
  have hrel := compressedCarrier_relative A hlo hhi
  have hsm : ContDiffAt ℝ k (fun t : ℝ => carrierPower β (M + t • U)) 0 := by
    have hz := contDiffAt_carrierPower_dyadic q (compressedCarrierCLM A S) hM
    have hl : ContDiffAt ℝ ∞ (fun t : ℝ => compressedCarrierCLM A S +
        t • compressedCarrierCLM A X) 0 := by fun_prop
    have hz' : ContDiffAt ℝ ∞ (fun Y : selfAdjoint
        (Matrix (AtomCarrierIndex A) (AtomCarrierIndex A) ℂ) => carrierPower β
          (Y : Matrix (AtomCarrierIndex A) (AtomCarrierIndex A) ℂ))
        (compressedCarrierCLM A S + (0 : ℝ) • compressedCarrierCLM A X) := by
      simpa only [zero_smul, add_zero] using hz
    have hh := hz'.comp 0 hl
    simpa only [selfAdjoint_add, selfAdjoint.val_smul, M, U] using
      hh.of_le (show (k : WithTop ℕ∞) ≤ ∞ by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))
  have he : (fun t : ℝ => f t • sourceTerm β A
      ((S : Matrix (n ⊕ n) (n ⊕ n) ℂ) + t • (X : Matrix (n ⊕ n) (n ⊕ n) ℂ))) =ᶠ[𝓝 0]
      (fun t : ℝ => ownerOutput A (f t • carrierPower β (M + t • U))) := by
    filter_upwards [KSMovingOwnerHessian.eventually_posDef_transportLine hS
      (show (X : Matrix (n ⊕ n) (n ⊕ n) ℂ).IsHermitian from X.property)] with t ht
    have hr := sourceTerm_eq_ownerOutput A q hq (show
      ((S : Matrix (n ⊕ n) (n ⊕ n) ℂ) + t • (X : Matrix (n ⊕ n) (n ⊕ n) ℂ)).PosSemidef
        from ht.posSemidef)
    change sourceTerm β A _ = _ at hr
    rw [hr, map_smul]
    have hec : compressedCarrier A ((S : Matrix (n ⊕ n) (n ⊕ n) ℂ) + t • (X : Matrix (n ⊕ n) (n ⊕ n) ℂ)) =
        M + t • U := by
      have hh := compressedCarrierCLM_coe A (S + t • X)
      simpa only [map_add, map_smul, selfAdjoint_add, selfAdjoint.val_smul, M, U] using hh.symm
    rw [hec]
  have hde := he.iteratedDeriv_eq k
  rw [WeightedCompactIntegral.iteratedDeriv_clm _ (hf.smul hsm)] at hde
  have hbound : -((k.factorial : ℝ) * (d + 2 * b) ^ k) • (c • carrierPower β M) ≤
      iteratedDeriv k (fun t : ℝ => f t • carrierPower β (M + t • U)) 0 ∧
      iteratedDeriv k (fun t : ℝ => f t • carrierPower β (M + t • U)) 0 ≤
        ((k.factorial : ℝ) * (d + 2 * b) ^ k) • (c • carrierPower β M) := by
    rcases isEmpty_or_nonempty (AtomCarrierIndex A) with he | hn
    · letI := he
      exact ⟨le_of_eq (Subsingleton.elim _ _), le_of_eq (Subsingleton.elim _ _)⟩
    · letI := hn
      exact RelativeProductDerivatives.weighted_carrier_derivative_relative hβ hM hU hb
        hrel.1 hrel.2 hf hc hd hfbound
  have hl := ownerOutput_mono A hbound.1
  have hu := ownerOutput_mono A hbound.2
  simp only [map_smul] at hl hu
  change _ ≤ iteratedDeriv k (fun t : ℝ => f t • sourceTerm β A
    ((S : Matrix (n ⊕ n) (n ⊕ n) ℂ) + t • (X : Matrix (n ⊕ n) (n ⊕ n) ℂ))) 0 ∧ _ ≤ _
  rw [hde, sourceTerm_eq_ownerOutput A q hq hS.posSemidef]
  simpa only [M, compressedCarrierCLM_coe, β] using And.intro hl hu

theorem marginal_relative
    {S X : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ)} {b : ℝ}
    (hlo : (-b) • (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) ≤ (X : Matrix (n ⊕ n) (n ⊕ n) ℂ))
    (hhi : (X : Matrix (n ⊕ n) (n ⊕ n) ℂ) ≤ b • (S : Matrix (n ⊕ n) (n ⊕ n) ℂ)) :
    (-b) • (hermitianMarginalCLM S : Matrix n n ℂ) ≤ (hermitianMarginalCLM X : Matrix n n ℂ) ∧
      (hermitianMarginalCLM X : Matrix n n ℂ) ≤ b • (hermitianMarginalCLM S : Matrix n n ℂ) := by
  constructor
  · apply Matrix.le_iff.mpr
    have hp := HigherRankKS.marginal_posSemidef (Matrix.le_iff.mp hlo)
    have he := hermitianMarginalCLM_coe (X - (-b) • S)
    simp only [map_sub, map_smul, selfAdjoint_sub, selfAdjoint.val_smul] at he
    rw [← he] at hp
    exact hp
  · apply Matrix.le_iff.mpr
    have hp := HigherRankKS.marginal_posSemidef (Matrix.le_iff.mp hhi)
    have he := hermitianMarginalCLM_coe (b • S - X)
    simp only [map_sub, map_smul, selfAdjoint_sub, selfAdjoint.val_smul] at he
    rw [← he] at hp
    exact hp

theorem sourceTerm_line_smooth (A : Matrix n n ℂ) (q : ℕ) (hq : 1 ≤ q)
    (S X : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ))
    (hS : (S : Matrix (n ⊕ n) (n ⊕ n) ℂ).PosDef) (k : ℕ) :
    ContDiffAt ℝ k (fun t : ℝ => sourceTerm ((1 : ℝ) / (2 : ℝ) ^ q) A
      ((S : Matrix (n ⊕ n) (n ⊕ n) ℂ) + t • (X : Matrix (n ⊕ n) (n ⊕ n) ℂ))) 0 := by
  have hf := HigherRankKS.contDiffAt_sourceTerm A q hq S hS
  have hf' : ContDiffAt ℝ ∞ (fun Y : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ) =>
      sourceTerm ((1 : ℝ) / (2 : ℝ) ^ q) A (Y : Matrix (n ⊕ n) (n ⊕ n) ℂ))
      (S + (0 : ℝ) • X) := by simpa only [zero_smul, add_zero] using hf
  have hh := hf'.comp 0 (show ContDiffAt ℝ ∞ (fun t : ℝ => S + t • X) 0 by fun_prop)
  simpa only [selfAdjoint_add, selfAdjoint.val_smul] using
    hh.of_le (show (k : WithTop ℕ∞) ≤ ∞ by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))

theorem weighted_four_sourceTerm_derivative_relative (A : Matrix n n ℂ)
    (q : ℕ) (hq : 1 ≤ q)
    {S X : selfAdjoint (Matrix (AugmentedHigherRankKS.FourSpin n) (AugmentedHigherRankKS.FourSpin n) ℂ)}
    (hS : (S : Matrix (AugmentedHigherRankKS.FourSpin n) (AugmentedHigherRankKS.FourSpin n) ℂ).PosDef)
    {b : ℝ} (hb : 0 ≤ b)
    (hlo : (-b) • (S : Matrix (AugmentedHigherRankKS.FourSpin n) (AugmentedHigherRankKS.FourSpin n) ℂ) ≤
      (X : Matrix (AugmentedHigherRankKS.FourSpin n) (AugmentedHigherRankKS.FourSpin n) ℂ))
    (hhi : (X : Matrix (AugmentedHigherRankKS.FourSpin n) (AugmentedHigherRankKS.FourSpin n) ℂ) ≤
      b • (S : Matrix (AugmentedHigherRankKS.FourSpin n) (AugmentedHigherRankKS.FourSpin n) ℂ))
    {f : ℝ → ℝ} {k : ℕ} {c d : ℝ} (hf : ContDiffAt ℝ k f 0)
    (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hfbound : ∀ i ≤ k, ‖iteratedDeriv i f 0‖ ≤ (i.factorial : ℝ) * d ^ i * c) :
    -((k.factorial : ℝ) * (d + 2 * b) ^ k) •
        (c • AugmentedHigherRankKS.sourceTerm ((1 : ℝ) / (2 : ℝ) ^ q) A (S : Matrix _ _ ℂ)) ≤
      iteratedDeriv k (fun t : ℝ => f t • AugmentedHigherRankKS.sourceTerm ((1 : ℝ) / (2 : ℝ) ^ q) A
        ((S : Matrix _ _ ℂ) + t • (X : Matrix _ _ ℂ))) 0 ∧
    iteratedDeriv k (fun t : ℝ => f t • AugmentedHigherRankKS.sourceTerm ((1 : ℝ) / (2 : ℝ) ^ q) A
        ((S : Matrix _ _ ℂ) + t • (X : Matrix _ _ ℂ))) 0 ≤
      ((k.factorial : ℝ) * (d + 2 * b) ^ k) •
        (c • AugmentedHigherRankKS.sourceTerm ((1 : ℝ) / (2 : ℝ) ^ q) A (S : Matrix _ _ ℂ)) := by
  let S₂ := hermitianMarginalCLM S
  let X₂ := hermitianMarginalCLM X
  have hS₂ : (S₂ : Matrix (n ⊕ n) (n ⊕ n) ℂ).PosDef := HigherRankKS.marginal_posDef hS
  obtain ⟨hl₂, hu₂⟩ := marginal_relative hlo hhi
  have hh := weighted_sourceTerm_derivative_relative A q hq hS₂ hb hl₂ hu₂ hf hc hd hfbound
  let g := fun t : ℝ => f t • sourceTerm ((1 : ℝ) / (2 : ℝ) ^ q) A
    ((S₂ : Matrix (n ⊕ n) (n ⊕ n) ℂ) + t • (X₂ : Matrix (n ⊕ n) (n ⊕ n) ℂ))
  have hg : ContDiffAt ℝ k g 0 := hf.smul (sourceTerm_line_smooth A q hq S₂ X₂ hS₂ k)
  have he : (fun t : ℝ => f t • AugmentedHigherRankKS.sourceTerm ((1 : ℝ) / (2 : ℝ) ^ q) A
      ((S : Matrix _ _ ℂ) + t • (X : Matrix _ _ ℂ))) =
      (fun t => spinDuplicateCLM (g t)) := by
    funext t
    have hm := hermitianMarginalCLM_coe (S + t • X)
    simp only [map_add, map_smul, selfAdjoint_add, selfAdjoint.val_smul] at hm
    simp only [AugmentedHigherRankKS.sourceTerm, g, map_smul]
    rw [← hm]
  rw [he, WeightedCompactIntegral.iteratedDeriv_clm _ hg]
  have hl := spinDuplicate_mono hh.1
  have hu := spinDuplicate_mono hh.2
  simpa only [map_smul, AugmentedHigherRankKS.sourceTerm, S₂,
    hermitianMarginalCLM_coe] using And.intro hl hu

theorem iteratedDeriv_sum {ι F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (s : Finset ι) (f : ι → ℝ → F) (k : ℕ) (x : ℝ)
    (hf : ∀ i ∈ s, ContDiffAt ℝ k (f i) x) :
    iteratedDeriv k (fun t => ∑ i ∈ s, f i t) x = ∑ i ∈ s, iteratedDeriv k (f i) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [iteratedDeriv_succ']
      simpa using ih
  | @insert a s ha ih =>
    have hfa := hf a (Finset.mem_insert_self _ _)
    have hfs := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hsum : ContDiffAt ℝ k (fun t => ∑ i ∈ s, f i t) x := ContDiffAt.sum hfs
    simp only [Finset.sum_insert ha]
    rw [show (fun t => f a t + ∑ i ∈ s, f i t) = f a + (fun t => ∑ i ∈ s, f i t) from rfl,
      iteratedDeriv_add hfa hsum, ih hfs]

theorem four_source_derivative_relative {ι : Type*} [Fintype ι]
    (A : ι → Matrix n n ℂ) (q : ℕ) (hq : 1 ≤ q)
    {S X : selfAdjoint (Matrix (AugmentedHigherRankKS.FourSpin n) (AugmentedHigherRankKS.FourSpin n) ℂ)}
    (hS : (S : Matrix (AugmentedHigherRankKS.FourSpin n) (AugmentedHigherRankKS.FourSpin n) ℂ).PosDef)
    {b : ℝ} (hb : 0 ≤ b)
    (hlo : (-b) • (S : Matrix (AugmentedHigherRankKS.FourSpin n) (AugmentedHigherRankKS.FourSpin n) ℂ) ≤
      (X : Matrix (AugmentedHigherRankKS.FourSpin n) (AugmentedHigherRankKS.FourSpin n) ℂ))
    (hhi : (X : Matrix (AugmentedHigherRankKS.FourSpin n) (AugmentedHigherRankKS.FourSpin n) ℂ) ≤
      b • (S : Matrix (AugmentedHigherRankKS.FourSpin n) (AugmentedHigherRankKS.FourSpin n) ℂ))
    {f : ι → ℝ → ℝ} {k : ℕ} {c : ι → ℝ} {d : ℝ}
    (hf : ∀ i, ContDiffAt ℝ k (f i) 0) (hc : ∀ i, 0 ≤ c i) (hd : 0 ≤ d)
    (hfbound : ∀ i j, j ≤ k → ‖iteratedDeriv j (f i) 0‖ ≤ (j.factorial : ℝ) * d ^ j * c i) :
    -((k.factorial : ℝ) * (d + 2 * b) ^ k) •
        AugmentedHigherRankKS.source A ((1 : ℝ) / (2 : ℝ) ^ q) c (S : Matrix _ _ ℂ) ≤
      iteratedDeriv k (fun t : ℝ => AugmentedHigherRankKS.source A ((1 : ℝ) / (2 : ℝ) ^ q)
        (fun i => f i t) ((S : Matrix _ _ ℂ) + t • (X : Matrix _ _ ℂ))) 0 ∧
    iteratedDeriv k (fun t : ℝ => AugmentedHigherRankKS.source A ((1 : ℝ) / (2 : ℝ) ^ q)
        (fun i => f i t) ((S : Matrix _ _ ℂ) + t • (X : Matrix _ _ ℂ))) 0 ≤
      ((k.factorial : ℝ) * (d + 2 * b) ^ k) •
        AugmentedHigherRankKS.source A ((1 : ℝ) / (2 : ℝ) ^ q) c (S : Matrix _ _ ℂ) := by
  have hsm : ∀ i, ContDiffAt ℝ k (fun t : ℝ => f i t •
      AugmentedHigherRankKS.sourceTerm ((1 : ℝ) / (2 : ℝ) ^ q) (A i)
      ((S : Matrix _ _ ℂ) + t • (X : Matrix _ _ ℂ))) 0 := by
    intro i
    have ht := AugmentedHigherRankKS.contDiffAt_sourceTerm (A i) q hq S hS
    have ht' : ContDiffAt ℝ ∞ (fun Y : selfAdjoint
        (Matrix (AugmentedHigherRankKS.FourSpin n) (AugmentedHigherRankKS.FourSpin n) ℂ) =>
        AugmentedHigherRankKS.sourceTerm ((1 : ℝ) / (2 : ℝ) ^ q) (A i) (Y : Matrix _ _ ℂ))
        (S + (0 : ℝ) • X) := by simpa only [zero_smul, add_zero] using ht
    have hh := ht'.comp 0 (show ContDiffAt ℝ ∞ (fun t : ℝ => S + t • X) 0 by fun_prop)
    apply (hf i).smul
    simpa only [selfAdjoint_add, selfAdjoint.val_smul] using
      hh.of_le (show (k : WithTop ℕ∞) ≤ ∞ by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))
  simp only [AugmentedHigherRankKS.source]
  rw [iteratedDeriv_sum Finset.univ _ k 0 (fun i _ => hsm i)]
  simp only [Finset.smul_sum]
  constructor
  · exact Finset.sum_le_sum (fun i _ => (weighted_four_sourceTerm_derivative_relative
      (A i) q hq hS hb hlo hhi (hf i) (hc i) hd (hfbound i)).1)
  · exact Finset.sum_le_sum (fun i _ => (weighted_four_sourceTerm_derivative_relative
      (A i) q hq hS hb hlo hhi (hf i) (hc i) hd (hfbound i)).2)

end HigherRankKSRuntime.SourceRelativeDerivatives
