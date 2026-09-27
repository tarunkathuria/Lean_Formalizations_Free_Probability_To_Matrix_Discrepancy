import HigherRankKS.SourceCompression
import HigherRankKS.SourceProfile

/-! Smoothness of the actual nonlinear source at faithful densities. Singular
atoms are handled through their constructed fixed carrier, not by assuming
that the ambient carrier matrix is positive definite. -/

noncomputable section
open Matrix MatrixSpencer Filter Topology
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff

namespace HigherRankKS

variable {n : Type*} [Fintype n] [DecidableEq n]
local instance sourceSmoothnessCStar {k : Type*} [Fintype k] [DecidableEq k] :
    CStarAlgebra (Matrix k k ℂ) := {}

def hermitianMarginalCLM : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ) →L[ℝ]
    selfAdjoint (Matrix n n ℂ) := by
  letI : FiniteDimensional ℝ (selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ)) :=
    inferInstanceAs (FiniteDimensional ℝ (selfAdjoint.submodule ℝ (Matrix (n ⊕ n) (n ⊕ n) ℂ)))
  exact LinearMap.toContinuousLinearMap
    { toFun := fun X => ⟨marginal (X : Matrix (n ⊕ n) (n ⊕ n) ℂ),
        ((show (X : Matrix (n ⊕ n) (n ⊕ n) ℂ).IsHermitian from X.property).submatrix Sum.inl).add
          ((show (X : Matrix (n ⊕ n) (n ⊕ n) ℂ).IsHermitian from X.property).submatrix Sum.inr)⟩
      map_add' := by
        intro X Y
        apply Subtype.ext
        ext i j
        simp [marginal, Matrix.toBlocks₁₁, Matrix.toBlocks₂₂]
        ring
      map_smul' := by
        intro a X
        apply Subtype.ext
        ext i j
        simp [marginal, Matrix.toBlocks₁₁, Matrix.toBlocks₂₂, smul_add] }

@[simp] theorem hermitianMarginalCLM_coe (S : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ)) :
    (hermitianMarginalCLM S : Matrix n n ℂ) = marginal (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) := rfl

def compressedCarrierCLM (A : Matrix n n ℂ) :
    selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ) →L[ℝ]
      selfAdjoint (Matrix (AtomCarrierIndex A) (AtomCarrierIndex A) ℂ) :=
  (krausReducedSourceCLM (atomKraus A)).comp hermitianMarginalCLM

@[simp] theorem compressedCarrierCLM_coe (A : Matrix n n ℂ)
    (S : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ)) :
    (compressedCarrierCLM A S : Matrix _ _ ℂ) =
      compressedCarrier A (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) := by
  simp only [compressedCarrierCLM, ContinuousLinearMap.comp_apply,
    krausReducedSourceCLM_coe, hermitianMarginalCLM_coe]
  rfl

def matrixExtensionCLM {m : Type*} [Fintype m] [DecidableEq m] (V : Matrix n m ℂ) :
    Matrix m m ℂ →L[ℝ] Matrix n n ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => V * M * Vᴴ
      map_add' := by intro M N; simp only [Matrix.mul_add, Matrix.add_mul]
      map_smul' := by intro a M; simp only [Matrix.mul_smul, Matrix.smul_mul]; rfl }

omit [Fintype n] [DecidableEq n] in
@[simp] theorem matrixExtensionCLM_apply {m : Type*} [Fintype m] [DecidableEq m]
    (V : Matrix n m ℂ) (M : Matrix m m ℂ) : matrixExtensionCLM V M = V * M * Vᴴ := rfl

theorem contDiffAt_carrierPower_carrier (A : Matrix n n ℂ) (k : ℕ) (hk : 1 ≤ k)
    (S : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ))
    (hS : (S : Matrix (n ⊕ n) (n ⊕ n) ℂ).PosDef) :
    ContDiffAt ℝ ∞ (fun X : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ) =>
      carrierPower ((1 : ℝ) / (2 : ℝ) ^ k) (carrier A (X : Matrix _ _ ℂ))) S := by
  have hcompressed : (compressedCarrierCLM A S :
      Matrix (AtomCarrierIndex A) (AtomCarrierIndex A) ℂ).PosDef := by
    rw [compressedCarrierCLM_coe]
    exact compressedCarrier_posDef A hS
  have hp := (contDiffAt_carrierPower_dyadic k (compressedCarrierCLM A S) hcompressed).comp S
    (compressedCarrierCLM A).contDiff.contDiffAt
  have hfun : ContDiffAt ℝ ∞ (fun X : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ) =>
      atomEmbedding A * carrierPower ((1 : ℝ) / (2 : ℝ) ^ k)
        (compressedCarrier A (X : Matrix _ _ ℂ)) * (atomEmbedding A)ᴴ) S := by
    simpa only [Function.comp_def, matrixExtensionCLM_apply, compressedCarrierCLM_coe] using
      (matrixExtensionCLM (atomEmbedding A)).contDiff.contDiffAt.comp S hp
  apply hfun.congr_of_eventuallyEq
  filter_upwards [eventually_nonneg_of_posDef S hS] with X hX
  exact carrierPower_reconstruct A hX.posSemidef k hk

theorem contDiffAt_sourceBlock (A : Matrix n n ℂ) (k : ℕ) (hk : 1 ≤ k)
    (S : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ))
    (hS : (S : Matrix (n ⊕ n) (n ⊕ n) ℂ).PosDef) :
    ContDiffAt ℝ ∞ (fun X : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ) =>
      sourceBlock ((1 : ℝ) / (2 : ℝ) ^ k) A (X : Matrix _ _ ℂ)) S :=
  (contDiffAt_const.mul (contDiffAt_carrierPower_carrier A k hk S hS)).mul contDiffAt_const

def spinDuplicateCLM : Matrix n n ℂ →L[ℝ] Matrix (n ⊕ n) (n ⊕ n) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => Matrix.fromBlocks M 0 0 M
      map_add' := by
        intro M N
        ext i j
        cases i <;> cases j <;> simp [Matrix.fromBlocks]
      map_smul' := by
        intro a M
        ext i j
        cases i <;> cases j <;> simp [Matrix.fromBlocks] }

theorem contDiffAt_sourceTerm (A : Matrix n n ℂ) (k : ℕ) (hk : 1 ≤ k)
    (S : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ))
    (hS : (S : Matrix (n ⊕ n) (n ⊕ n) ℂ).PosDef) :
    ContDiffAt ℝ ∞ (fun X : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ) =>
      sourceTerm ((1 : ℝ) / (2 : ℝ) ^ k) A (X : Matrix _ _ ℂ)) S :=
  (spinDuplicateCLM (n := n)).contDiff.contDiffAt.comp S (contDiffAt_sourceBlock A k hk S hS)

variable {ι : Type*} [Fintype ι]

theorem contDiffAt_source (A : ι → Matrix n n ℂ) (c : ι → ℝ)
    (k : ℕ) (hk : 1 ≤ k) (S : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ))
    (hS : (S : Matrix (n ⊕ n) (n ⊕ n) ℂ).PosDef) :
    ContDiffAt ℝ ∞ (fun X : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ) =>
      source A ((1 : ℝ) / (2 : ℝ) ^ k) c (X : Matrix _ _ ℂ)) S := by
  exact ContDiffAt.sum (fun i _ =>
    contDiffAt_const.smul (contDiffAt_sourceTerm (A i) k hk S hS))

/-- Joint smoothness in arbitrary real source coefficients and faithful full density. -/
theorem contDiffAt_jointSource (A : ι → Matrix n n ℂ)
    (k : ℕ) (hk : 1 ≤ k) (c : ι → ℝ)
    (S : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ))
    (hS : (S : Matrix (n ⊕ n) (n ⊕ n) ℂ).PosDef) :
    ContDiffAt ℝ ∞ (fun P : (ι → ℝ) × selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ) =>
      source A ((1 : ℝ) / (2 : ℝ) ^ k) P.1 (P.2 : Matrix _ _ ℂ)) (c, S) := by
  apply ContDiffAt.sum
  intro i hi
  have hc : ContDiffAt ℝ ∞
      (fun P : (ι → ℝ) × selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ) => P.1 i) (c, S) :=
    (contDiff_apply ℝ ℝ i).contDiffAt.comp (c, S) (f := Prod.fst) contDiffAt_fst
  have hs : ContDiffAt ℝ ∞
      (fun P : (ι → ℝ) × selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ) =>
        sourceTerm ((1 : ℝ) / (2 : ℝ) ^ k) (A i) (P.2 : Matrix _ _ ℂ)) (c, S) :=
    (contDiffAt_sourceTerm (A i) k hk S hS).comp (c, S) (f := Prod.snd) contDiffAt_snd
  exact hc.smul hs

theorem contDiffAt_source_of_dyadic (A : ι → Matrix n n ℂ) (c : ι → ℝ)
    {q : ℕ} (hq : ∃ k : ℕ, q = 2 ^ k) (hq2 : 2 ≤ q)
    (S : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ))
    (hS : (S : Matrix (n ⊕ n) (n ⊕ n) ℂ).PosDef) :
    ContDiffAt ℝ ∞ (fun X : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ) =>
      source A ((1 : ℝ) / q) c (X : Matrix _ _ ℂ)) S := by
  obtain ⟨k, rfl⟩ := hq
  have hk : 1 ≤ k := by cases k <;> simp_all
  simpa using contDiffAt_source A c k hk S hS

def jointReducedSourcePair (A : ι → Matrix n n ℂ) (β : ℝ)
    (P : (ι → ℝ) × selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ)) :
    selfAdjoint (Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ) ×
      selfAdjoint (Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ) :=
  (hermitianRectangularCompressionCLM (sourceEmbedding A) P.2,
    hermitianProjection (compressedSource A β P.1 (P.2 : Matrix _ _ ℂ)))

theorem jointReducedSourcePair_snd_coe (A : ι → Matrix n n ℂ) (β : ℝ)
    (P : (ι → ℝ) × selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ))
    (hc : ∀ i, 0 ≤ P.1 i) (hS : (P.2 : Matrix (n ⊕ n) (n ⊕ n) ℂ).PosSemidef) :
    ((jointReducedSourcePair A β P).2 : Matrix _ _ ℂ) =
      compressedSource A β P.1 (P.2 : Matrix _ _ ℂ) := by
  apply IsSelfAdjoint.coe_selfAdjointPart_apply
  exact ((source_posSemidef A β hc hS).conjTranspose_mul_mul_same (sourceEmbedding A)).isHermitian

theorem contDiffAt_jointReducedSourcePair (A : ι → Matrix n n ℂ)
    (k : ℕ) (hk : 1 ≤ k) (c : ι → ℝ)
    (S : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ))
    (hS : (S : Matrix (n ⊕ n) (n ⊕ n) ℂ).PosDef) :
    ContDiffAt ℝ ∞ (jointReducedSourcePair A ((1 : ℝ) / (2 : ℝ) ^ k)) (c, S) := by
  have hs := contDiffAt_jointSource A k hk c S hS
  have hc : ContDiffAt ℝ ∞
      (fun P : (ι → ℝ) × selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ) =>
        compressedSource A ((1 : ℝ) / (2 : ℝ) ^ k) P.1 (P.2 : Matrix _ _ ℂ)) (c, S) := by
    simpa only [Function.comp_def, matrixExtensionCLM_apply, Matrix.conjTranspose_conjTranspose,
      compressedSource] using
        (matrixExtensionCLM (sourceEmbedding A)ᴴ).contDiff.contDiffAt.comp (c, S) hs
  exact ((hermitianRectangularCompressionCLM (sourceEmbedding A)).contDiff.contDiffAt.comp
    (c, S) (f := Prod.snd) contDiffAt_snd).prodMk
      ((hermitianProjection (n := SourceCarrierIndex A)).contDiff.contDiffAt.comp (c, S) hc)

def jointSourceFidelity (A : ι → Matrix n n ℂ) (β : ℝ)
    (P : (ι → ℝ) × selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ)) : ℝ :=
  2 * fidelity (P.2 : Matrix _ _ ℂ) (source A β P.1 (P.2 : Matrix _ _ ℂ))

def reducedSourceFidelity (A : ι → Matrix n n ℂ) (β : ℝ)
    (P : (ι → ℝ) × selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ)) : ℝ :=
  doubleFidelity (jointReducedSourcePair A β P)

theorem jointSourceFidelity_eq_reduced (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (k : ℕ) (hk : 1 ≤ k)
    (P : (ι → ℝ) × selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ))
    (hc : ∀ i, 0 < P.1 i) (hS : (P.2 : Matrix (n ⊕ n) (n ⊕ n) ℂ).PosDef) :
    jointSourceFidelity A ((1 : ℝ) / (2 : ℝ) ^ k) P =
      reducedSourceFidelity A ((1 : ℝ) / (2 : ℝ) ^ k) P := by
  have he := jointReducedSourcePair_snd_coe A ((1 : ℝ) / (2 : ℝ) ^ k) P
    (fun i => (hc i).le) hS.posSemidef
  have hf1 : ((jointReducedSourcePair A ((1 : ℝ) / (2 : ℝ) ^ k) P).1 :
      Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ) =
      (sourceEmbedding A)ᴴ * (P.2 : Matrix _ _ ℂ) * sourceEmbedding A :=
    hermitianRectangularCompressionCLM_coe (sourceEmbedding A) P.2
  have hred : reducedSourceFidelity A ((1 : ℝ) / (2 : ℝ) ^ k) P =
      2 * fidelity ((sourceEmbedding A)ᴴ * (P.2 : Matrix _ _ ℂ) * sourceEmbedding A)
        (compressedSource A ((1 : ℝ) / (2 : ℝ) ^ k) P.1 (P.2 : Matrix _ _ ℂ)) := by
    unfold reducedSourceFidelity doubleFidelity
    exact congrArg (fun t : ℝ => 2 * t) (congrArg₂ (fidelity (n := SourceCarrierIndex A)) hf1 he)
  exact (congrArg (fun t : ℝ => 2 * t)
    (fidelity_source_compression A hA hc hS k hk)).trans hred.symm

theorem contDiffAt_reducedSourceFidelity (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (k : ℕ) (hk : 1 ≤ k) (c : ι → ℝ) (hc : ∀ i, 0 < c i)
    (S : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ))
    (hS : (S : Matrix (n ⊕ n) (n ⊕ n) ℂ).PosDef) :
    ContDiffAt ℝ ∞ (reducedSourceFidelity A ((1 : ℝ) / (2 : ℝ) ^ k)) (c, S) := by
  have hr1 : ((jointReducedSourcePair A ((1 : ℝ) / (2 : ℝ) ^ k) (c, S)).1 :
      Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ).PosDef :=
    posDef_isometry_compression (sourceEmbedding A) (krausSupportEmbedding_isometry _) hS
  have hr2 : ((jointReducedSourcePair A ((1 : ℝ) / (2 : ℝ) ^ k) (c, S)).2 :
      Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ).PosDef
      := by
    exact (jointReducedSourcePair_snd_coe A _ (c, S)
      (fun i => (hc i).le) hS.posSemidef).symm ▸ compressedSource_posDef A hA hc hS k hk
  exact (contDiffAt_doubleFidelity _ _ hr1 hr2).comp (c, S)
    (contDiffAt_jointReducedSourcePair A k hk c S hS)

/-- Actual supported fidelity is jointly smooth in positive live coefficients and faithful
full density. The density is not assumed to have the support of the source. -/
theorem contDiffAt_jointSourceFidelity (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (k : ℕ) (hk : 1 ≤ k) (c : ι → ℝ) (hc : ∀ i, 0 < c i)
    (S : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ))
    (hS : (S : Matrix (n ⊕ n) (n ⊕ n) ℂ).PosDef) :
    ContDiffAt ℝ ∞
      (fun P : (ι → ℝ) × selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ) =>
        2 * fidelity (P.2 : Matrix _ _ ℂ)
          (source A ((1 : ℝ) / (2 : ℝ) ^ k) P.1 (P.2 : Matrix _ _ ℂ))) (c, S) := by
  apply (contDiffAt_reducedSourceFidelity A hA k hk c hc S hS).congr_of_eventuallyEq
  have hnear : ∀ᶠ P : (ι → ℝ) × selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ) in 𝓝 (c, S),
      ∀ i, 0 < P.1 i := by
    apply Filter.eventually_all.mpr
    intro i
    exact (((continuous_apply i).comp continuous_fst).continuousAt (x := (c, S))).eventually
      (IsOpen.mem_nhds isOpen_Ioi (hc i))
  filter_upwards [hnear, (continuous_snd.continuousAt (x := (c, S))).eventually
    (eventually_posDef_of_posDef S hS)] with P hPc hPS
  exact jointSourceFidelity_eq_reduced A hA k hk P hPc hPS

section Face

variable [DecidableEq ι]

/-- Insert the live coordinates into a full face state while preserving frozen entries. -/
def faceState (L : Finset ι) (frozen : ι → ℝ) (x : {i // i ∈ L} → ℝ) : ι → ℝ :=
  fun i => if hi : i ∈ L then x ⟨i, hi⟩ else frozen i

theorem source_face_eq_live (A : ι → Matrix n n ℂ) {β : ℝ} (hβ : 0 < β)
    (L : Finset ι) (frozen : ι → ℝ)
    (hfrozen : ∀ i, i ∉ L → frozen i = -1 ∨ frozen i = 1)
    (x : {i // i ∈ L} → ℝ) (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) :
    source A β (fun i => SourceProfile.owner β (faceState L frozen x i)) S =
      source (fun i : {i // i ∈ L} => A i) β (fun i => SourceProfile.owner β (x i)) S := by
  rw [source_eq_live A β L (fun i => SourceProfile.owner β (faceState L frozen x i)) ?_ S]
  · congr 1
    funext i
    simp [faceState, i.property]
  · intro i hi
    simp only [faceState, dif_neg hi]
    rcases hfrozen i hi with hm | hp
    · rw [hm, SourceProfile.owner_neg_one hβ]
    · rw [hp, SourceProfile.owner_one hβ]

omit [Fintype ι] [DecidableEq ι] in
theorem live_owner_weights_pos {β : ℝ} (hβ : 0 < β) (L : Finset ι)
    (x : {i // i ∈ L} → ℝ) (hx : ∀ i, x i ∈ Set.Ioo (-1 : ℝ) 1) :
    ∀ i, 0 < SourceProfile.owner β (x i) := fun i => SourceProfile.owner_pos hβ (hx i)

omit [Fintype ι] [DecidableEq ι] in
theorem contDiffAt_live_owner_weights (β : ℝ) (L : Finset ι)
    (x : {i // i ∈ L} → ℝ) (hx : ∀ i, x i ∈ Set.Ioo (-1 : ℝ) 1) :
    ContDiffAt ℝ ∞ (fun y : {i // i ∈ L} → ℝ => fun i => SourceProfile.owner β (y i)) x := by
  apply contDiffAt_pi.mpr
  intro i
  have ho := (SourceProfile.contDiffOn_owner β ∞).contDiffAt (isOpen_Ioo.mem_nhds (hx i))
  exact ho.comp x (contDiff_apply ℝ ℝ i).contDiffAt

/-- Smooth fidelity on a literal open cube face, with frozen endpoint coefficients removed
only from the source. The full density remains faithful in the original ambient space. -/
theorem contDiffAt_jointFaceSourceFidelity (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (k : ℕ) (hk : 1 ≤ k) (L : Finset ι) (frozen : ι → ℝ)
    (hfrozen : ∀ i, i ∉ L → frozen i = -1 ∨ frozen i = 1)
    (x : {i // i ∈ L} → ℝ) (hx : ∀ i, x i ∈ Set.Ioo (-1 : ℝ) 1)
    (S : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ))
    (hS : (S : Matrix (n ⊕ n) (n ⊕ n) ℂ).PosDef) :
    ContDiffAt ℝ ∞
      (fun P : ({i // i ∈ L} → ℝ) × selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ) =>
        2 * fidelity (P.2 : Matrix _ _ ℂ)
          (source A ((1 : ℝ) / (2 : ℝ) ^ k)
            (fun i => SourceProfile.owner ((1 : ℝ) / (2 : ℝ) ^ k) (faceState L frozen P.1 i))
            (P.2 : Matrix _ _ ℂ))) (x, S) := by
  have hb : 0 < (1 : ℝ) / (2 : ℝ) ^ k := by positivity
  have hw := contDiffAt_live_owner_weights ((1 : ℝ) / (2 : ℝ) ^ k) L x hx
  have hmap : ContDiffAt ℝ ∞
      (fun P : ({i // i ∈ L} → ℝ) × selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ) =>
        ((fun i => SourceProfile.owner ((1 : ℝ) / (2 : ℝ) ^ k) (P.1 i)), P.2)) (x, S) :=
    (hw.comp (x, S) (f := Prod.fst) contDiffAt_fst).prodMk contDiffAt_snd
  have h := (contDiffAt_jointSourceFidelity (fun i : {i // i ∈ L} => A i)
    (fun i => hA i) k hk (fun i => SourceProfile.owner ((1 : ℝ) / (2 : ℝ) ^ k) (x i))
    (live_owner_weights_pos hb L x hx) S hS).comp (x, S) hmap
  convert h using 1
  funext P
  simp only [Function.comp_def, source_face_eq_live A hb L frozen hfrozen]

end Face

end HigherRankKS
