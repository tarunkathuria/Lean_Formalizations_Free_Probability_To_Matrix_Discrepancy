import AugmentedHigherRankKS.FourBlockCompression

/-! Smoothness of the four-block fidelity using its constructed fixed source support. -/
noncomputable section
open Matrix MatrixSpencer HigherRankKS Filter Topology
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
namespace AugmentedHigherRankKS
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
local instance sourceSmoothCStar {j : Type*} [Fintype j] [DecidableEq j] :
    CStarAlgebra (Matrix j j ℂ) := {}

def jointReducedSourcePair (A : ι → Matrix n n ℂ) (β : ℝ)
    (P : (ι → ℝ) × selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ)) :
    selfAdjoint (Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ) ×
      selfAdjoint (Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ) :=
  (hermitianRectangularCompressionCLM (sourceEmbedding A) P.2,
    hermitianProjection (compressedSource A β P.1 (P.2 : Matrix _ _ ℂ)))

theorem jointReducedSourcePair_snd_coe (A : ι → Matrix n n ℂ) (β : ℝ)
    (P : (ι → ℝ) × selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ))
    (hc : ∀ i, 0 ≤ P.1 i) (hS : (P.2 : Matrix (FourSpin n) (FourSpin n) ℂ).PosSemidef) :
    ((jointReducedSourcePair A β P).2 : Matrix _ _ ℂ) =
      compressedSource A β P.1 (P.2 : Matrix _ _ ℂ) := by
  apply IsSelfAdjoint.coe_selfAdjointPart_apply
  exact ((source_posSemidef A β hc hS).conjTranspose_mul_mul_same (sourceEmbedding A)).isHermitian

theorem contDiffAt_jointReducedSourcePair (A : ι → Matrix n n ℂ)
    (k : ℕ) (hk : 1 ≤ k) (c : ι → ℝ)
    (S : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ))
    (hS : (S : Matrix (FourSpin n) (FourSpin n) ℂ).PosDef) :
    ContDiffAt ℝ ∞ (jointReducedSourcePair A ((1 : ℝ) / (2 : ℝ) ^ k)) (c, S) := by
  have hs := contDiffAt_jointSource A k hk c S hS
  have hc : ContDiffAt ℝ ∞
      (fun P : (ι → ℝ) × selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ) =>
        compressedSource A ((1 : ℝ) / (2 : ℝ) ^ k) P.1 (P.2 : Matrix _ _ ℂ)) (c, S) := by
    simpa only [Function.comp_def, matrixExtensionCLM_apply, Matrix.conjTranspose_conjTranspose,
      compressedSource] using
        (matrixExtensionCLM (sourceEmbedding A)ᴴ).contDiff.contDiffAt.comp (c, S) hs
  exact ((hermitianRectangularCompressionCLM (sourceEmbedding A)).contDiff.contDiffAt.comp
    (c, S) (f := Prod.snd) contDiffAt_snd).prodMk
      ((hermitianProjection (n := SourceCarrierIndex A)).contDiff.contDiffAt.comp (c, S) hc)

def jointSourceFidelity (A : ι → Matrix n n ℂ) (β : ℝ)
    (P : (ι → ℝ) × selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ)) : ℝ :=
  2 * fidelity (P.2 : Matrix _ _ ℂ) (source A β P.1 (P.2 : Matrix _ _ ℂ))

def reducedSourceFidelity (A : ι → Matrix n n ℂ) (β : ℝ)
    (P : (ι → ℝ) × selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ)) : ℝ :=
  doubleFidelity (jointReducedSourcePair A β P)

theorem jointSourceFidelity_eq_reduced (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (k : ℕ) (hk : 1 ≤ k)
    (P : (ι → ℝ) × selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ))
    (hc : ∀ i, 0 < P.1 i) (hS : (P.2 : Matrix (FourSpin n) (FourSpin n) ℂ).PosDef) :
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
    (S : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ))
    (hS : (S : Matrix (FourSpin n) (FourSpin n) ℂ).PosDef) :
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
    (S : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ))
    (hS : (S : Matrix (FourSpin n) (FourSpin n) ℂ).PosDef) :
    ContDiffAt ℝ ∞
      (fun P : (ι → ℝ) × selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ) =>
        2 * fidelity (P.2 : Matrix _ _ ℂ)
          (source A ((1 : ℝ) / (2 : ℝ) ^ k) P.1 (P.2 : Matrix _ _ ℂ))) (c, S) := by
  apply (contDiffAt_reducedSourceFidelity A hA k hk c hc S hS).congr_of_eventuallyEq
  have hnear : ∀ᶠ P : (ι → ℝ) × selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ) in 𝓝 (c, S),
      ∀ i, 0 < P.1 i := by
    apply Filter.eventually_all.mpr
    intro i
    exact (((continuous_apply i).comp continuous_fst).continuousAt (x := (c, S))).eventually
      (IsOpen.mem_nhds isOpen_Ioi (hc i))
  filter_upwards [hnear, (continuous_snd.continuousAt (x := (c, S))).eventually
    (eventually_posDef_of_posDef S hS)] with P hPc hPS
  exact jointSourceFidelity_eq_reduced A hA k hk P hPc hPS


end AugmentedHigherRankKS
