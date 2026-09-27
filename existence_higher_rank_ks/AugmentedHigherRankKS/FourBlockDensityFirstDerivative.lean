import AugmentedHigherRankKS.FourBlockPotentialFirstDerivative
import AugmentedHigherRankKS.FourBlockSourceDifferential
import AugmentedHigherRankKS.FourBlockSupportedSource

/-! The complete supported density derivative of the nonlinear fidelity. -/
noncomputable section
open Matrix MatrixSpencer HigherRankKS Filter Set
open scoped Topology ContDiff BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace AugmentedHigherRankKS
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
local instance densityFirstCStar {j : Type*} [Fintype j] [DecidableEq j] :
  CStarAlgebra (Matrix j j ℂ) := {}

set_option maxHeartbeats 800000 in
theorem nonlinearSourceFidelity_fderiv (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) (k : ℕ) (hk : 1 ≤ k)
    (c : ι → ℝ) (hc : ∀ i, 0 < c i)
    (S X : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ))
    (hS : (S : Matrix (FourSpin n) (FourSpin n) ℂ).PosDef) :
    let β := (1:ℝ)/2^k
    let Z := SupportedSpin.transport A β c S
    fderiv ℝ (nonlinearSourceFidelity A β c) S X =
      realTrace (Z⁻¹ * SupportedSpin.density A X) +
      realTrace (Z * ((sourceEmbedding A)ᴴ * fderiv ℝ (densitySource A β c) S X * sourceEmbedding A)) := by
  dsimp only
  let β := (1:ℝ)/2^k
  let G := fun t : ℝ => jointReducedSourcePair A β (c, S+t • X)
  have hl : HasDerivAt (fun t : ℝ => S+t • X) X 0 := by
    simpa only [zero_add, one_smul, Pi.add_apply] using (hasDerivAt_const (0:ℝ) S).add ((hasDerivAt_id (0:ℝ)).smul_const X)
  have hline : Tendsto (fun t : ℝ => S+t • X) (𝓝 0) (𝓝 S) := by
    simpa only [zero_smul, add_zero] using hl.continuousAt.tendsto
  have hG : DifferentiableAt ℝ G 0 := by
    have hp : ContDiffAt ℝ ∞ (fun t : ℝ => ((c,S+t • X) :
        (ι → ℝ) × selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ))) 0 := by fun_prop
    have hb : ContDiffAt ℝ ∞ (jointReducedSourcePair A β) (c,S+(0:ℝ) • X) := by
      simpa only [zero_smul, add_zero] using contDiffAt_jointReducedSourcePair A k hk c S hS
    exact (hb.comp 0 hp).differentiableAt (by simp)
  have he1 : ((G 0).1 : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ) =
      SupportedSpin.density A S := by
    simpa only [G, zero_smul, add_zero] using hermitianRectangularCompressionCLM_coe (sourceEmbedding A) S
  have he2 : ((G 0).2 : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ) =
      compressedSource A β c S := by
    simpa only [G, zero_smul, add_zero] using jointReducedSourcePair_snd_coe A β (c,S)
      (fun i => (hc i).le) hS.posSemidef
  have hp1 : ((G 0).1 : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ).PosDef := by
    rw [he1]; exact SupportedSpin.density_posDef A hS
  have hp2 : ((G 0).2 : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ).PosDef := by
    rw [he2]; exact compressedSource_posDef A hA hc hS k hk
  have hv1 : ((deriv G 0).1 : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ) =
      SupportedSpin.density A X := by
    exact ReducedSourceVelocity.density_velocity A k hk (fun _ => c) contDiffAt_const S X hS
  have hs := (densitySource_smooth A k hk c S hS).differentiableAt (by simp)
  have hsc := (matrixExtensionCLM (sourceEmbedding A)ᴴ).hasFDerivAt.comp_hasDerivAt 0
    (hs.hasFDerivAt.comp_hasDerivAt_of_eq 0 hl (by simp))
  have hv2 : ((deriv G 0).2 : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ) =
      (sourceEmbedding A)ᴴ * fderiv ℝ (densitySource A β c) S X * sourceEmbedding A := by
    have he := (((hermitianInclusion (n := SourceCarrierIndex A)).comp
      (ContinuousLinearMap.snd ℝ _ _)).hasFDerivAt.comp_hasDerivAt 0 hG.hasDerivAt).deriv
    have heq : (fun t => ((G t).2 : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ)) =ᶠ[𝓝 0]
        (fun t => (sourceEmbedding A)ᴴ * source A β c (S+t • X) * sourceEmbedding A) := by
      have hnear : ∀ᶠ t in 𝓝 (0:ℝ), ((S+t • X) : Matrix (FourSpin n) (FourSpin n) ℂ).PosDef :=
        hline.eventually (eventually_posDef_of_posDef S hS)
      filter_upwards [hnear] with t ht
      exact jointReducedSourcePair_snd_coe A β (c,S+t • X) (fun i => (hc i).le) ht.posSemidef
    change deriv (fun t => ((G t).2 : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ)) 0 = ((deriv G 0).2 : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ) at he
    rw [← he, heq.deriv_eq]
    have hh := hsc.deriv
    have hefun : (⇑(matrixExtensionCLM (sourceEmbedding A)ᴴ) ∘ densitySource A ((1:ℝ)/2^k) c ∘
        (fun t : ℝ => S+t • X)) =
        (fun t => (sourceEmbedding A)ᴴ * source A β c (S+t • X) * sourceEmbedding A) := by
      funext t
      simp only [Function.comp_apply, densitySource, matrixExtensionCLM_apply,
        Matrix.conjTranspose_conjTranspose]
      rfl
    rw [hefun] at hh
    simpa only [matrixExtensionCLM_apply, Matrix.conjTranspose_conjTranspose] using hh
  have hd := ((hasFDerivAt_doubleFidelity (G 0).1 (G 0).2 hp1 hp2).comp_hasDerivAt
    0 hG.hasDerivAt).deriv
  change deriv (fun t => doubleFidelity (G t)) 0 =
    realTrace ((transportOptimizer ((G 0).1 : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ) (G 0).2)⁻¹ *
      ((deriv G 0).1 : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ)) +
    realTrace (transportOptimizer ((G 0).1 : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ) (G 0).2 *
      ((deriv G 0).2 : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ)) at hd
  rw [he1,he2,hv1,hv2] at hd
  have heq : (fun t => nonlinearSourceFidelity A β c (S+t • X)) =ᶠ[𝓝 0]
      (fun t => doubleFidelity (G t)) := by
    have hnear : ∀ᶠ t in 𝓝 (0:ℝ), ((S+t • X) : Matrix (FourSpin n) (FourSpin n) ℂ).PosDef :=
      hline.eventually (eventually_posDef_of_posDef S hS)
    filter_upwards [hnear] with t ht
    exact jointSourceFidelity_eq_reduced A hA k hk (c,S+t • X) hc ht
  have hf := ((contDiffAt_nonlinearSourceFidelity A hA k hk c hc S hS).differentiableAt (by simp)).hasFDerivAt
  exact (hf.comp_hasDerivAt_of_eq 0 hl (by simp)).deriv.symm.trans (heq.deriv_eq.trans hd)

end AugmentedHigherRankKS
