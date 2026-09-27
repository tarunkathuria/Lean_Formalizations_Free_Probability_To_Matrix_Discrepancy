import HigherRankKS.SourceDerivatives
import HigherRankKS.BalancedTransportResponse

open Matrix MatrixSpencer Filter Set
open scoped Topology BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
noncomputable section
namespace HigherRankKS.ReducedSourceVelocity
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
local instance reducedVelocityCStar {j : Type*} [Fintype j] [DecidableEq j] :
    CStarAlgebra (Matrix j j ℂ) := {}
local instance reducedVelocitySpace :
    NormedSpace ℝ (selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ)) := inferInstance

private theorem deriv_linear {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F)
    (f : ℝ → E) (hf : DifferentiableAt ℝ f 0) :
    deriv (fun t => L (f t)) 0 = L (deriv f 0) := by
  exact (L.hasFDerivAt.comp_hasDerivAt 0 hf.hasDerivAt).deriv

set_option maxHeartbeats 800000 in
/-- Actual supported source velocity is the compression of the full
coefficient and density derivative, including the nonlinear density term. -/
theorem source_velocity (A : ι → Matrix n n ℂ)
    (k : ℕ) (hk : 1 ≤ k) (c : ℝ → ι → ℝ) (hcs : ContDiffAt ℝ 2 c 0)
    (hc : ∀ i, 0 < c 0 i)
    (S X : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ))
    (hS : (S : Matrix (n ⊕ n) (n ⊕ n) ℂ).PosDef) :
    let G := fun t : ℝ => jointReducedSourcePair A ((1 : ℝ) / 2 ^ k) (c t, S + t • X)
    ((deriv G 0).2 : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ) =
      (sourceEmbedding A)ᴴ *
        (∑ i, (deriv (fun t => c t i) 0 • SourceDerivatives.term ((1 : ℝ) / 2 ^ k) (A i) S +
          c 0 i • fderiv ℝ (SourceDerivatives.term ((1 : ℝ) / 2 ^ k) (A i)) S X)) *
        sourceEmbedding A := by
  let P := fun t : ℝ => (c t, S + t • X)
  let G := fun t : ℝ => jointReducedSourcePair A ((1 : ℝ) / 2 ^ k) (P t)
  have hP : ContDiffAt ℝ 2 P 0 := hcs.prodMk (by fun_prop)
  have hP0 : P 0 = (c 0, S) := by simp [P]
  have hg : DifferentiableAt ℝ G 0 := by
    have hb : ContDiffAt ℝ ∞ (jointReducedSourcePair A ((1 : ℝ) / 2 ^ k)) (P 0) := by
      rw [hP0]
      exact contDiffAt_jointReducedSourcePair A k hk (c 0) S hS
    exact (hb.differentiableAt (by simp)).comp 0 (hP.differentiableAt (by norm_num))
  have he := deriv_linear ((hermitianInclusion (n := SourceCarrierIndex A)).comp
    (ContinuousLinearMap.snd ℝ _ _)) G hg
  change deriv (fun t => ((G t).2 : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ)) 0 =
    ((deriv G 0).2 : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ) at he
  change ((deriv G 0).2 : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ) = _
  rw [← he]
  have heq : (fun t => ((G t).2 : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ)) =ᶠ[𝓝 0]
      (fun t => compressedSource A ((1 : ℝ) / 2 ^ k) (c t) ((S + t • X) : Matrix (n ⊕ n) (n ⊕ n) ℂ)) := by
    have hcoeff : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ i, 0 < c t i := by
      apply Filter.eventually_all.mpr
      intro i
      exact ((continuous_apply i).continuousAt.comp hcs.continuousAt).eventually
        (isOpen_Ioi.mem_nhds (hc i))
    have hline : Tendsto (fun t : ℝ => S + t • X) (𝓝 0) (𝓝 S) := by
      simpa using ((continuous_const.add (continuous_id.smul continuous_const)).continuousAt :
        ContinuousAt (fun t : ℝ => S + t • X) 0).tendsto
    filter_upwards [hcoeff, hline.eventually (eventually_posDef_of_posDef S hS)] with t ht hSt
    exact jointReducedSourcePair_snd_coe A _ (P t) (fun i => (ht i).le) hSt.posSemidef
  rw [heq.deriv_eq]
  have hsource : DifferentiableAt ℝ
      (fun t : ℝ => source A ((1 : ℝ) / 2 ^ k) (c t) ((S + t • X) : Matrix (n ⊕ n) (n ⊕ n) ℂ)) 0 := by
    have hb : ContDiffAt ℝ ∞
        (fun p : (ι → ℝ) × selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ) =>
          source A ((1 : ℝ) / 2 ^ k) p.1 p.2) (P 0) := by
      rw [hP0]
      exact contDiffAt_jointSource A k hk (c 0) S hS
    exact (hb.differentiableAt (by simp)).comp 0 (hP.differentiableAt (by norm_num))
  have hcomp := deriv_linear (matrixExtensionCLM (sourceEmbedding A)ᴴ) _ hsource
  simp only [matrixExtensionCLM_apply, Matrix.conjTranspose_conjTranspose] at hcomp
  rw [show (fun t : ℝ => compressedSource A ((1 : ℝ) / 2 ^ k) (c t)
      ((S + t • X) : Matrix (n ⊕ n) (n ⊕ n) ℂ)) =
      (fun t => (sourceEmbedding A)ᴴ * source A ((1 : ℝ) / 2 ^ k) (c t)
      ((S + t • X) : Matrix (n ⊕ n) (n ⊕ n) ℂ) * sourceEmbedding A) from rfl,
    hcomp, SourceDerivatives.source_first_affine_density A k hk c
      (hcs.differentiableAt (by norm_num)) S X hS]

/-- The first reduced input differentiates to the compression of the full
ambient variation, with no restriction on its off-support entries. -/
theorem density_velocity (A : ι → Matrix n n ℂ)
    (k : ℕ) (hk : 1 ≤ k) (c : ℝ → ι → ℝ) (hcs : ContDiffAt ℝ 2 c 0)
    (S X : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ))
    (hS : (S : Matrix (n ⊕ n) (n ⊕ n) ℂ).PosDef) :
    let G := fun t : ℝ => jointReducedSourcePair A ((1 : ℝ) / 2 ^ k) (c t, S + t • X)
    ((deriv G 0).1 : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ) =
      (sourceEmbedding A)ᴴ * (X : Matrix (n ⊕ n) (n ⊕ n) ℂ) * sourceEmbedding A := by
  let P := fun t : ℝ => (c t, S + t • X)
  let G := fun t : ℝ => jointReducedSourcePair A ((1 : ℝ) / 2 ^ k) (P t)
  have hP : ContDiffAt ℝ 2 P 0 := hcs.prodMk (by fun_prop)
  have hb : ContDiffAt ℝ ∞ (jointReducedSourcePair A ((1 : ℝ) / 2 ^ k)) (P 0) := by
    simpa [P] using contDiffAt_jointReducedSourcePair A k hk (c 0) S hS
  have hg : DifferentiableAt ℝ G 0 :=
    (hb.differentiableAt (by simp)).comp 0 (hP.differentiableAt (by norm_num))
  have he := deriv_linear ((hermitianInclusion (n := SourceCarrierIndex A)).comp
    (ContinuousLinearMap.fst ℝ _ _)) G hg
  change deriv (fun t => ((G t).1 : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ)) 0 =
    ((deriv G 0).1 : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ) at he
  change ((deriv G 0).1 : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ) = _
  rw [← he]
  have hd := ((hermitianInclusion (n := SourceCarrierIndex A)).comp
    (hermitianRectangularCompressionCLM (sourceEmbedding A))).hasFDerivAt.comp_hasDerivAt
      (0 : ℝ) ((hasDerivAt_const (0 : ℝ) S).add ((hasDerivAt_id (0 : ℝ)).smul_const X))
  simpa only [Function.comp_def, Pi.add_apply, id_eq, one_smul, zero_add] using hd.deriv

/-- The actual balanced mismatch is density motion minus the true nonlinear
source channel and the external coefficient forcing. -/
theorem mismatch_eq (A : ι → Matrix n n ℂ)
    (k : ℕ) (hk : 1 ≤ k) (c : ℝ → ι → ℝ) (hcs : ContDiffAt ℝ 2 c 0)
    (hc : ∀ i, 0 < c 0 i)
    (S X : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ))
    (hS : (S : Matrix (n ⊕ n) (n ⊕ n) ℂ).PosDef)
    (T : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ) :
    let G := fun t : ℝ => jointReducedSourcePair A ((1 : ℝ) / 2 ^ k) (c t, S + t • X)
    BalancedTransportResponse.mismatch T
      ((deriv G 0).1 : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ)
      ((deriv G 0).2 : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ) =
    (CFC.sqrt T)⁻¹ * ((sourceEmbedding A)ᴴ * (X : Matrix (n ⊕ n) (n ⊕ n) ℂ) * sourceEmbedding A) * (CFC.sqrt T)⁻¹ -
      (∑ i, c 0 i • (CFC.sqrt T * ((sourceEmbedding A)ᴴ *
        fderiv ℝ (SourceDerivatives.term ((1 : ℝ) / 2 ^ k) (A i)) S X * sourceEmbedding A) * CFC.sqrt T)) -
      (∑ i, deriv (fun t => c t i) 0 • (CFC.sqrt T * ((sourceEmbedding A)ᴴ *
        SourceDerivatives.term ((1 : ℝ) / 2 ^ k) (A i) S * sourceEmbedding A) * CFC.sqrt T)) := by
  dsimp only
  rw [BalancedTransportResponse.mismatch, density_velocity A k hk c hcs S X hS,
    source_velocity A k hk c hcs hc S X hS]
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_smul, Matrix.smul_mul, Finset.sum_add_distrib]
  abel

end HigherRankKS.ReducedSourceVelocity
