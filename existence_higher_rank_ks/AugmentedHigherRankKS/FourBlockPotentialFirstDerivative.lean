import AugmentedHigherRankKS.FourBlockPotentialSmoothness
import MatrixSpencer.FidelityDerivative
import AugmentedHigherRankKS.FourBlockReducedVelocity

/-! First-order envelope identities for the actual four-block potential. -/

open Matrix MatrixSpencer Filter Set
open scoped Topology BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff

noncomputable section
namespace AugmentedHigherRankKS

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n] [Nonempty n]
local instance firstDerivativeCStar {j : Type*} [Fintype j] [DecidableEq j] :
    CStarAlgebra (Matrix j j ℂ) := {}
local instance firstDerivativeSpace :
    NormedSpace ℝ (selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ)) := inferInstance

/-- At an actual maximizing density, the parameter derivative of the
optimized value equals the fixed-density derivative. The optimizing
density is obtained mathematically, not supplied as a solver primitive. -/
theorem potential_deriv_eq_fixed_density
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (k : ℕ) (hk : 1 ≤ k) (θ : ℝ) (hθ : 0 < θ)
    (H : ℝ → Matrix (FourSpin n) (FourSpin n) ℂ) (c : ℝ → ι → ℝ)
    (hH : ContDiffAt ℝ ∞ H 0) (hcs : ContDiffAt ℝ ∞ c 0)
    (hc : ∀ i, 0 < c 0 i)
    (S : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ))
    (hS : (S : Matrix (FourSpin n) (FourSpin n) ℂ) ∈ densitySet)
    (hmax : ∀ T ∈ densitySet, objective (H 0) A ((1 : ℝ) / 2 ^ k) (c 0) θ T ≤
      objective (H 0) A ((1 : ℝ) / 2 ^ k) (c 0) θ S) :
    deriv (fun t => potential (H t) A ((1 : ℝ) / 2 ^ k) (c t) θ) 0 =
      deriv (fun t => objective (H t) A ((1 : ℝ) / 2 ^ k) (c t) θ S) 0 := by
  have hβ : 0 < (1 : ℝ) / 2 ^ k := by positivity
  have hβ1 : (1 : ℝ) / 2 ^ k < 1 := by
    apply (div_lt_one (by positivity)).mpr
    exact one_lt_pow₀ (by norm_num) (by omega)
  have hSpos := maximizer_posDef (H 0) A hβ hβ1 (fun i => (hc i).le) hθ hS hmax
  have hp := (contDiffAt_potential_of_positive_weights A hA k hk θ hθ H c 0
    hH hcs hc).differentiableAt (by simp)
  have ho : DifferentiableAt ℝ
      (fun t => objective (H t) A ((1 : ℝ) / 2 ^ k) (c t) θ S) 0 := by
    exact ((contDiffAt_objective_of_data A hA k hk θ H c 0 hH hcs hc S hSpos).comp 0
      (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
  have hnear : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ i, 0 < c t i := by
    apply Filter.eventually_all.mpr
    intro i
    exact ((continuous_apply i).continuousAt.comp hcs.continuousAt).eventually
      (isOpen_Ioi.mem_nhds (hc i))
  have hmin : IsLocalMin
      (fun t => potential (H t) A ((1 : ℝ) / 2 ^ k) (c t) θ -
        objective (H t) A ((1 : ℝ) / 2 ^ k) (c t) θ S) 0 := by
    filter_upwards [hnear] with t ht
    change potential (H 0) A _ (c 0) θ - objective (H 0) A _ (c 0) θ S ≤ _
    rw [potential_eq_of_optimizer (H 0) A _ (c 0) θ hS hmax, sub_self]
    exact sub_nonneg.mpr (objective_le_potential (H t) A hβ.le hβ1.le
      (fun i => (ht i).le) θ hS)
  exact sub_eq_zero.mp (hmin.hasDerivAt_eq_zero (hp.hasDerivAt.sub ho.hasDerivAt))


/-- The fixed-density fidelity derivative is the supported transport pairing
with the actual reserve-source derivative. -/
theorem fixed_density_fidelity_deriv
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (k : ℕ) (hk : 1 ≤ k) (c : ℝ → ι → ℝ)
    (hcs : ContDiffAt ℝ ∞ c 0) (hc : ∀ i, 0 < c 0 i)
    (S : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ))
    (hS : (S : Matrix (FourSpin n) (FourSpin n) ℂ).PosDef) :
    deriv (fun t => jointSourceFidelity A ((1 : ℝ) / 2 ^ k) (c t, S)) 0 =
      realTrace (transportOptimizer
        ((sourceEmbedding A)ᴴ * (S : Matrix _ _ ℂ) * sourceEmbedding A)
        (compressedSource A ((1 : ℝ) / 2 ^ k) (c 0) S) *
        compressedSource A ((1 : ℝ) / 2 ^ k) (fun i => deriv (fun t => c t i) 0) S) := by
  let G := fun t : ℝ => jointReducedSourcePair A ((1 : ℝ) / 2 ^ k) (c t, S)
  have hG : DifferentiableAt ℝ G 0 := by
    have hp : ContDiffAt ℝ ∞ (fun t : ℝ => (c t, S)) 0 :=
      hcs.prodMk contDiffAt_const
    exact ((contDiffAt_jointReducedSourcePair A k hk (c 0) S hS).comp 0 hp).differentiableAt
      (by simp)
  have he1 : ((G 0).1 : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ) =
      (sourceEmbedding A)ᴴ * (S : Matrix _ _ ℂ) * sourceEmbedding A :=
    hermitianRectangularCompressionCLM_coe (sourceEmbedding A) S
  have he2 : ((G 0).2 : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ) =
      compressedSource A ((1 : ℝ) / 2 ^ k) (c 0) S :=
    jointReducedSourcePair_snd_coe A _ (c 0, S) (fun i => (hc i).le) hS.posSemidef
  have hp1 : ((G 0).1 : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ).PosDef := by
    rw [he1]
    exact posDef_isometry_compression (sourceEmbedding A) (krausSupportEmbedding_isometry _) hS
  have hp2 : ((G 0).2 : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ).PosDef := by
    rw [he2]
    exact compressedSource_posDef A hA hc hS k hk
  have htwo : ContDiffAt ℝ 2 c 0 := hcs.of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have hv1 : ((deriv G 0).1 : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ) = 0 := by
    simpa only [zero_smul, smul_zero, add_zero, ZeroMemClass.coe_zero, Matrix.mul_zero, Matrix.zero_mul,
      G] using ReducedSourceVelocity.density_velocity A k hk c htwo S 0 hS
  have hv2 : ((deriv G 0).2 : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ) =
      compressedSource A ((1 : ℝ) / 2 ^ k) (fun i => deriv (fun t => c t i) 0) S := by
    simpa only [zero_smul, smul_zero, add_zero, map_zero, G, compressedSource, source,
      SourceDerivatives.term] using ReducedSourceVelocity.source_velocity A k hk c htwo hc S 0 hS
  have hd := ((hasFDerivAt_doubleFidelity (G 0).1 (G 0).2 hp1 hp2).comp_hasDerivAt
    0 hG.hasDerivAt).deriv
  change deriv (fun t => doubleFidelity (G t)) 0 =
    realTrace ((transportOptimizer ((G 0).1 : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ) (G 0).2)⁻¹ *
      ((deriv G 0).1 : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ)) +
    realTrace (transportOptimizer ((G 0).1 : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ) (G 0).2 *
      ((deriv G 0).2 : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ)) at hd
  rw [he1, he2, hv1, hv2, Matrix.mul_zero, realTrace_zero, zero_add] at hd
  have hnear : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ i, 0 < c t i := by
    apply Filter.eventually_all.mpr
    intro i
    exact ((continuous_apply i).continuousAt.comp hcs.continuousAt).eventually
      (isOpen_Ioi.mem_nhds (hc i))
  have heq : (fun t => jointSourceFidelity A ((1 : ℝ) / 2 ^ k) (c t, S)) =ᶠ[𝓝 0]
      (fun t => doubleFidelity (G t)) := by
    filter_upwards [hnear] with t ht
    exact jointSourceFidelity_eq_reduced A hA k hk (c t, S) ht hS
  exact heq.deriv_eq.trans hd


/-- The envelope derivative consists of the center pairing and the supported
transport pairing. This is the preparation formula for the actual potential. -/
theorem potential_deriv_formula
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (k : ℕ) (hk : 1 ≤ k) (θ : ℝ) (hθ : 0 < θ)
    (H : ℝ → Matrix (FourSpin n) (FourSpin n) ℂ) (c : ℝ → ι → ℝ)
    (hH : ContDiffAt ℝ ∞ H 0) (hcs : ContDiffAt ℝ ∞ c 0)
    (hc : ∀ i, 0 < c 0 i)
    (S : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ))
    (hS : (S : Matrix (FourSpin n) (FourSpin n) ℂ) ∈ densitySet)
    (hmax : ∀ T ∈ densitySet, objective (H 0) A ((1 : ℝ) / 2 ^ k) (c 0) θ T ≤
      objective (H 0) A ((1 : ℝ) / 2 ^ k) (c 0) θ S) :
    deriv (fun t => potential (H t) A ((1 : ℝ) / 2 ^ k) (c t) θ) 0 =
      realTrace (deriv H 0 * (S : Matrix _ _ ℂ)) +
      realTrace (transportOptimizer
        ((sourceEmbedding A)ᴴ * (S : Matrix _ _ ℂ) * sourceEmbedding A)
        (compressedSource A ((1 : ℝ) / 2 ^ k) (c 0) S) *
        compressedSource A ((1 : ℝ) / 2 ^ k) (fun i => deriv (fun t => c t i) 0) S) := by
  have hβ : 0 < (1 : ℝ) / 2 ^ k := by positivity
  have hβ1 : (1 : ℝ) / 2 ^ k < 1 := by
    apply (div_lt_one (by positivity)).mpr
    exact one_lt_pow₀ (by norm_num) (by omega)
  have hSpos := maximizer_posDef (H 0) A hβ hβ1 (fun i => (hc i).le) hθ hS hmax
  rw [potential_deriv_eq_fixed_density A hA k hk θ hθ H c hH hcs hc S hS hmax]
  have ht : HasDerivAt (fun t => realTrace (H t * (S : Matrix _ _ ℂ)))
      (realTrace (deriv H 0 * (S : Matrix _ _ ℂ))) 0 := by
    exact realTraceCLM.hasFDerivAt.comp_hasDerivAt 0
      ((hH.differentiableAt (by simp)).hasDerivAt.mul_const (S : Matrix _ _ ℂ))
  have hf : DifferentiableAt ℝ
      (fun t => jointSourceFidelity A ((1 : ℝ) / 2 ^ k) (c t, S)) 0 := by
    exact ((contDiffAt_jointSourceFidelity A hA k hk (c 0) hc S hSpos).comp 0
      (hcs.prodMk contDiffAt_const)).differentiableAt (by simp)
  have hd := ((ht.add hf.hasDerivAt).add_const
    (2 * θ * realTrace (CFC.sqrt (S : Matrix (FourSpin n) (FourSpin n) ℂ)))).deriv
  simp only [fixed_density_fidelity_deriv A hA k hk c hcs hc S hSpos] at hd
  exact hd

end AugmentedHigherRankKS
