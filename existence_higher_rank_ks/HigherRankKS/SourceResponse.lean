import HigherRankKS.SourceSmoothness
import HigherRankKS.BalancedTransportResponse
import MatrixSpencer.FidelityHessian
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! Actual second derivatives of fidelity along a curved nonlinear source.
The source acceleration is retained explicitly; it is not discarded as it
would be for a linear Kraus source. -/

open Matrix MatrixSpencer Filter Set
open scoped Topology BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff

noncomputable section
namespace HigherRankKS.SourceResponse

section Joint
variable {m : Type*} [Fintype m] [DecidableEq m]
local instance sourceResponseCStar : CStarAlgebra (Matrix m m ℂ) := {}
local instance sourceResponseSpace : NormedSpace ℝ (selfAdjoint (Matrix m m ℂ)) := inferInstance

/-- The exact second-order chain rule retains the nonlinear source
acceleration and the actual optimizing transport response. -/
theorem doubleFidelity_second_curve
    (G : ℝ → selfAdjoint (Matrix m m ℂ) × selfAdjoint (Matrix m m ℂ))
    (hG : ContDiffAt ℝ 2 G 0)
    (hS : ((G 0).1 : Matrix m m ℂ).PosDef)
    (hM : ((G 0).2 : Matrix m m ℂ).PosDef) :
    let T := transportOptimizer ((G 0).1 : Matrix m m ℂ) ((G 0).2 : Matrix m m ℂ)
    let U := fderiv ℝ jointTransportOptimizer (G 0) (deriv G 0)
    iteratedDeriv 2 (fun t => doubleFidelity (G t)) 0 =
      -2 * realTrace (T⁻¹ * U * ((G 0).2 : Matrix m m ℂ) * U) +
      realTrace (T⁻¹ * ((iteratedDeriv 2 G 0).1 : Matrix m m ℂ)) +
      realTrace (T * ((iteratedDeriv 2 G 0).2 : Matrix m m ℂ)) := by
  have hf : ContDiffAt ℝ 2 (doubleFidelity (n := m)) (G 0) :=
    (contDiffAt_doubleFidelity (G 0).1 (G 0).2 hS hM).of_le
      (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have h := iteratedDeriv_vcomp_two hf hG
  rw [iteratedFDeriv_two_apply,
    fderiv_fderiv_doubleFidelity_quadratic (G 0).1 (G 0).2 (deriv G 0).1 (deriv G 0).2 hS hM,
    (hasFDerivAt_doubleFidelity (G 0).1 (G 0).2 hS hM).fderiv,
    jointTransportFunctional_apply] at h
  dsimp only at h ⊢
  simpa only [Function.comp_def, add_assoc] using h

end Joint

section NonlinearSource
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
local instance nonlinearResponseCStar {j : Type*} [Fintype j] [DecidableEq j] :
    CStarAlgebra (Matrix j j ℂ) := {}
local instance nonlinearResponseSpace :
    NormedSpace ℝ (selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ)) := inferInstance

/-- The exact response formula for the actual singular-source fidelity.
The source is compressed to its proved fixed support; the varying density
remains an arbitrary full ambient Hermitian density. -/
theorem nonlinear_fidelity_second_curve
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (k : ℕ) (hk : 1 ≤ k)
    (P : ℝ → (ι → ℝ) × selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ))
    (hP : ContDiffAt ℝ 2 P 0) (hc : ∀ i, 0 < (P 0).1 i)
    (hS : ((P 0).2 : Matrix (n ⊕ n) (n ⊕ n) ℂ).PosDef) :
    let G := fun t => jointReducedSourcePair A ((1 : ℝ) / 2 ^ k) (P t)
    let T := transportOptimizer ((G 0).1 : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ)
      ((G 0).2 : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ)
    let U := fderiv ℝ jointTransportOptimizer (G 0) (deriv G 0)
    iteratedDeriv 2 (fun t => jointSourceFidelity A ((1 : ℝ) / 2 ^ k) (P t)) 0 =
      -2 * realTrace (T⁻¹ * U * ((G 0).2 : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ) * U) +
      realTrace (T⁻¹ * ((iteratedDeriv 2 G 0).1 : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ)) +
      realTrace (T * ((iteratedDeriv 2 G 0).2 : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ)) := by
  let G := fun t => jointReducedSourcePair A ((1 : ℝ) / 2 ^ k) (P t)
  have hR : ContDiffAt ℝ 2 (jointReducedSourcePair A ((1 : ℝ) / 2 ^ k)) (P 0) :=
    (contDiffAt_jointReducedSourcePair A k hk (P 0).1 (P 0).2 hS).of_le
      (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have hG : ContDiffAt ℝ 2 G 0 := hR.comp 0 hP
  have hfirst : ((G 0).1 : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ).PosDef :=
    posDef_isometry_compression (sourceEmbedding A) (krausSupportEmbedding_isometry _) hS
  have hsecond : ((G 0).2 : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ).PosDef := by
    change ((jointReducedSourcePair A ((1 : ℝ) / 2 ^ k) (P 0)).2 :
      Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ).PosDef
    rw [jointReducedSourcePair_snd_coe A _ (P 0) (fun i => (hc i).le) hS.posSemidef]
    exact compressedSource_posDef A hA hc hS k hk
  have hnear : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ i, 0 < (P t).1 i := by
    apply Filter.eventually_all.mpr
    intro i
    exact ((continuous_apply i).continuousAt.comp hP.continuousAt.fst).eventually
      (isOpen_Ioi.mem_nhds (hc i))
  have heq : (fun t => jointSourceFidelity A ((1 : ℝ) / 2 ^ k) (P t)) =ᶠ[𝓝 0]
      (fun t => doubleFidelity (G t)) := by
    filter_upwards [hnear, hP.continuousAt.snd.eventually (eventually_posDef_of_posDef (P 0).2 hS)]
      with t hct hSt
    exact jointSourceFidelity_eq_reduced A hA k hk (P t) hct hSt
  rw [heq.iteratedDeriv_eq 2]
  exact doubleFidelity_second_curve G hG hfirst hsecond

/-- Fixed-support reduced inputs are positive definite at a faithful full
density and positive live weights, even when the full source is singular. -/
theorem reduced_pair_posDef
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (k : ℕ) (hk : 1 ≤ k)
    (P : (ι → ℝ) × selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ))
    (hc : ∀ i, 0 < P.1 i) (hS : (P.2 : Matrix (n ⊕ n) (n ⊕ n) ℂ).PosDef) :
    let G := jointReducedSourcePair A ((1 : ℝ) / 2 ^ k) P
    (G.1 : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ).PosDef ∧
      (G.2 : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ).PosDef := by
  constructor
  · exact posDef_isometry_compression (sourceEmbedding A) (krausSupportEmbedding_isometry _) hS
  · rw [jointReducedSourcePair_snd_coe A _ P (fun i => (hc i).le) hS.posSemidef]
    exact compressedSource_posDef A hA hc hS k hk

/-- The actual nonlinear fidelity second derivative is its source/density
acceleration cost minus the balanced inverse-Sylvester mismatch energy. -/
theorem nonlinear_fidelity_second_curve_energy
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (k : ℕ) (hk : 1 ≤ k)
    (P : ℝ → (ι → ℝ) × selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ))
    (hP : ContDiffAt ℝ 2 P 0) (hc : ∀ i, 0 < (P 0).1 i)
    (hS : ((P 0).2 : Matrix (n ⊕ n) (n ⊕ n) ℂ).PosDef) :
    let G := fun t => jointReducedSourcePair A ((1 : ℝ) / 2 ^ k) (P t)
    let T := transportOptimizer ((G 0).1 : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ)
      ((G 0).2 : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ)
    let hp := reduced_pair_posDef A hA k hk (P 0) hc hS
    iteratedDeriv 2 (fun t => jointSourceFidelity A ((1 : ℝ) / 2 ^ k) (P t)) 0 =
      -SylvesterMetric.energy
        (BalancedTransportResponse.weight ((G 0).1 : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ)
          ((G 0).2 : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ))
        (BalancedTransportResponse.weight_posDef hp.1 hp.2)
        (BalancedTransportResponse.mismatch T
          ((deriv G 0).1 : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ)
          ((deriv G 0).2 : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ)) +
      realTrace (T⁻¹ * ((iteratedDeriv 2 G 0).1 : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ)) +
      realTrace (T * ((iteratedDeriv 2 G 0).2 : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ)) := by
  let G := fun t => jointReducedSourcePair A ((1 : ℝ) / 2 ^ k) (P t)
  have hp := reduced_pair_posDef A hA k hk (P 0) hc hS
  have he := BalancedTransportResponse.doubleFidelity_hessian_eq_energy
    (G 0).1 (G 0).2 (deriv G 0).1 (deriv G 0).2 hp.1 hp.2
  rw [fderiv_fderiv_doubleFidelity_quadratic (G 0).1 (G 0).2 (deriv G 0).1 (deriv G 0).2
    hp.1 hp.2] at he
  have h := nonlinear_fidelity_second_curve A hA k hk P hP hc hS
  dsimp only at h he ⊢
  rw [he] at h
  exact h

end NonlinearSource

end HigherRankKS.SourceResponse
