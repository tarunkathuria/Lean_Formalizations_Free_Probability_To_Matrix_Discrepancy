import MatrixSpencer.KrausCompressionBridge

/-!
# Density calculus with the actual, possibly singular, Kraus source

At a positive definite physical density the two constructed compressed arguments
are positive definite. Exact fidelity compression identifies the actual objective
with the smooth reduced objective in a neighborhood. All derivatives below are
derivatives of the original objective, not a redefined surrogate.
-/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
open Filter Topology

namespace MatrixSpencer

noncomputable section

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]

local instance singularDensityCStarAlgebra {m : Type*} [Fintype m] [DecidableEq m] :
    CStarAlgebra (Matrix m m ℂ) := {}
local instance singularDensityNormedSpace {m : Type*} [Fintype m] [DecidableEq m] :
    NormedSpace ℝ (selfAdjoint (Matrix m m ℂ)) := inferInstance
local instance singularDensityEuclideanInner : InnerProductSpace ℂ (EuclideanSpace ℂ n) :=
  PiLp.innerProductSpace (fun _ : n => ℂ)
local instance singularDensityFiniteDimensional :
    FiniteDimensional ℝ (selfAdjoint (Matrix n n ℂ)) :=
  inferInstanceAs (FiniteDimensional ℝ (selfAdjoint.submodule ℝ (Matrix n n ℂ)))

def reducedKrausFidelity (B : ι → Matrix n n ℂ)
    (S : selfAdjoint (Matrix n n ℂ)) : ℝ :=
  doubleFidelity (krausReducedPairCLM B S)

theorem krausSourceFidelity_eventuallyEq_reduced (B : ι → Matrix n n ℂ)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef) :
    krausSourceFidelity B =ᶠ[𝓝 S] reducedKrausFidelity B := by
  filter_upwards [eventually_posDef_of_posDef S hS] with X hX
  change 2 * fidelity (X : Matrix n n ℂ) (krausChannel B (X : Matrix n n ℂ)) =
    2 * fidelity (krausReducedDensityCLM B X : Matrix (Fin (Module.finrank ℂ (krausSupport B))) (Fin (Module.finrank ℂ (krausSupport B))) ℂ)
      (krausReducedSourceCLM B X : Matrix (Fin (Module.finrank ℂ (krausSupport B))) (Fin (Module.finrank ℂ (krausSupport B))) ℂ)
  rw [krausReducedDensityCLM_coe, krausReducedSourceCLM_coe,
    fidelity_kraus_support_compression B hX.posSemidef]

theorem contDiffAt_reducedKrausFidelity (B : ι → Matrix n n ℂ)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef) :
    ContDiffAt ℝ ∞ (reducedKrausFidelity B) S := by
  have hd : (krausReducedDensityCLM B S : Matrix (Fin (Module.finrank ℂ (krausSupport B))) (Fin (Module.finrank ℂ (krausSupport B))) ℂ).PosDef := by
    simpa using krausCompressedDensity_posDef B hS
  have hm : (krausReducedSourceCLM B S : Matrix (Fin (Module.finrank ℂ (krausSupport B))) (Fin (Module.finrank ℂ (krausSupport B))) ℂ).PosDef := by
    simpa using krausCompressedSource_posDef B hS
  exact (contDiffAt_doubleFidelity (krausReducedDensityCLM B S)
    (krausReducedSourceCLM B S) hd hm).comp S (krausReducedPairCLM B).contDiff.contDiffAt

/-- Smoothness of the original source fidelity without source faithfulness. -/
theorem contDiffAt_krausSourceFidelity_source_unrestricted (B : ι → Matrix n n ℂ)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef) :
    ContDiffAt ℝ ∞ (krausSourceFidelity B) S :=
  (contDiffAt_reducedKrausFidelity B S hS).congr_of_eventuallyEq
    (krausSourceFidelity_eventuallyEq_reduced B S hS)

def krausReducedDualPullback (B : ι → Matrix n n ℂ) :=
  (ContinuousLinearMap.compL ℝ (selfAdjoint (Matrix n n ℂ))
    (selfAdjoint (Matrix (Fin (Module.finrank ℂ (krausSupport B)))
      (Fin (Module.finrank ℂ (krausSupport B))) ℂ) ×
      selfAdjoint (Matrix (Fin (Module.finrank ℂ (krausSupport B)))
        (Fin (Module.finrank ℂ (krausSupport B))) ℂ)) ℝ).flip (krausReducedPairCLM B)

theorem hasFDerivAt_krausSourceFidelity_source_unrestricted (B : ι → Matrix n n ℂ)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef) :
    HasFDerivAt (krausSourceFidelity B)
      ((fderiv ℝ (doubleFidelity (n := Fin (Module.finrank ℂ (krausSupport B)))) (krausReducedPairCLM B S)).comp (krausReducedPairCLM B)) S := by
  have hd : (krausReducedDensityCLM B S : Matrix (Fin (Module.finrank ℂ (krausSupport B))) (Fin (Module.finrank ℂ (krausSupport B))) ℂ).PosDef := by
    simpa using krausCompressedDensity_posDef B hS
  have hm : (krausReducedSourceCLM B S : Matrix (Fin (Module.finrank ℂ (krausSupport B))) (Fin (Module.finrank ℂ (krausSupport B))) ℂ).PosDef := by
    simpa using krausCompressedSource_posDef B hS
  have hf := ((contDiffAt_doubleFidelity (krausReducedDensityCLM B S)
    (krausReducedSourceCLM B S) hd hm).differentiableAt
    (by simp : (1 : WithTop ℕ∞) ≤ ∞)).hasFDerivAt.comp S (krausReducedPairCLM B).hasFDerivAt
  exact hf.congr_of_eventuallyEq (krausSourceFidelity_eventuallyEq_reduced B S hS)

theorem hasStrictFDerivAt_fderiv_krausSourceFidelity_source_unrestricted
    (B : ι → Matrix n n ℂ) (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) :
    HasStrictFDerivAt (fun X => fderiv ℝ (krausSourceFidelity B) X)
      ((krausReducedDualPullback B).comp
        ((fderiv ℝ (fun P => fderiv ℝ (doubleFidelity (n := Fin (Module.finrank ℂ (krausSupport B)))) P)
          (krausReducedPairCLM B S)).comp (krausReducedPairCLM B))) S := by
  have hd : (krausReducedDensityCLM B S : Matrix (Fin (Module.finrank ℂ (krausSupport B))) (Fin (Module.finrank ℂ (krausSupport B))) ℂ).PosDef := by
    simpa using krausCompressedDensity_posDef B hS
  have hm : (krausReducedSourceCLM B S : Matrix (Fin (Module.finrank ℂ (krausSupport B))) (Fin (Module.finrank ℂ (krausSupport B))) ℂ).PosDef := by
    simpa using krausCompressedSource_posDef B hS
  have hf := hasStrictFDerivAt_fderiv_doubleFidelity (krausReducedDensityCLM B S)
    (krausReducedSourceCLM B S) hd hm
  rw [← hf.hasFDerivAt.fderiv] at hf
  have hp := (krausReducedDualPullback B).hasStrictFDerivAt.comp S
    (hf.comp S (krausReducedPairCLM B).hasStrictFDerivAt)
  apply hp.congr_of_eventuallyEq
  filter_upwards [eventually_posDef_of_posDef S hS] with X hX
  exact (hasFDerivAt_krausSourceFidelity_source_unrestricted B X hX).fderiv.symm

theorem fderiv_fderiv_krausSourceFidelity_apply_source_unrestricted
    (B : ι → Matrix n n ℂ) (S X Y : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) :
    fderiv ℝ (fun A => fderiv ℝ (krausSourceFidelity B) A) S X Y =
      fderiv ℝ (fun P => fderiv ℝ (doubleFidelity (n := Fin (Module.finrank ℂ (krausSupport B)))) P)
        (krausReducedPairCLM B S) (krausReducedPairCLM B X) (krausReducedPairCLM B Y) := by
  rw [(hasStrictFDerivAt_fderiv_krausSourceFidelity_source_unrestricted B S hS).hasFDerivAt.fderiv]
  rfl

theorem fderiv_fderiv_krausSourceFidelity_quadratic_nonpos_source_unrestricted
    (B : ι → Matrix n n ℂ) (S X : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) :
    fderiv ℝ (fun A => fderiv ℝ (krausSourceFidelity B) A) S X X ≤ 0 := by
  rw [fderiv_fderiv_krausSourceFidelity_apply_source_unrestricted B S X X hS]
  have hd : (krausReducedDensityCLM B S : Matrix (Fin (Module.finrank ℂ (krausSupport B))) (Fin (Module.finrank ℂ (krausSupport B))) ℂ).PosDef := by
    simpa using krausCompressedDensity_posDef B hS
  have hm : (krausReducedSourceCLM B S : Matrix (Fin (Module.finrank ℂ (krausSupport B))) (Fin (Module.finrank ℂ (krausSupport B))) ℂ).PosDef := by
    simpa using krausCompressedSource_posDef B hS
  exact fderiv_fderiv_doubleFidelity_quadratic_nonpos (krausReducedDensityCLM B S)
    (krausReducedSourceCLM B S) (krausReducedDensityCLM B X) (krausReducedSourceCLM B X) hd hm

theorem contDiffAt_hermitianDensityObjective_source_unrestricted (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ) (θ : ℝ)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef) :
    ContDiffAt ℝ ∞ (hermitianDensityObjective H B θ) S :=
  (((tracePairing H).contDiff.contDiffAt).add
    (contDiffAt_krausSourceFidelity_source_unrestricted B S hS)).add (contDiffAt_tsallisPotential θ S hS)

theorem fderiv_hermitianDensityObjective_eq_source_unrestricted (H : Matrix n n ℂ)
    (B : ι → Matrix n n ℂ) (θ : ℝ) (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) :
    fderiv ℝ (hermitianDensityObjective H B θ) S = tracePairing H +
      fderiv ℝ (krausSourceFidelity B) S + fderiv ℝ (tsallisPotential θ (n := n)) S := by
  have hf := ((contDiffAt_krausSourceFidelity_source_unrestricted B S hS).differentiableAt
    (by simp : (1 : WithTop ℕ∞) ≤ ∞)).hasFDerivAt
  have ht := ((contDiffAt_tsallisPotential θ S hS).differentiableAt
    (by simp : (1 : WithTop ℕ∞) ≤ ∞)).hasFDerivAt
  exact (((tracePairing H).hasFDerivAt.add hf).add ht).fderiv

theorem hasStrictFDerivAt_fderiv_hermitianDensityObjective_source_unrestricted (H : Matrix n n ℂ)
    (B : ι → Matrix n n ℂ) (θ : ℝ) (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) :
    HasStrictFDerivAt (fun A => fderiv ℝ (hermitianDensityObjective H B θ) A)
      (fderiv ℝ (fun A => fderiv ℝ (krausSourceFidelity B) A) S +
        fderiv ℝ (fun A => fderiv ℝ (tsallisPotential θ (n := n)) A) S) S := by
  have hf := hasStrictFDerivAt_fderiv_krausSourceFidelity_source_unrestricted B S hS
  rw [← hf.hasFDerivAt.fderiv] at hf
  have ht := hasStrictFDerivAt_fderiv_tsallisPotential θ S hS
  rw [← ht.hasFDerivAt.fderiv] at ht
  have hc := ((hasStrictFDerivAt_const (𝕜 := ℝ) (tracePairing H) S).add hf).add ht
  simp only [zero_add] at hc
  apply hc.congr_of_eventuallyEq
  filter_upwards [eventually_posDef_of_posDef S hS] with X hX
  exact (fderiv_hermitianDensityObjective_eq_source_unrestricted H B θ X hX).symm

theorem fderiv_fderiv_hermitianDensityObjective_apply_source_unrestricted (H : Matrix n n ℂ)
    (B : ι → Matrix n n ℂ) (θ : ℝ) (S X Y : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) :
    fderiv ℝ (fun A => fderiv ℝ (hermitianDensityObjective H B θ) A) S X Y =
      fderiv ℝ (fun A => fderiv ℝ (krausSourceFidelity B) A) S X Y +
        fderiv ℝ (fun A => fderiv ℝ (tsallisPotential θ (n := n)) A) S X Y := by
  rw [(hasStrictFDerivAt_fderiv_hermitianDensityObjective_source_unrestricted H B θ S hS).hasFDerivAt.fderiv]
  rfl

/-- The actual negative Hessian of the actual density objective is strictly positive in
every nonzero Hermitian direction, with only physical density faithfulness. -/
theorem negativeDensityHessian_quadratic_pos_source_unrestricted (H : Matrix n n ℂ)
    (B : ι → Matrix n n ℂ) (θ : ℝ) (hθ : 0 < θ)
    (S X : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef) (hX : X ≠ 0) :
    0 < -fderiv ℝ (fun A => fderiv ℝ (hermitianDensityObjective H B θ) A) S X X := by
  have hf := fderiv_fderiv_krausSourceFidelity_quadratic_nonpos_source_unrestricted B S X hS
  have ht := negativeTsallisHessian_quadratic_pos θ hθ S X hS hX
  rw [realTrace_mul_comm] at ht
  rw [fderiv_fderiv_hermitianDensityObjective_apply_source_unrestricted H B θ S X X hS,
    fderiv_fderiv_tsallisPotential_apply θ hθ.ne' S X X hS]
  linarith

local instance singularDensityTangentNormedGroup : NormedAddCommGroup (densityTangent (n := n)) :=
  inferInstance
local instance singularDensityTangentNormedSpace : NormedSpace ℝ (densityTangent (n := n)) :=
  inferInstance
local instance singularDensityTangentFiniteDimensional :
    FiniteDimensional ℝ (densityTangent (n := n)) := inferInstance

theorem densityTangentNegativeHessian_pos_source_unrestricted
    (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ) (θ : ℝ) (hθ : 0 < θ)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (X : densityTangent (n := n)) (hX : X ≠ 0) :
    0 < densityTangentNegativeHessian H B θ S X X := by
  have hX' : (X : selfAdjoint (Matrix n n ℂ)) ≠ 0 := fun h => hX (Subtype.ext h)
  exact negativeDensityHessian_quadratic_pos_source_unrestricted H B θ hθ S X hS hX'

/-- The actual trace-zero negative Hessian is invertible even for a singular Kraus source. -/
def densityTangentHessianEquiv_source_unrestricted (H : Matrix n n ℂ)
    (B : ι → Matrix n n ℂ) (θ : ℝ) (hθ : 0 < θ)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef) :
    densityTangent (n := n) ≃L[ℝ] (densityTangent (n := n) →L[ℝ] ℝ) :=
  positiveBilinearEquiv (densityTangentNegativeHessian H B θ S)
    (densityTangentNegativeHessian_pos_source_unrestricted H B θ hθ S hS)

@[simp] theorem densityTangentHessianEquiv_source_unrestricted_apply
    (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ) (θ : ℝ) (hθ : 0 < θ)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (X : densityTangent (n := n)) :
    densityTangentHessianEquiv_source_unrestricted H B θ hθ S hS X =
      densityTangentNegativeHessian H B θ S X := rfl

end
end MatrixSpencer
