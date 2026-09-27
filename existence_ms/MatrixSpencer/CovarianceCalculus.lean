import MatrixSpencer.CovarianceSupport
import MatrixSpencer.OptimizerResponseUnrestricted
import MatrixSpencer.OwnerPotential
import MatrixSpencer.RealCovarianceDomain

/-!
# Calculus of the concrete covariance source

The coefficient covariance enters bilinearly. Source compression uses a fixed
physical embedding, so the joint calculus never differentiates a chosen Kraus
factor or a moving support.
-/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
open Filter Topology

namespace MatrixSpencer
noncomputable section
set_option maxHeartbeats 800000
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n]
local instance covarianceCalculusCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance covarianceCalculusCoeffNormedGroup : NormedAddCommGroup (Matrix ι ι ℝ) := inferInstance
local instance covarianceCalculusCoeffMatrixSpace : NormedSpace ℝ (Matrix ι ι ℝ) := inferInstance
local instance covarianceCalculusPhysicalSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance
local instance covarianceCalculusCoeffSpace : NormedSpace ℝ (selfAdjoint (Matrix ι ι ℝ)) := inferInstance
local instance covarianceCalculusPhysicalFinite : FiniteDimensional ℝ (selfAdjoint (Matrix n n ℂ)) :=
  inferInstanceAs (FiniteDimensional ℝ (selfAdjoint.submodule ℝ (Matrix n n ℂ)))
local instance covarianceCalculusCoeffFinite : FiniteDimensional ℝ (selfAdjoint (Matrix ι ι ℝ)) :=
  inferInstanceAs (FiniteDimensional ℝ (selfAdjoint.submodule ℝ (Matrix ι ι ℝ)))

/-- Inclusion of real symmetric coefficient matrices. -/
def realHermitianInclusion : selfAdjoint (Matrix ι ι ℝ) →L[ℝ] Matrix ι ι ℝ :=
  (selfAdjoint.submodule ℝ (Matrix ι ι ℝ)).subtypeL

/-- The actual covariance source as a continuous bilinear map on full matrix spaces. -/
def covarianceSourceBilinear (A : ι → Matrix n n ℂ) :
    Matrix ι ι ℝ →L[ℝ] (Matrix n n ℂ →L[ℝ] Matrix n n ℂ) :=
  ({ toFun := fun C => ∑ i, ∑ j, C i j • ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℂ) (A i) (A j)
     map_add' := by
       intro C D
       simp only [Matrix.add_apply, add_smul, Finset.sum_add_distrib]
     map_smul' := by
       intro r C
       simp only [Matrix.smul_apply, smul_eq_mul, MulAction.mul_smul, Finset.smul_sum]
       rfl } : Matrix ι ι ℝ →ₗ[ℝ] (Matrix n n ℂ →L[ℝ] Matrix n n ℂ)).toContinuousLinearMap

omit [DecidableEq ι] in
@[simp] theorem covarianceSourceBilinear_apply (A : ι → Matrix n n ℂ)
    (C : Matrix ι ι ℝ) (S : Matrix n n ℂ) : covarianceSourceBilinear A C S = covarianceSource A C S := by
  change (∑ i, ∑ j, C i j • ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℂ) (A i) (A j)) S = _
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.mulLeftRight_apply, covarianceSource]


omit [DecidableEq ι] [DecidableEq n] in
/-- Symmetric coefficients and Hermitian physical inputs give a Hermitian source, without positivity. -/
theorem covarianceSource_isHermitian (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (C : selfAdjoint (Matrix ι ι ℝ)) (S : selfAdjoint (Matrix n n ℂ)) :
    (covarianceSource A (C : Matrix ι ι ℝ) (S : Matrix n n ℂ)).IsHermitian := by
  have hC : ∀ i j, (C : Matrix ι ι ℝ) j i = (C : Matrix ι ι ℝ) i j := by
    intro i j
    have h := congrArg (fun M : Matrix ι ι ℝ => M i j) C.property
    simpa only [star_eq_conjTranspose, Matrix.conjTranspose_apply, star_trivial] using h
  change (covarianceSource A (C : Matrix ι ι ℝ) (S : Matrix n n ℂ))ᴴ = _
  simp only [covarianceSource, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, star_trivial,
    Matrix.conjTranspose_mul, fun i => (hA i).eq,
    show (S : Matrix n n ℂ)ᴴ = S from S.property]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hC]
  simp only [Matrix.mul_assoc]

def hermitianCovarianceSource (A : ι → Matrix n n ℂ)
    (C : selfAdjoint (Matrix ι ι ℝ)) (S : selfAdjoint (Matrix n n ℂ)) :
    selfAdjoint (Matrix n n ℂ) :=
  hermitianProjection (covarianceSource A (C : Matrix ι ι ℝ) (S : Matrix n n ℂ))

omit [DecidableEq ι] in
theorem hermitianCovarianceSource_coe (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (C : selfAdjoint (Matrix ι ι ℝ)) (S : selfAdjoint (Matrix n n ℂ)) :
    (hermitianCovarianceSource A C S : Matrix n n ℂ) = covarianceSource A C S :=
  IsSelfAdjoint.coe_selfAdjointPart_apply ℝ (covarianceSource_isHermitian A hA C S)

theorem contDiff_hermitianCovarianceSource (A : ι → Matrix n n ℂ) :
    ContDiff ℝ ∞ (fun P : selfAdjoint (Matrix ι ι ℝ) × selfAdjoint (Matrix n n ℂ) =>
      hermitianCovarianceSource A P.1 P.2) := by
  have hc : ContDiff ℝ ∞ (fun P : selfAdjoint (Matrix ι ι ℝ) × selfAdjoint (Matrix n n ℂ) =>
      covarianceSourceBilinear A (P.1 : Matrix ι ι ℝ)) :=
    ContDiff.comp (g := (covarianceSourceBilinear A).comp realHermitianInclusion)
      (f := fun P : selfAdjoint (Matrix ι ι ℝ) × selfAdjoint (Matrix n n ℂ) => P.1)
      (ContinuousLinearMap.contDiff _) contDiff_fst
  have hs : ContDiff ℝ ∞ (fun P : selfAdjoint (Matrix ι ι ℝ) × selfAdjoint (Matrix n n ℂ) =>
      (P.2 : Matrix n n ℂ)) := (hermitianInclusion (n := n)).contDiff.comp contDiff_snd
  have h := hermitianProjection.contDiff.comp (hc.clm_apply hs)
  simpa only [Function.comp_def, covarianceSourceBilinear_apply, hermitianCovarianceSource] using h


/-- Covariance variation with the physical density fixed is an actual continuous linear map. -/
def covarianceAtDensity (A : ι → Matrix n n ℂ) (S : selfAdjoint (Matrix n n ℂ)) :
    selfAdjoint (Matrix ι ι ℝ) →L[ℝ] selfAdjoint (Matrix n n ℂ) :=
  hermitianProjection.comp (((covarianceSourceBilinear A).flip (S : Matrix n n ℂ)).comp realHermitianInclusion)

@[simp] theorem covarianceAtDensity_apply (A : ι → Matrix n n ℂ)
    (S : selfAdjoint (Matrix n n ℂ)) (C : selfAdjoint (Matrix ι ι ℝ)) :
    covarianceAtDensity A S C = hermitianCovarianceSource A C S := by
  apply Subtype.ext
  simp only [covarianceAtDensity, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    covarianceSourceBilinear_apply]
  rfl

/-- The actual fixed-support reduced pair, polynomial in covariance and density. -/
def covarianceReducedPair (A : ι → Matrix n n ℂ)
    (P : selfAdjoint (Matrix ι ι ℝ) × selfAdjoint (Matrix n n ℂ)) :=
  (krausReducedDensityCLM A P.2,
    hermitianRectangularCompressionCLM (krausSupportEmbedding A) (hermitianCovarianceSource A P.1 P.2))

omit [DecidableEq ι] in
theorem covarianceReducedPair_snd_coe (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (C : selfAdjoint (Matrix ι ι ℝ)) (S : selfAdjoint (Matrix n n ℂ)) :
    ((covarianceReducedPair A (C, S)).2 : Matrix _ _ ℂ) = covarianceCompressedSource A C S := by
  simp only [covarianceReducedPair, hermitianRectangularCompressionCLM_coe,
    hermitianCovarianceSource_coe A hA]
  rfl

theorem contDiff_covarianceReducedPair (A : ι → Matrix n n ℂ) :
    ContDiff ℝ ∞ (covarianceReducedPair A) :=
  ((krausReducedDensityCLM A).contDiff.comp contDiff_snd).prodMk
    ((hermitianRectangularCompressionCLM (krausSupportEmbedding A)).contDiff.comp
      (contDiff_hermitianCovarianceSource A))

def covarianceFidelity (A : ι → Matrix n n ℂ)
    (P : selfAdjoint (Matrix ι ι ℝ) × selfAdjoint (Matrix n n ℂ)) : ℝ :=
  2 * fidelity (P.2 : Matrix n n ℂ) (covarianceSource A (P.1 : Matrix ι ι ℝ) (P.2 : Matrix n n ℂ))

def reducedCovarianceFidelity (A : ι → Matrix n n ℂ)
    (P : selfAdjoint (Matrix ι ι ℝ) × selfAdjoint (Matrix n n ℂ)) : ℝ :=
  doubleFidelity (covarianceReducedPair A P)

theorem covarianceFidelity_eq_reduced (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (C : selfAdjoint (Matrix ι ι ℝ)) (S : selfAdjoint (Matrix n n ℂ))
    (hC : (C : Matrix ι ι ℝ).PosDef) (hS : (S : Matrix n n ℂ).PosDef) :
    covarianceFidelity A (C, S) = reducedCovarianceFidelity A (C, S) := by
  change 2 * fidelity (S : Matrix n n ℂ) (covarianceSource A C S) =
    2 * fidelity (krausCompressedDensity A S) ((covarianceReducedPair A (C, S)).2 : Matrix _ _ ℂ)
  rw [covarianceReducedPair_snd_coe A hA,
    fidelity_covariance_support_compression A hA hC hS]

theorem contDiffAt_reducedCovarianceFidelity (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (C : selfAdjoint (Matrix ι ι ℝ)) (S : selfAdjoint (Matrix n n ℂ))
    (hC : (C : Matrix ι ι ℝ).PosDef) (hS : (S : Matrix n n ℂ).PosDef) :
    ContDiffAt ℝ ∞ (reducedCovarianceFidelity A) (C, S) := by
  have hp : ((covarianceReducedPair A (C, S)).1 :
      Matrix (Fin (Module.finrank ℂ (krausSupport A))) (Fin (Module.finrank ℂ (krausSupport A))) ℂ).PosDef :=
    krausCompressedDensity_posDef A hS
  have hm : ((covarianceReducedPair A (C, S)).2 :
      Matrix (Fin (Module.finrank ℂ (krausSupport A))) (Fin (Module.finrank ℂ (krausSupport A))) ℂ).PosDef := by
    rw [covarianceReducedPair_snd_coe A hA]
    exact covarianceCompressedSource_posDef A hA hC hS
  exact (contDiffAt_doubleFidelity _ _ hp hm).comp (C, S)
    (contDiff_covarianceReducedPair A).contDiffAt

/-- Joint smoothness of the actual fidelity source term, with physical source rank unrestricted. -/
theorem contDiffAt_covarianceFidelity (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (C : selfAdjoint (Matrix ι ι ℝ)) (S : selfAdjoint (Matrix n n ℂ))
    (hC : (C : Matrix ι ι ℝ).PosDef) (hS : (S : Matrix n n ℂ).PosDef) :
    ContDiffAt ℝ ∞ (covarianceFidelity A) (C, S) := by
  apply (contDiffAt_reducedCovarianceFidelity A hA C S hC hS).congr_of_eventuallyEq
  filter_upwards [(continuous_fst.continuousAt (x := (C, S))).eventually
    (eventually_real_posDef_of_posDef C hC),
    (continuous_snd.continuousAt (x := (C, S))).eventually
      (eventually_posDef_of_posDef S hS)] with P hPC hPS
  exact covarianceFidelity_eq_reduced A hA P.1 P.2 hPC hPS

/-- The original objective in joint real covariance and Hermitian density coordinates. -/
def jointOwnerObjective (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ) (θ : ℝ)
    (P : selfAdjoint (Matrix ι ι ℝ) × selfAdjoint (Matrix n n ℂ)) : ℝ :=
  ownerObjective H A P.1 θ P.2

theorem contDiffAt_jointOwnerObjective (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (θ : ℝ)
    (C : selfAdjoint (Matrix ι ι ℝ)) (S : selfAdjoint (Matrix n n ℂ))
    (hC : (C : Matrix ι ι ℝ).PosDef) (hS : (S : Matrix n n ℂ).PosDef) :
    ContDiffAt ℝ ∞ (jointOwnerObjective H A θ) (C, S) := by
  have ht : ContDiffAt ℝ ∞ (fun P : selfAdjoint (Matrix ι ι ℝ) × selfAdjoint (Matrix n n ℂ) =>
      tsallisPotential θ P.2) (C, S) :=
    ContDiffAt.comp (g := tsallisPotential θ) (f := Prod.snd) (C, S)
      (contDiffAt_tsallisPotential θ S hS) contDiffAt_snd
  have hl : ContDiffAt ℝ ∞ (fun P : selfAdjoint (Matrix ι ι ℝ) × selfAdjoint (Matrix n n ℂ) =>
      tracePairing H P.2) (C, S) :=
    (tracePairing H).contDiff.contDiffAt.comp (C, S) contDiffAt_snd
  exact (hl.add (contDiffAt_covarianceFidelity A hA C S hC hS)).add ht

/-- Covariance variation after compression to the fixed physical source support. -/
def compressedCovarianceAtDensity (A : ι → Matrix n n ℂ) (S : selfAdjoint (Matrix n n ℂ)) :=
  (hermitianRectangularCompressionCLM (krausSupportEmbedding A)).comp (covarianceAtDensity A S)

@[simp] theorem compressedCovarianceAtDensity_coe (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (S : selfAdjoint (Matrix n n ℂ))
    (C : selfAdjoint (Matrix ι ι ℝ)) :
    (compressedCovarianceAtDensity A S C : Matrix _ _ ℂ) = covarianceCompressedSource A C S := by
  simp only [compressedCovarianceAtDensity, ContinuousLinearMap.comp_apply,
    covarianceAtDensity_apply, hermitianRectangularCompressionCLM_coe,
    hermitianCovarianceSource_coe A hA]
  rfl

/-- The transport on the fixed support, extended by zero to the physical space. -/
def covarianceSupportTransport (A : ι → Matrix n n ℂ)
    (C : selfAdjoint (Matrix ι ι ℝ)) (S : selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ :=
  krausSupportEmbedding A *
    transportOptimizer (krausCompressedDensity A S) (covarianceCompressedSource A C S) *
    (krausSupportEmbedding A)ᴴ

/-- The concrete covariance differential, packaged as a continuous linear functional. -/
def covarianceDerivativeFunctional (A : ι → Matrix n n ℂ)
    (C : selfAdjoint (Matrix ι ι ℝ)) (S : selfAdjoint (Matrix n n ℂ)) :
    selfAdjoint (Matrix ι ι ℝ) →L[ℝ] ℝ :=
  (tracePairing (transportOptimizer (krausCompressedDensity A S)
    (covarianceCompressedSource A C S))).comp (compressedCovarianceAtDensity A S)

theorem covarianceDerivativeFunctional_apply (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (C ΔC : selfAdjoint (Matrix ι ι ℝ))
    (S : selfAdjoint (Matrix n n ℂ)) :
    covarianceDerivativeFunctional A C S ΔC =
      realTrace (covarianceSupportTransport A C S * covarianceSource A ΔC S) := by
  change realTrace (transportOptimizer (krausCompressedDensity A S) (covarianceCompressedSource A C S) *
    (compressedCovarianceAtDensity A S ΔC : Matrix (Fin (Module.finrank ℂ (krausSupport A)))
      (Fin (Module.finrank ℂ (krausSupport A))) ℂ)) = _
  rw [compressedCovarianceAtDensity_coe A hA]
  unfold covarianceSupportTransport covarianceCompressedSource
  simp only [Matrix.mul_assoc]
  rw [realTrace_rectangular_mul_comm (krausSupportEmbedding A)]
  simp only [Matrix.mul_assoc]

/-- Partial differentiation in covariance of the reduced, actual fidelity formula. -/
theorem hasStrictFDerivAt_reducedCovarianceFidelity_covariance
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (C : selfAdjoint (Matrix ι ι ℝ)) (S : selfAdjoint (Matrix n n ℂ))
    (hC : (C : Matrix ι ι ℝ).PosDef) (hS : (S : Matrix n n ℂ).PosDef) :
    HasStrictFDerivAt (fun K => reducedCovarianceFidelity A (K, S))
      (covarianceDerivativeFunctional A C S) C := by
  let Q := krausReducedDensityCLM A S
  let L := compressedCovarianceAtDensity A S
  have hQ : (Q : Matrix (Fin (Module.finrank ℂ (krausSupport A)))
      (Fin (Module.finrank ℂ (krausSupport A))) ℂ).PosDef := krausCompressedDensity_posDef A hS
  have hL : (L C : Matrix (Fin (Module.finrank ℂ (krausSupport A)))
      (Fin (Module.finrank ℂ (krausSupport A))) ℂ).PosDef := by
    rw [show (L C : Matrix _ _ ℂ) = covarianceCompressedSource A C S from
      compressedCovarianceAtDensity_coe A hA S C]
    exact covarianceCompressedSource_posDef A hA hC hS
  have hf := (hasStrictFDerivAt_doubleFidelity Q (L C) hQ hL).comp C
    ((hasStrictFDerivAt_const (𝕜 := ℝ) Q C).prodMk L.hasStrictFDerivAt)
  have he : (jointTransportFunctional (transportOptimizer (Q : Matrix _ _ ℂ) (L C))).comp
      ((0 : selfAdjoint (Matrix ι ι ℝ) →L[ℝ] _).prod L) =
      covarianceDerivativeFunctional A C S := by
    ext ΔC
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.zero_apply, jointTransportFunctional_apply, ZeroMemClass.coe_zero,
      Matrix.mul_zero, realTrace_zero, zero_add]
    change realTrace (transportOptimizer (krausCompressedDensity A S) (L C) * (L ΔC : Matrix _ _ ℂ)) = _
    rw [show (L C : Matrix _ _ ℂ) = covarianceCompressedSource A C S from
      compressedCovarianceAtDensity_coe A hA S C]
    rfl
  rw [he] at hf
  have hefun : (fun K => reducedCovarianceFidelity A (K, S)) =
      (fun K => doubleFidelity (Q, L K)) := by
    funext K
    apply congrArg doubleFidelity
    exact Prod.ext rfl (by simp only [covarianceReducedPair, L,
      compressedCovarianceAtDensity, ContinuousLinearMap.comp_apply, covarianceAtDensity_apply])
  rw [hefun]
  exact hf

/-- The physical source may be singular: the actual covariance derivative is still the
fixed-support transport trace, with no differentiability assumption on an optimizer. -/
theorem hasStrictFDerivAt_covarianceFidelity_covariance
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (C : selfAdjoint (Matrix ι ι ℝ)) (S : selfAdjoint (Matrix n n ℂ))
    (hC : (C : Matrix ι ι ℝ).PosDef) (hS : (S : Matrix n n ℂ).PosDef) :
    HasStrictFDerivAt (fun K => covarianceFidelity A (K, S))
      (covarianceDerivativeFunctional A C S) C := by
  apply (hasStrictFDerivAt_reducedCovarianceFidelity_covariance A hA C S hC hS).congr_of_eventuallyEq
  filter_upwards [eventually_real_posDef_of_posDef C hC] with K hK
  exact (covarianceFidelity_eq_reduced A hA K S hK hS).symm

theorem hasStrictFDerivAt_ownerObjective_covariance
    (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) (θ : ℝ)
    (C : selfAdjoint (Matrix ι ι ℝ)) (S : selfAdjoint (Matrix n n ℂ))
    (hC : (C : Matrix ι ι ℝ).PosDef) (hS : (S : Matrix n n ℂ).PosDef) :
    HasStrictFDerivAt (fun K : selfAdjoint (Matrix ι ι ℝ) => ownerObjective H A K θ S)
      (covarianceDerivativeFunctional A C S) C := by
  have hf := ((hasStrictFDerivAt_const (𝕜 := ℝ) (realTrace (H * (S : Matrix n n ℂ))) C).add
    (hasStrictFDerivAt_covarianceFidelity_covariance A hA C S hC hS)).add
    (hasStrictFDerivAt_const (𝕜 := ℝ) (tsallisPotential θ S) C)
  simpa only [zero_add, add_zero] using hf

theorem fderiv_ownerObjective_covariance_apply
    (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) (θ : ℝ)
    (C ΔC : selfAdjoint (Matrix ι ι ℝ)) (S : selfAdjoint (Matrix n n ℂ))
    (hC : (C : Matrix ι ι ℝ).PosDef) (hS : (S : Matrix n n ℂ).PosDef) :
    fderiv ℝ (fun K : selfAdjoint (Matrix ι ι ℝ) => ownerObjective H A K θ S) C ΔC =
      realTrace (covarianceSupportTransport A C S * covarianceSource A ΔC S) := by
  rw [(hasStrictFDerivAt_ownerObjective_covariance H A hA θ C S hC hS).hasFDerivAt.fderiv]
  exact covarianceDerivativeFunctional_apply A hA C ΔC S

end
end MatrixSpencer
