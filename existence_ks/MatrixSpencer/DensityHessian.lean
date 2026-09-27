import MatrixSpencer.DensityPotential
import MatrixSpencer.FidelityHessian
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The actual density-objective Hessian

The source is the concrete Kraus channel from `densityObjective`. All local
derivative statements explicitly require a positive definite density and source.
-/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
open Filter Topology

namespace MatrixSpencer

noncomputable section

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]

local instance densityHessianCStarAlgebra : CStarAlgebra (Matrix n n ℂ) := {}
local instance densityHessianNormedSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) :=
  inferInstance
local instance densityHessianFiniteDimensional :
    FiniteDimensional ℝ (selfAdjoint (Matrix n n ℂ)) :=
  inferInstanceAs (FiniteDimensional ℝ (selfAdjoint.submodule ℝ (Matrix n n ℂ)))

def hermitianKrausChannel (B : ι → Matrix n n ℂ) :
    selfAdjoint (Matrix n n ℂ) →L[ℝ] selfAdjoint (Matrix n n ℂ) :=
  ({ toFun := fun X => ⟨krausChannel B X, by
       change (krausChannel B (X : Matrix n n ℂ))ᴴ = _
       simp only [krausChannel, Matrix.conjTranspose_sum, Matrix.conjTranspose_mul,
         Matrix.conjTranspose_conjTranspose,
         show (X : Matrix n n ℂ)ᴴ = X from X.property, Matrix.mul_assoc]⟩
     map_add' := by
       intro X Y
       apply Subtype.ext
       change krausChannel B ((X : Matrix n n ℂ) + Y) = _
       simp only [krausChannel, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]
       rfl
     map_smul' := by
       intro r X
       apply Subtype.ext
       change krausChannel B (r • (X : Matrix n n ℂ)) = _
       simp only [krausChannel, Matrix.mul_smul, Matrix.smul_mul]
       change (∑ a, r • (B a * (X : Matrix n n ℂ) * (B a)ᴴ)) =
         r • ∑ a, B a * (X : Matrix n n ℂ) * (B a)ᴴ
       rw [Finset.smul_sum] } : selfAdjoint (Matrix n n ℂ) →ₗ[ℝ]
       selfAdjoint (Matrix n n ℂ)).toContinuousLinearMap

@[simp] theorem hermitianKrausChannel_coe (B : ι → Matrix n n ℂ)
    (S : selfAdjoint (Matrix n n ℂ)) :
    (hermitianKrausChannel B S : Matrix n n ℂ) = krausChannel B (S : Matrix n n ℂ) := rfl

def krausSourceJoint (B : ι → Matrix n n ℂ) :
    selfAdjoint (Matrix n n ℂ) →L[ℝ]
      (selfAdjoint (Matrix n n ℂ) × selfAdjoint (Matrix n n ℂ)) :=
  (ContinuousLinearMap.id ℝ _).prod (hermitianKrausChannel B)

def krausSourceFidelity (B : ι → Matrix n n ℂ) (S : selfAdjoint (Matrix n n ℂ)) : ℝ :=
  doubleFidelity (krausSourceJoint B S)

def krausDualPullback (B : ι → Matrix n n ℂ) :
    ((selfAdjoint (Matrix n n ℂ) × selfAdjoint (Matrix n n ℂ)) →L[ℝ] ℝ) →L[ℝ]
      (selfAdjoint (Matrix n n ℂ) →L[ℝ] ℝ) :=
  (ContinuousLinearMap.compL ℝ (selfAdjoint (Matrix n n ℂ))
    (selfAdjoint (Matrix n n ℂ) × selfAdjoint (Matrix n n ℂ)) ℝ).flip (krausSourceJoint B)

theorem eventually_posDef_krausSource (B : ι → Matrix n n ℂ)
    (S : selfAdjoint (Matrix n n ℂ))
    (hM : (krausChannel B (S : Matrix n n ℂ)).PosDef) :
    ∀ᶠ X : selfAdjoint (Matrix n n ℂ) in 𝓝 S,
      (krausChannel B (X : Matrix n n ℂ)).PosDef :=
  (hermitianKrausChannel B).continuous.continuousAt.eventually
    (eventually_posDef_of_posDef (hermitianKrausChannel B S) hM)

theorem contDiffAt_krausSourceFidelity (B : ι → Matrix n n ℂ)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (hM : (krausChannel B (S : Matrix n n ℂ)).PosDef) :
    ContDiffAt ℝ ∞ (krausSourceFidelity B) S :=
  (contDiffAt_doubleFidelity S (hermitianKrausChannel B S) hS hM).comp S
    (krausSourceJoint B).contDiff.contDiffAt

theorem hasFDerivAt_krausSourceFidelity (B : ι → Matrix n n ℂ)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (hM : (krausChannel B (S : Matrix n n ℂ)).PosDef) :
    HasFDerivAt (krausSourceFidelity B)
      ((fderiv ℝ (doubleFidelity (n := n)) (krausSourceJoint B S)).comp (krausSourceJoint B)) S :=
  ((contDiffAt_doubleFidelity S (hermitianKrausChannel B S) hS hM).differentiableAt
    (by simp : (1 : WithTop ℕ∞) ≤ ∞)).hasFDerivAt.comp S (krausSourceJoint B).hasFDerivAt

theorem hasStrictFDerivAt_fderiv_krausSourceFidelity (B : ι → Matrix n n ℂ)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (hM : (krausChannel B (S : Matrix n n ℂ)).PosDef) :
    HasStrictFDerivAt (fun X => fderiv ℝ (krausSourceFidelity B) X)
      ((krausDualPullback B).comp
        ((fderiv ℝ (fun P => fderiv ℝ (doubleFidelity (n := n)) P)
          (krausSourceJoint B S)).comp (krausSourceJoint B))) S := by
  have hd := hasStrictFDerivAt_fderiv_doubleFidelity S (hermitianKrausChannel B S) hS hM
  rw [← hd.hasFDerivAt.fderiv] at hd
  have hp := (krausDualPullback B).hasStrictFDerivAt.comp S
    (hd.comp S (krausSourceJoint B).hasStrictFDerivAt)
  apply hp.congr_of_eventuallyEq
  filter_upwards [eventually_posDef_of_posDef S hS,
    eventually_posDef_krausSource B S hM] with X hX hMX
  exact (hasFDerivAt_krausSourceFidelity B X hX hMX).fderiv.symm

theorem fderiv_fderiv_krausSourceFidelity_apply (B : ι → Matrix n n ℂ)
    (S X Y : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (hM : (krausChannel B (S : Matrix n n ℂ)).PosDef) :
    fderiv ℝ (fun A => fderiv ℝ (krausSourceFidelity B) A) S X Y =
      fderiv ℝ (fun P => fderiv ℝ (doubleFidelity (n := n)) P)
        (krausSourceJoint B S) (krausSourceJoint B X) (krausSourceJoint B Y) := by
  rw [(hasStrictFDerivAt_fderiv_krausSourceFidelity B S hS hM).hasFDerivAt.fderiv]
  rfl

theorem fderiv_fderiv_krausSourceFidelity_quadratic_nonpos (B : ι → Matrix n n ℂ)
    (S X : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (hM : (krausChannel B (S : Matrix n n ℂ)).PosDef) :
    fderiv ℝ (fun A => fderiv ℝ (krausSourceFidelity B) A) S X X ≤ 0 := by
  rw [fderiv_fderiv_krausSourceFidelity_apply B S X X hS hM]
  exact fderiv_fderiv_doubleFidelity_quadratic_nonpos S (hermitianKrausChannel B S)
    X (hermitianKrausChannel B X) hS hM

/-- The actual root objective, with only its domain restricted to Hermitian matrices. -/
def hermitianDensityObjective (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ) (θ : ℝ)
    (S : selfAdjoint (Matrix n n ℂ)) : ℝ := densityObjective H B θ (S : Matrix n n ℂ)

theorem hermitianDensityObjective_eq (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ) (θ : ℝ)
    (S : selfAdjoint (Matrix n n ℂ)) :
    hermitianDensityObjective H B θ S =
      tracePairing H S + krausSourceFidelity B S + tsallisPotential θ S := rfl

theorem contDiffAt_hermitianDensityObjective (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ) (θ : ℝ)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (hM : (krausChannel B (S : Matrix n n ℂ)).PosDef) :
    ContDiffAt ℝ ∞ (hermitianDensityObjective H B θ) S :=
  (((tracePairing H).contDiff.contDiffAt).add
    (contDiffAt_krausSourceFidelity B S hS hM)).add (contDiffAt_tsallisPotential θ S hS)

theorem fderiv_hermitianDensityObjective_eq (H : Matrix n n ℂ)
    (B : ι → Matrix n n ℂ) (θ : ℝ) (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef)
    (hM : (krausChannel B (S : Matrix n n ℂ)).PosDef) :
    fderiv ℝ (hermitianDensityObjective H B θ) S = tracePairing H +
      fderiv ℝ (krausSourceFidelity B) S + fderiv ℝ (tsallisPotential θ (n := n)) S := by
  have hf := ((contDiffAt_krausSourceFidelity B S hS hM).differentiableAt
    (by simp : (1 : WithTop ℕ∞) ≤ ∞)).hasFDerivAt
  have ht := ((contDiffAt_tsallisPotential θ S hS).differentiableAt
    (by simp : (1 : WithTop ℕ∞) ≤ ∞)).hasFDerivAt
  exact (((tracePairing H).hasFDerivAt.add hf).add ht).fderiv

theorem hasStrictFDerivAt_fderiv_hermitianDensityObjective (H : Matrix n n ℂ)
    (B : ι → Matrix n n ℂ) (θ : ℝ) (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef)
    (hM : (krausChannel B (S : Matrix n n ℂ)).PosDef) :
    HasStrictFDerivAt (fun A => fderiv ℝ (hermitianDensityObjective H B θ) A)
      (fderiv ℝ (fun A => fderiv ℝ (krausSourceFidelity B) A) S +
        fderiv ℝ (fun A => fderiv ℝ (tsallisPotential θ (n := n)) A) S) S := by
  have hf := hasStrictFDerivAt_fderiv_krausSourceFidelity B S hS hM
  rw [← hf.hasFDerivAt.fderiv] at hf
  have ht := hasStrictFDerivAt_fderiv_tsallisPotential θ S hS
  rw [← ht.hasFDerivAt.fderiv] at ht
  have hc := ((hasStrictFDerivAt_const (𝕜 := ℝ) (tracePairing H) S).add hf).add ht
  simp only [zero_add] at hc
  apply hc.congr_of_eventuallyEq
  filter_upwards [eventually_posDef_of_posDef S hS,
    eventually_posDef_krausSource B S hM] with X hX hMX
  exact (fderiv_hermitianDensityObjective_eq H B θ X hX hMX).symm

theorem fderiv_fderiv_hermitianDensityObjective_apply (H : Matrix n n ℂ)
    (B : ι → Matrix n n ℂ) (θ : ℝ) (S X Y : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef)
    (hM : (krausChannel B (S : Matrix n n ℂ)).PosDef) :
    fderiv ℝ (fun A => fderiv ℝ (hermitianDensityObjective H B θ) A) S X Y =
      fderiv ℝ (fun A => fderiv ℝ (krausSourceFidelity B) A) S X Y +
        fderiv ℝ (fun A => fderiv ℝ (tsallisPotential θ (n := n)) A) S X Y := by
  rw [(hasStrictFDerivAt_fderiv_hermitianDensityObjective H B θ S hS hM).hasFDerivAt.fderiv]
  rfl

/-- The actual negative Hessian of the actual density objective is strictly positive in
every nonzero Hermitian direction, under the explicit faithful local hypotheses. -/
theorem negativeDensityHessian_quadratic_pos (H : Matrix n n ℂ)
    (B : ι → Matrix n n ℂ) (θ : ℝ) (hθ : 0 < θ)
    (S X : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (hM : (krausChannel B (S : Matrix n n ℂ)).PosDef) (hX : X ≠ 0) :
    0 < -fderiv ℝ (fun A => fderiv ℝ (hermitianDensityObjective H B θ) A) S X X := by
  have hf := fderiv_fderiv_krausSourceFidelity_quadratic_nonpos B S X hS hM
  have ht := negativeTsallisHessian_quadratic_pos θ hθ S X hS hX
  rw [realTrace_mul_comm] at ht
  rw [fderiv_fderiv_hermitianDensityObjective_apply H B θ S X X hS hM,
    fderiv_fderiv_tsallisPotential_apply θ hθ.ne' S X X hS]
  linarith

section PositiveBilinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem positiveBilinear_injective (A : E →L[ℝ] (E →L[ℝ] ℝ))
    (hA : ∀ X : E, X ≠ 0 → 0 < A X X) : Function.Injective A := by
  intro X Y hXY
  by_contra hne
  have hp := hA (X - Y) (sub_ne_zero.mpr hne)
  have hz : A (X - Y) = 0 := by rw [map_sub, hXY, sub_self]
  rw [hz, ContinuousLinearMap.zero_apply] at hp
  exact (lt_irrefl 0) hp

/-- Strictly positive finite-dimensional bilinear forms are actual isomorphisms to the dual. -/
def positiveBilinearEquiv (A : E →L[ℝ] (E →L[ℝ] ℝ))
    (hA : ∀ X : E, X ≠ 0 → 0 < A X X) : E ≃L[ℝ] (E →L[ℝ] ℝ) := by
  have hdim : Module.finrank ℝ E = Module.finrank ℝ (E →L[ℝ] ℝ) := by
    calc
      _ = Module.finrank ℝ (E →ₗ[ℝ] ℝ) := (Subspace.dual_finrank_eq (K := ℝ) (V := E)).symm
      _ = _ := (LinearMap.toContinuousLinearMap :
        (E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (E →L[ℝ] ℝ)).finrank_eq
  exact (A.toLinearMap.linearEquivOfInjective (positiveBilinear_injective A hA) hdim).toContinuousLinearEquiv

@[simp] theorem positiveBilinearEquiv_apply (A : E →L[ℝ] (E →L[ℝ] ℝ))
    (hA : ∀ X : E, X ≠ 0 → 0 < A X X) (X : E) : positiveBilinearEquiv A hA X = A X := rfl

end PositiveBilinear

/-- The tangent space of the trace-one affine constraint. -/
def densityTangent : Submodule ℝ (selfAdjoint (Matrix n n ℂ)) :=
  LinearMap.ker ((realTraceCLM.comp (hermitianInclusion (n := n))).toLinearMap)

local instance densityHessianTangentNormedGroup : NormedAddCommGroup (densityTangent (n := n)) :=
  inferInstance
local instance densityHessianTangentNormedSpace : NormedSpace ℝ (densityTangent (n := n)) :=
  inferInstance
local instance densityHessianTangentFiniteDimensional :
    FiniteDimensional ℝ (densityTangent (n := n)) := inferInstance

theorem mem_densityTangent_iff (X : selfAdjoint (Matrix n n ℂ)) :
    X ∈ densityTangent ↔ realTrace (X : Matrix n n ℂ) = 0 := Iff.rfl

def densityNegativeHessian (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ) (θ : ℝ)
    (S : selfAdjoint (Matrix n n ℂ)) :
    selfAdjoint (Matrix n n ℂ) →L[ℝ] (selfAdjoint (Matrix n n ℂ) →L[ℝ] ℝ) :=
  -fderiv ℝ (fun A => fderiv ℝ (hermitianDensityObjective H B θ) A) S

def densityTangentNegativeHessian (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ) (θ : ℝ)
    (S : selfAdjoint (Matrix n n ℂ)) :
    densityTangent (n := n) →L[ℝ] (densityTangent (n := n) →L[ℝ] ℝ) :=
  ((ContinuousLinearMap.compL ℝ (densityTangent (n := n))
      (selfAdjoint (Matrix n n ℂ)) ℝ).flip (densityTangent (n := n)).subtypeL).comp
    ((densityNegativeHessian H B θ S).comp (densityTangent (n := n)).subtypeL)

theorem densityTangentNegativeHessian_pos (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (θ : ℝ) (hθ : 0 < θ) (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) (hM : (krausChannel B (S : Matrix n n ℂ)).PosDef)
    (X : densityTangent (n := n)) (hX : X ≠ 0) :
    0 < densityTangentNegativeHessian H B θ S X X := by
  have hX' : (X : selfAdjoint (Matrix n n ℂ)) ≠ 0 := fun h => hX (Subtype.ext h)
  exact negativeDensityHessian_quadratic_pos H B θ hθ S X hS hM hX'

/-- The actual trace-zero constrained negative Hessian, invertible as a map to its dual. -/
def densityTangentHessianEquiv (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (θ : ℝ) (hθ : 0 < θ) (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) (hM : (krausChannel B (S : Matrix n n ℂ)).PosDef) :
    densityTangent (n := n) ≃L[ℝ] (densityTangent (n := n) →L[ℝ] ℝ) :=
  positiveBilinearEquiv (densityTangentNegativeHessian H B θ S)
    (densityTangentNegativeHessian_pos H B θ hθ S hS hM)

def densityTangentTracePairing :
    densityTangent (n := n) →L[ℝ] (densityTangent (n := n) →L[ℝ] ℝ) :=
  ((ContinuousLinearMap.compL ℝ (densityTangent (n := n))
      (selfAdjoint (Matrix n n ℂ)) ℝ).flip (densityTangent (n := n)).subtypeL).comp
    ((tracePairing.comp hermitianInclusion).comp (densityTangent (n := n)).subtypeL)

theorem densityTangentTracePairing_pos (X : densityTangent (n := n)) (hX : X ≠ 0) :
    0 < densityTangentTracePairing X X := by
  let A : Matrix n n ℂ := (X : selfAdjoint (Matrix n n ℂ))
  have hA : A ≠ 0 := fun h => hX (Subtype.ext (Subtype.ext h))
  have hn := realTrace_conjTranspose_mul_self_nonneg A
  have hz : realTrace (Aᴴ * A) ≠ 0 :=
    mt (realTrace_conjTranspose_mul_self_eq_zero_iff A).mp hA
  have hp := lt_of_le_of_ne hn (Ne.symm hz)
  have hs : Aᴴ = A := (X : selfAdjoint (Matrix n n ℂ)).property
  rw [hs] at hp
  exact hp

/-- Real trace Riesz identification on the trace-zero Hermitian tangent. -/
def densityTangentTraceEquiv :
    densityTangent (n := n) ≃L[ℝ] (densityTangent (n := n) →L[ℝ] ℝ) :=
  positiveBilinearEquiv densityTangentTracePairing densityTangentTracePairing_pos

/-- The actual constrained negative Hessian as an invertible endomorphism in real trace geometry. -/
def densityTangentHessianEndomorphism (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (θ : ℝ) (hθ : 0 < θ) (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) (hM : (krausChannel B (S : Matrix n n ℂ)).PosDef) :
    densityTangent (n := n) ≃L[ℝ] densityTangent (n := n) :=
  (densityTangentHessianEquiv H B θ hθ S hS hM).trans densityTangentTraceEquiv.symm

theorem densityTangentHessianEndomorphism_represents (H : Matrix n n ℂ)
    (B : ι → Matrix n n ℂ) (θ : ℝ) (hθ : 0 < θ) (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) (hM : (krausChannel B (S : Matrix n n ℂ)).PosDef)
    (X Y : densityTangent (n := n)) :
    densityTangentTracePairing (densityTangentHessianEndomorphism H B θ hθ S hS hM X) Y =
      densityTangentNegativeHessian H B θ S X Y := by
  change densityTangentTraceEquiv
    (densityTangentTraceEquiv.symm (densityTangentHessianEquiv H B θ hθ S hS hM X)) Y = _
  rw [ContinuousLinearEquiv.apply_symm_apply]
  rfl

end

end MatrixSpencer
