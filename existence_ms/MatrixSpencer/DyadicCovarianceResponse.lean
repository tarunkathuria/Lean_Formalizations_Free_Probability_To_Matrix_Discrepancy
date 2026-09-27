import MatrixSpencer.DyadicCovarianceCalculus
import MatrixSpencer.CovarianceResponse

/-!
# Covariance response of the actual optimized potential

The covariance is positive definite in its fixed coefficient face. The physical
source may be singular. A parameter inverse-function theorem uses the actual
constrained density Hessian and identifies its branch by global strict concavity.
-/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
open Filter Topology

namespace MatrixSpencer
namespace DyadicCovarianceResponse
noncomputable section
set_option maxHeartbeats 800000
set_option linter.unusedVariables false
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n]
local instance dyadicCovarianceResponseCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance dyadicCovarianceResponsePhysicalGroup : NormedAddCommGroup (selfAdjoint (Matrix n n ℂ)) := inferInstance
local instance dyadicCovarianceResponseCoeffGroup : NormedAddCommGroup (selfAdjoint (Matrix ι ι ℝ)) := inferInstance
local instance dyadicCovarianceResponsePhysicalSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance
local instance dyadicCovarianceResponseCoeffSpace : NormedSpace ℝ (selfAdjoint (Matrix ι ι ℝ)) := inferInstance
local instance dyadicCovarianceResponsePhysicalFinite : FiniteDimensional ℝ (selfAdjoint (Matrix n n ℂ)) :=
  inferInstanceAs (FiniteDimensional ℝ (selfAdjoint.submodule ℝ (Matrix n n ℂ)))
local instance dyadicCovarianceResponseCoeffFinite : FiniteDimensional ℝ (selfAdjoint (Matrix ι ι ℝ)) :=
  inferInstanceAs (FiniteDimensional ℝ (selfAdjoint.submodule ℝ (Matrix ι ι ℝ)))
local instance dyadicCovarianceResponseCoeffComplete : CompleteSpace (selfAdjoint (Matrix ι ι ℝ)) :=
  FiniteDimensional.complete ℝ _
local instance dyadicCovarianceResponseTangentGroup : NormedAddCommGroup (densityTangent (n := n)) := inferInstance
local instance dyadicCovarianceResponseTangentSpace : NormedSpace ℝ (densityTangent (n := n)) := inferInstance
local instance dyadicCovarianceResponseTangentFinite : FiniteDimensional ℝ (densityTangent (n := n)) := inferInstance
local instance dyadicCovarianceResponseTangentComplete : CompleteSpace (densityTangent (n := n)) :=
  FiniteDimensional.complete ℝ _
local instance dyadicCovarianceResponseDualGroup : NormedAddCommGroup (densityTangent (n := n) →L[ℝ] ℝ) := inferInstance
local instance dyadicCovarianceResponseDualSpace : NormedSpace ℝ (densityTangent (n := n) →L[ℝ] ℝ) := inferInstance

local instance dyadicCovarianceResponseJointGroup : NormedAddCommGroup
    (selfAdjoint (Matrix ι ι ℝ) × selfAdjoint (Matrix n n ℂ)) := inferInstance
local instance dyadicCovarianceResponseJointSpace : NormedSpace ℝ
    (selfAdjoint (Matrix ι ι ℝ) × selfAdjoint (Matrix n n ℂ)) := inferInstance
local instance dyadicCovarianceResponseJointMaps : NormedAddCommGroup
    (densityTangent (n := n) →L[ℝ] (selfAdjoint (Matrix ι ι ℝ) × selfAdjoint (Matrix n n ℂ))) := inferInstance

/-- Negative density gradient in the fixed affine trace-one chart. -/
def covarianceGradientChart (m : ℕ) (hm : 1 ≤ m) (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ) (θ : ℝ)
    (S : selfAdjoint (Matrix n n ℂ))
    (P : selfAdjoint (Matrix ι ι ℝ) × densityTangent (n := n)) : densityTangent (n := n) →L[ℝ] ℝ :=
  -jointDensityTangentRestriction
    (fderiv ℝ (DyadicCovarianceCalculus.jointOwnerObjective m H A θ) (P.1, densityChart S P.2))

theorem contDiffAt_covarianceGradientChart (m : ℕ) (hm : 1 ≤ m) (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (θ : ℝ)
    (C : selfAdjoint (Matrix ι ι ℝ)) (S : selfAdjoint (Matrix n n ℂ))
    (hC : (C : Matrix ι ι ℝ).PosDef) (hS : (S : Matrix n n ℂ).PosDef) :
    ContDiffAt ℝ ∞ (covarianceGradientChart m hm H A θ S) (C, 0) := by
  have hg : ContDiffAt ℝ ∞ (fun P => fderiv ℝ (DyadicCovarianceCalculus.jointOwnerObjective m H A θ) P) (C, S) :=
    (DyadicCovarianceCalculus.contDiffAt_jointOwnerObjective m H A hA θ C S hC hS).fderiv_right (by simp)
  have hp : ContDiffAt ℝ ∞ (fun P : selfAdjoint (Matrix ι ι ℝ) × densityTangent (n := n) =>
      (P.1, densityChart S P.2)) (C, 0) :=
    contDiffAt_fst.prodMk (contDiffAt_const.add
      ((densityTangent (n := n)).subtypeL.contDiff.contDiffAt.comp (C, 0) contDiffAt_snd))
  have hg' : ContDiffAt ℝ ∞ (fun P => fderiv ℝ (DyadicCovarianceCalculus.jointOwnerObjective m H A θ) P)
      (C, densityChart S 0) := by simpa only [densityChart_zero] using hg
  exact ((jointDensityTangentRestriction (ι := ι) (n := n)).contDiff.contDiffAt.comp (C, 0)
    (hg'.comp (C, 0) hp)).neg

/-- On each positive covariance fiber, the actual joint gradient equals the already proved
actual density gradient for its covariance Kraus representation. -/
theorem covarianceGradientChart_eq_densityGradientChart (m : ℕ) (hm : 1 ≤ m)
    (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) (θ : ℝ)
    (C : selfAdjoint (Matrix ι ι ℝ)) (S : selfAdjoint (Matrix n n ℂ))
    (X : densityTangent (n := n)) (hC : (C : Matrix ι ι ℝ).PosDef)
    (hS : (densityChart S X : Matrix n n ℂ).PosDef) :
    covarianceGradientChart m hm H A θ S (C, X) = dyadicDensityGradientChart H (covarianceKraus A C) m θ S X := by
  have hd := ((DyadicCovarianceCalculus.contDiffAt_jointOwnerObjective m H A hA θ C (densityChart S X) hC hS).differentiableAt
    (by simp : (1 : WithTop ℕ∞) ≤ ∞)).hasFDerivAt
  have hp := hd.comp (densityChart S X)
    ((hasFDerivAt_const (𝕜 := ℝ) C (densityChart S X)).prodMk (hasFDerivAt_id _))
  have he : (fun T : selfAdjoint (Matrix n n ℂ) => DyadicCovarianceCalculus.jointOwnerObjective m H A θ (C, T)) =
      hermitianDyadicDensityObjective H (covarianceKraus A C) m θ := by
    funext T
    exact DyadicCovarianceCalculus.ownerObjective_eq_densityObjective m H A hA hC.posSemidef θ T
  change HasFDerivAt (fun T : selfAdjoint (Matrix n n ℂ) => DyadicCovarianceCalculus.jointOwnerObjective m H A θ (C, T)) _ _ at hp
  rw [he] at hp
  unfold covarianceGradientChart dyadicDensityGradientChart
  rw [hp.fderiv]
  congr 1

/-- Covariance block of the actual derivative of the constrained gradient. -/
def covarianceGradientCross (m : ℕ) (hm : 1 ≤ m) (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ) (θ : ℝ)
    (C : selfAdjoint (Matrix ι ι ℝ)) (S : selfAdjoint (Matrix n n ℂ)) :
    selfAdjoint (Matrix ι ι ℝ) →L[ℝ] (densityTangent (n := n) →L[ℝ] ℝ) :=
  (fderiv ℝ (covarianceGradientChart m hm H A θ S) (C, 0)).comp
    ((ContinuousLinearMap.id ℝ _).prod 0)

/-- The augmented parameter map retains covariance and records the actual density gradient. -/
def covarianceStationarityMap (m : ℕ) (hm : 1 ≤ m) (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ) (θ : ℝ)
    (S : selfAdjoint (Matrix n n ℂ))
    (P : selfAdjoint (Matrix ι ι ℝ) × densityTangent (n := n)) :=
  (P.1, covarianceGradientChart m hm H A θ S P)

/-- Its derivative is a genuine triangular continuous linear equivalence. -/
def covarianceStationarityEquiv (m : ℕ) (hm : 1 ≤ m) (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ)
    (θ : ℝ) (hθ : 0 < θ) (C : selfAdjoint (Matrix ι ι ℝ))
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef) :
    (selfAdjoint (Matrix ι ι ℝ) × densityTangent (n := n)) ≃L[ℝ]
      (selfAdjoint (Matrix ι ι ℝ) × (densityTangent (n := n) →L[ℝ] ℝ)) :=
  (ContinuousLinearEquiv.refl ℝ (selfAdjoint (Matrix ι ι ℝ))).skewProd
    (dyadicDensityTangentHessianEquiv H (covarianceKraus A C) m hm θ hθ S hS)
    (covarianceGradientCross m hm H A θ C S)

theorem hasStrictFDerivAt_covarianceStationarityMap (m : ℕ) (hm : 1 ≤ m)
    (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (θ : ℝ) (hθ : 0 < θ) (C : selfAdjoint (Matrix ι ι ℝ))
    (S : selfAdjoint (Matrix n n ℂ)) (hC : (C : Matrix ι ι ℝ).PosDef)
    (hS : (S : Matrix n n ℂ).PosDef) :
    HasStrictFDerivAt (covarianceStationarityMap m hm H A θ S)
      (covarianceStationarityEquiv m hm H A θ hθ C S hS).toContinuousLinearMap (C, 0) := by
  let J := fderiv ℝ (covarianceGradientChart m hm H A θ S) (C, 0)
  let E := dyadicDensityTangentHessianEquiv H (covarianceKraus A C) m hm θ hθ S hS
  have hg : HasStrictFDerivAt (covarianceGradientChart m hm H A θ S) J (C, 0) :=
    (contDiffAt_covarianceGradientChart m hm H A hA θ C S hC hS).hasStrictFDerivAt (by simp)
  have hx := hg.comp (0 : densityTangent (n := n))
    ((hasStrictFDerivAt_const (𝕜 := ℝ) C (0 : densityTangent (n := n))).prodMk (hasStrictFDerivAt_id _))
  have heq : ∀ᶠ X : densityTangent (n := n) in 𝓝 0,
      covarianceGradientChart m hm H A θ S (C, X) = dyadicDensityGradientChart H (covarianceKraus A C) m θ S X := by
    have hc := (hasStrictFDerivAt_densityChart S 0).continuousAt
    have hp : ∀ᶠ X : densityTangent (n := n) in 𝓝 0,
        (densityChart S X : Matrix n n ℂ).PosDef :=
      hc.eventually (by simpa only [densityChart_zero] using eventually_posDef_of_posDef S hS)
    filter_upwards [hp] with X hX
    exact covarianceGradientChart_eq_densityGradientChart m hm H A hA θ C S X hC hX
  have hx' := hx.congr_of_eventuallyEq heq
  have hright : J.comp ((0 : densityTangent (n := n) →L[ℝ] selfAdjoint (Matrix ι ι ℝ)).prod
      (ContinuousLinearMap.id ℝ _)) = E.toContinuousLinearMap :=
    hx'.hasFDerivAt.unique
      (hasStrictFDerivAt_dyadicDensityGradientChart H (covarianceKraus A C) m hm θ hθ S hS).hasFDerivAt
  have hd := (hasStrictFDerivAt_fst (𝕜 := ℝ) (p := (C, (0 : densityTangent (n := n))))).prodMk hg
  have he : (ContinuousLinearMap.fst ℝ _ _).prod J =
      (covarianceStationarityEquiv m hm H A θ hθ C S hS).toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro P
    change (P.1, J P) = (P.1, E P.2 + J (P.1, 0))
    apply congrArg (fun Y : densityTangent (n := n) →L[ℝ] ℝ => (P.1, Y))
    have hr := DFunLike.congr_fun hright P.2
    change J (0, P.2) = E P.2 at hr
    calc
      J P = J ((0, P.2) + (P.1, 0)) := by congr 1; simp
      _ = J (0, P.2) + J (P.1, 0) := J.map_add _ _
      _ = _ := by rw [hr]
  rw [he] at hd
  exact hd

theorem contDiffAt_covarianceStationarityMap (m : ℕ) (hm : 1 ≤ m)
    (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (θ : ℝ) (C : selfAdjoint (Matrix ι ι ℝ)) (S : selfAdjoint (Matrix n n ℂ))
    (hC : (C : Matrix ι ι ℝ).PosDef) (hS : (S : Matrix n n ℂ).PosDef) :
    ContDiffAt ℝ ∞ (covarianceStationarityMap m hm H A θ S) (C, 0) :=
  contDiffAt_fst.prodMk (contDiffAt_covarianceGradientChart m hm H A hA θ C S hC hS)

/-- The actual local inverse supplied by the ordinary Banach inverse-function theorem. -/
def covarianceStationarityLocalInverse (m : ℕ) (hm : 1 ≤ m)
    (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (θ : ℝ) (hθ : 0 < θ) (C : selfAdjoint (Matrix ι ι ℝ))
    (S : selfAdjoint (Matrix n n ℂ)) (hC : (C : Matrix ι ι ℝ).PosDef)
    (hS : (S : Matrix n n ℂ).PosDef) :
    (selfAdjoint (Matrix ι ι ℝ) × (densityTangent (n := n) →L[ℝ] ℝ)) →
      (selfAdjoint (Matrix ι ι ℝ) × densityTangent (n := n)) := by
  let f := covarianceStationarityMap m hm H A θ S
  let e := covarianceStationarityEquiv m hm H A θ hθ C S hS
  have hf : HasStrictFDerivAt f e.toContinuousLinearMap (C, 0) :=
    hasStrictFDerivAt_covarianceStationarityMap m hm H A hA θ hθ C S hC hS
  exact hf.localInverse f e (C, 0)

def dyadicCovarianceResponseBranch (m : ℕ) (hm : 1 ≤ m)
    (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (θ : ℝ) (hθ : 0 < θ) (C : selfAdjoint (Matrix ι ι ℝ))
    (S : selfAdjoint (Matrix n n ℂ)) (hC : (C : Matrix ι ι ℝ).PosDef)
    (hS : (S : Matrix n n ℂ).PosDef) (K : selfAdjoint (Matrix ι ι ℝ)) :
    selfAdjoint (Matrix n n ℂ) :=
  densityChart S ((covarianceStationarityLocalInverse m hm H A hA θ hθ C S hC hS (K, 0)).2)

theorem covarianceStationarityMap_base (m : ℕ) (hm : 1 ≤ m)
    (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (θ : ℝ) (C : selfAdjoint (Matrix ι ι ℝ)) (S : selfAdjoint (Matrix n n ℂ))
    (hC : (C : Matrix ι ι ℝ).PosDef) (hS : (S : Matrix n n ℂ).PosDef)
    (hstat : densityTangentRestriction
      (fderiv ℝ (hermitianDyadicDensityObjective H (covarianceKraus A C) m θ) S) = 0) :
    covarianceStationarityMap m hm H A θ S (C, 0) = (C, 0) := by
  change (C, covarianceGradientChart m hm H A θ S (C, 0)) = (C, 0)
  rw [covarianceGradientChart_eq_densityGradientChart m hm H A hA θ C S 0 hC
    (by simpa only [densityChart_zero] using hS)]
  simp only [dyadicDensityGradientChart, densityChart_zero, hstat, neg_zero]

theorem contDiffAt_dyadicCovarianceResponseBranch (m : ℕ) (hm : 1 ≤ m)
    (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (θ : ℝ) (hθ : 0 < θ) (C : selfAdjoint (Matrix ι ι ℝ))
    (S : selfAdjoint (Matrix n n ℂ)) (hC : (C : Matrix ι ι ℝ).PosDef)
    (hS : (S : Matrix n n ℂ).PosDef)
    (hstat : densityTangentRestriction
      (fderiv ℝ (hermitianDyadicDensityObjective H (covarianceKraus A C) m θ) S) = 0) :
    ContDiffAt ℝ ∞ (dyadicCovarianceResponseBranch m hm H A hA θ hθ C S hC hS) C := by
  have hf := hasStrictFDerivAt_covarianceStationarityMap m hm H A hA θ hθ C S hC hS
  have hg := contDiffAt_covarianceStationarityMap m hm H A hA θ C S hC hS
  have hi : ContDiffAt ℝ ∞ (hf.localInverse _ _ (C, 0))
      (covarianceStationarityMap m hm H A θ S (C, 0)) := hg.to_localInverse hf.hasFDerivAt (by simp)
  rw [covarianceStationarityMap_base m hm H A hA θ C S hC hS hstat] at hi
  have hc : ContDiffAt ℝ ∞ (fun K : selfAdjoint (Matrix ι ι ℝ) =>
      (K, (0 : densityTangent (n := n) →L[ℝ] ℝ))) C := contDiffAt_id.prodMk contDiffAt_const
  have ht := hi.comp C hc
  exact contDiffAt_const.add ((densityTangent (n := n)).subtypeL.contDiff.contDiffAt.comp C
    (contDiffAt_snd.comp C ht))

/-- The local stationary branch equals the actual chosen global density optimizer. -/
theorem eventually_covarianceOptimizer_eq_responseBranch (m : ℕ) (hm : 1 ≤ m) [Nonempty n]
    (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (θ : ℝ) (hθ : 0 < θ) (C : selfAdjoint (Matrix ι ι ℝ))
    (S : selfAdjoint (Matrix n n ℂ)) (hC : (C : Matrix ι ι ℝ).PosDef)
    (hS : (S : Matrix n n ℂ).PosDef) (ht : realTrace (S : Matrix n n ℂ) = 1)
    (hstat : densityTangentRestriction
      (fderiv ℝ (hermitianDyadicDensityObjective H (covarianceKraus A C) m θ) S) = 0) :
    ∀ᶠ K : selfAdjoint (Matrix ι ι ℝ) in 𝓝 C,
      hermitianDyadicDensityOptimizer H (covarianceKraus A K) m θ =
        dyadicCovarianceResponseBranch m hm H A hA θ hθ C S hC hS K := by
  have hf := hasStrictFDerivAt_covarianceStationarityMap m hm H A hA θ hθ C S hC hS
  have hf0 := covarianceStationarityMap_base m hm H A hA θ C S hC hS hstat
  let target := fun K : selfAdjoint (Matrix ι ι ℝ) => (K, (0 : densityTangent (n := n) →L[ℝ] ℝ))
  have htarget : Tendsto target (𝓝 C) (𝓝 (covarianceStationarityMap m hm H A θ S (C, 0))) := by
    rw [hf0]
    exact (continuousAt_id.prodMk continuousAt_const).tendsto
  let inv := hf.localInverse (covarianceStationarityMap m hm H A θ S)
    (covarianceStationarityEquiv m hm H A θ hθ C S hS) (C, 0)
  have hinv : Tendsto (fun K => inv (target K)) (𝓝 C) (𝓝 (C, 0)) :=
    hf.localInverse_tendsto.comp htarget
  have hchart : Tendsto (fun K => densityChart S ((inv (target K)).2)) (𝓝 C) (𝓝 S) := by
    have hx : Tendsto (fun K => (inv (target K)).2) (𝓝 C) (𝓝 (0 : densityTangent (n := n))) :=
      continuous_snd.continuousAt.tendsto.comp hinv
    simpa only [densityChart_zero] using (hasStrictFDerivAt_densityChart S 0).continuousAt.tendsto.comp hx
  filter_upwards [eventually_real_posDef_of_posDef C hC,
    hchart.eventually (eventually_posDef_of_posDef S hS),
    htarget.eventually hf.eventually_right_inverse] with K hK hSK heq
  change hermitianDyadicDensityOptimizer H (covarianceKraus A K) m θ = densityChart S ((inv (target K)).2)
  apply dyadicDensity_stationary_eq_optimizer H (covarianceKraus A K) m hm θ hθ _ hSK
    ((densityChart_trace S _).trans ht)
  have hfirst := congrArg Prod.fst heq
  have hgrad := congrArg Prod.snd heq
  change (inv (target K)).1 = K at hfirst
  change covarianceGradientChart m hm H A θ S (inv (target K)) = 0 at hgrad
  have hg : covarianceGradientChart m hm H A θ S (K, (inv (target K)).2) = 0 := by
    have hp : (K, (inv (target K)).2) = inv (target K) := by
      apply Prod.ext
      · exact hfirst.symm
      · rfl
    rw [hp]
    exact hgrad
  rw [covarianceGradientChart_eq_densityGradientChart m hm H A hA θ K S _ hK hSK] at hg
  change -densityTangentRestriction
    (fderiv ℝ (hermitianDyadicDensityObjective H (covarianceKraus A K) m θ)
      (densityChart S ((inv (target K)).2))) = 0 at hg
  exact neg_eq_zero.mp hg

/-- Actual density optimizer smoothness in positive coefficient covariances. -/
theorem contDiffAt_covarianceDensityOptimizer (m : ℕ) (hm : 1 ≤ m) [Nonempty n]
    (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {θ : ℝ} (hθ : 0 < θ) (C : selfAdjoint (Matrix ι ι ℝ))
    (hC : (C : Matrix ι ι ℝ).PosDef) :
    ContDiffAt ℝ ∞ (fun K : selfAdjoint (Matrix ι ι ℝ) =>
      hermitianDyadicDensityOptimizer H (covarianceKraus A K) m θ) C := by
  let S := hermitianDyadicDensityOptimizer H (covarianceKraus A C) m θ
  have hS : (S : Matrix n n ℂ).PosDef := hermitianDyadicDensityOptimizer_posDef H (covarianceKraus A C) m hm θ hθ
  have ht : realTrace (S : Matrix n n ℂ) = 1 := hermitianDyadicDensityOptimizer_trace H (covarianceKraus A C) m θ
  have hstat := dyadicDensityOptimizer_stationary H (covarianceKraus A C) m hm θ hθ
  exact (contDiffAt_dyadicCovarianceResponseBranch m hm H A hA θ hθ C S hC hS hstat).congr_of_eventuallyEq
    (eventually_covarianceOptimizer_eq_responseBranch m hm H A hA θ hθ C S hC hS ht hstat)

/-- The original supremum potential on real symmetric coefficient covariances. -/
def hermitianOwnerPotential (m : ℕ) (hm : 1 ≤ m) (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ) (θ : ℝ)
    (C : selfAdjoint (Matrix ι ι ℝ)) : ℝ := DyadicCovarianceCalculus.ownerPotential m H A C θ

theorem ownerPotential_eq_chosenObjective (m : ℕ) (hm : 1 ≤ m) [Nonempty n]
    (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (θ : ℝ) (C : selfAdjoint (Matrix ι ι ℝ)) (hC : (C : Matrix ι ι ℝ).PosSemidef) :
    hermitianOwnerPotential m hm H A θ C =
      DyadicCovarianceCalculus.ownerObjective m H A C θ (hermitianDyadicDensityOptimizer H (covarianceKraus A C) m θ) := by
  change DyadicCovarianceCalculus.ownerPotential m H A C θ = _
  rw [DyadicCovarianceCalculus.ownerPotential_eq_densityPotential m H A hA hC,
    DyadicCovarianceCalculus.ownerObjective_eq_densityObjective m H A hA hC]
  exact dyadicDensityPotential_eq_of_maximizer H (covarianceKraus A C) m θ
    (S := dyadicDensityOptimizer H (covarianceKraus A C) m θ)
    (dyadicDensityOptimizer_mem H (covarianceKraus A C) m θ)
    (dyadicDensityOptimizer_isMaxOn H (covarianceKraus A C) m θ)

/-- Smoothness of the actual optimized value, with no covariance response assumption. -/
theorem contDiffAt_hermitianOwnerPotential (m : ℕ) (hm : 1 ≤ m) [Nonempty n]
    (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {θ : ℝ} (hθ : 0 < θ) (C : selfAdjoint (Matrix ι ι ℝ))
    (hC : (C : Matrix ι ι ℝ).PosDef) :
    ContDiffAt ℝ ∞ (hermitianOwnerPotential m hm H A θ) C := by
  have hs := contDiffAt_covarianceDensityOptimizer m hm H A hA hθ C hC
  have ho := DyadicCovarianceCalculus.contDiffAt_jointOwnerObjective m H A hA θ C
    (hermitianDyadicDensityOptimizer H (covarianceKraus A C) m θ) hC
    (hermitianDyadicDensityOptimizer_posDef H (covarianceKraus A C) m hm θ hθ)
  apply (ho.comp C (contDiffAt_id.prodMk hs)).congr_of_eventuallyEq
  filter_upwards [eventually_real_posDef_of_posDef C hC] with K hK
  exact ownerPotential_eq_chosenObjective m hm H A hA θ K hK.posSemidef

/-- The envelope derivative of the genuine covariance-dependent supremum. -/
theorem hasFDerivAt_hermitianOwnerPotential_covariance (m : ℕ) (hm : 1 ≤ m) [Nonempty n]
    (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {θ : ℝ} (hθ : 0 < θ) (C : selfAdjoint (Matrix ι ι ℝ))
    (hC : (C : Matrix ι ι ℝ).PosDef) :
    HasFDerivAt (hermitianOwnerPotential m hm H A θ)
      (covarianceDerivativeFunctional A C (hermitianDyadicDensityOptimizer H (covarianceKraus A C) m θ)) C := by
  let S := hermitianDyadicDensityOptimizer H (covarianceKraus A C) m θ
  have hd := ((contDiffAt_hermitianOwnerPotential m hm H A hA hθ C hC).differentiableAt
    (by simp : (1 : WithTop ℕ∞) ≤ ∞)).hasFDerivAt
  have hf := (DyadicCovarianceCalculus.hasStrictFDerivAt_ownerObjective_covariance m H A hA θ C S hC
    (hermitianDyadicDensityOptimizer_posDef H (covarianceKraus A C) m hm θ hθ)).hasFDerivAt
  have hmin : IsLocalMin (fun K : selfAdjoint (Matrix ι ι ℝ) =>
      hermitianOwnerPotential m hm H A θ K - DyadicCovarianceCalculus.ownerObjective m H A K θ S) C := by
    filter_upwards [eventually_real_posDef_of_posDef C hC] with K hK
    change hermitianOwnerPotential m hm H A θ C - DyadicCovarianceCalculus.ownerObjective m H A C θ S ≤
      hermitianOwnerPotential m hm H A θ K - DyadicCovarianceCalculus.ownerObjective m H A K θ S
    rw [ownerPotential_eq_chosenObjective m hm H A hA θ C hC.posSemidef]
    change DyadicCovarianceCalculus.ownerObjective m H A C θ S - DyadicCovarianceCalculus.ownerObjective m H A C θ S ≤ _
    rw [sub_self]
    apply sub_nonneg.mpr
    change DyadicCovarianceCalculus.ownerObjective m H A K θ S ≤ DyadicCovarianceCalculus.ownerPotential m H A K θ
    rw [DyadicCovarianceCalculus.ownerObjective_eq_densityObjective m H A hA hK.posSemidef,
      DyadicCovarianceCalculus.ownerPotential_eq_densityPotential m H A hA hK.posSemidef]
    exact dyadicDensityObjective_le_potential H (covarianceKraus A K) m θ
      (S := dyadicDensityOptimizer H (covarianceKraus A C) m θ)
      (dyadicDensityOptimizer_mem H (covarianceKraus A C) m θ)
  have hz := hmin.hasFDerivAt_eq_zero (hd.sub hf)
  rwa [sub_eq_zero.mp hz] at hd

theorem hasStrictFDerivAt_hermitianOwnerPotential_covariance (m : ℕ) (hm : 1 ≤ m) [Nonempty n]
    (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {θ : ℝ} (hθ : 0 < θ) (C : selfAdjoint (Matrix ι ι ℝ))
    (hC : (C : Matrix ι ι ℝ).PosDef) :
    HasStrictFDerivAt (hermitianOwnerPotential m hm H A θ)
      (covarianceDerivativeFunctional A C (hermitianDyadicDensityOptimizer H (covarianceKraus A C) m θ)) C :=
  (contDiffAt_hermitianOwnerPotential m hm H A hA hθ C hC).hasStrictFDerivAt'
    (hasFDerivAt_hermitianOwnerPotential_covariance m hm H A hA hθ C hC) (by simp)

/-- Exact covariance response of the actual optimum, including singular physical sources. -/
theorem fderiv_hermitianOwnerPotential_covariance_apply (m : ℕ) (hm : 1 ≤ m) [Nonempty n]
    (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {θ : ℝ} (hθ : 0 < θ) (C ΔC : selfAdjoint (Matrix ι ι ℝ))
    (hC : (C : Matrix ι ι ℝ).PosDef) :
    fderiv ℝ (hermitianOwnerPotential m hm H A θ) C ΔC =
      realTrace (covarianceSupportTransport A C (hermitianDyadicDensityOptimizer H (covarianceKraus A C) m θ) *
        covarianceSource A ΔC (hermitianDyadicDensityOptimizer H (covarianceKraus A C) m θ)) := by
  rw [(hasFDerivAt_hermitianOwnerPotential_covariance m hm H A hA hθ C hC).fderiv]
  exact covarianceDerivativeFunctional_apply A hA C ΔC _

end
end DyadicCovarianceResponse

noncomputable section
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n]
local instance dyadicOwnerCovarianceAPICStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance dyadicOwnerCovarianceAPISpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance
local instance dyadicOwnerCovarianceAPICoeffSpace : NormedSpace ℝ (selfAdjoint (Matrix ι ι ℝ)) := inferInstance

/-- The actual dyadic owner supremum, in covariance coordinates. -/
def hermitianDyadicOwnerPotential (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ)
    (m : ℕ) (θ : ℝ) (C : selfAdjoint (Matrix ι ι ℝ)) : ℝ :=
  regularizedOwnerPotential H A C (dyadicTsallisRegularizer m θ)

theorem contDiffAt_hermitianDyadicOwnerPotential [Nonempty n]
    (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (hθ : 0 < θ)
    (C : selfAdjoint (Matrix ι ι ℝ)) (hC : (C : Matrix ι ι ℝ).PosDef) :
    ContDiffAt ℝ ∞ (hermitianDyadicOwnerPotential H A m θ) C :=
  DyadicCovarianceResponse.contDiffAt_hermitianOwnerPotential m hm H A hA hθ C hC

theorem hasFDerivAt_hermitianDyadicOwnerPotential_covariance [Nonempty n]
    (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (hθ : 0 < θ)
    (C : selfAdjoint (Matrix ι ι ℝ)) (hC : (C : Matrix ι ι ℝ).PosDef) :
    HasFDerivAt (hermitianDyadicOwnerPotential H A m θ)
      (covarianceDerivativeFunctional A C
        (hermitianDyadicDensityOptimizer H (covarianceKraus A C) m θ)) C :=
  DyadicCovarianceResponse.hasFDerivAt_hermitianOwnerPotential_covariance m hm H A hA hθ C hC

theorem hasStrictFDerivAt_hermitianDyadicOwnerPotential_covariance [Nonempty n]
    (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (hθ : 0 < θ)
    (C : selfAdjoint (Matrix ι ι ℝ)) (hC : (C : Matrix ι ι ℝ).PosDef) :
    HasStrictFDerivAt (hermitianDyadicOwnerPotential H A m θ)
      (covarianceDerivativeFunctional A C
        (hermitianDyadicDensityOptimizer H (covarianceKraus A C) m θ)) C :=
  DyadicCovarianceResponse.hasStrictFDerivAt_hermitianOwnerPotential_covariance m hm H A hA hθ C hC

theorem fderiv_hermitianDyadicOwnerPotential_covariance_apply [Nonempty n]
    (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (hθ : 0 < θ)
    (C ΔC : selfAdjoint (Matrix ι ι ℝ)) (hC : (C : Matrix ι ι ℝ).PosDef) :
    fderiv ℝ (hermitianDyadicOwnerPotential H A m θ) C ΔC =
      realTrace (covarianceSupportTransport A C
        (hermitianDyadicDensityOptimizer H (covarianceKraus A C) m θ) *
        covarianceSource A ΔC (hermitianDyadicDensityOptimizer H (covarianceKraus A C) m θ)) :=
  DyadicCovarianceResponse.fderiv_hermitianOwnerPotential_covariance_apply m hm H A hA hθ C ΔC hC

end
end MatrixSpencer
