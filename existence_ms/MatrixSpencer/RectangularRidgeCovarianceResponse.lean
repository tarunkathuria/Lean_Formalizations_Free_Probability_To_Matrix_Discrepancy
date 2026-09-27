import MatrixSpencer.RectangularRidgeCovarianceCalculus
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
namespace RectangularRidgeCovarianceResponse
open RectangularRidgeCalculus RectangularRidgePotential
noncomputable section
set_option maxHeartbeats 300000
attribute [local irreducible] RectangularRidgePotential.optimizer
set_option linter.unusedVariables false
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n]
local instance ridgeCovarianceResponseCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance ridgeCovarianceResponsePhysicalGroup : NormedAddCommGroup (selfAdjoint (Matrix n n ℂ)) := inferInstance
local instance ridgeCovarianceResponseCoeffGroup : NormedAddCommGroup (selfAdjoint (Matrix ι ι ℝ)) := inferInstance
local instance ridgeCovarianceResponsePhysicalSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance
local instance ridgeCovarianceResponseCoeffSpace : NormedSpace ℝ (selfAdjoint (Matrix ι ι ℝ)) := inferInstance
local instance ridgeCovarianceResponsePhysicalFinite : FiniteDimensional ℝ (selfAdjoint (Matrix n n ℂ)) :=
  inferInstanceAs (FiniteDimensional ℝ (selfAdjoint.submodule ℝ (Matrix n n ℂ)))
local instance ridgeCovarianceResponseCoeffFinite : FiniteDimensional ℝ (selfAdjoint (Matrix ι ι ℝ)) :=
  inferInstanceAs (FiniteDimensional ℝ (selfAdjoint.submodule ℝ (Matrix ι ι ℝ)))
local instance ridgeCovarianceResponseCoeffComplete : CompleteSpace (selfAdjoint (Matrix ι ι ℝ)) :=
  FiniteDimensional.complete ℝ _
local instance ridgeCovarianceResponseTangentGroup : NormedAddCommGroup (densityTangent (n := n)) := inferInstance
local instance ridgeCovarianceResponseTangentSpace : NormedSpace ℝ (densityTangent (n := n)) := inferInstance
local instance ridgeCovarianceResponseTangentFinite : FiniteDimensional ℝ (densityTangent (n := n)) := inferInstance
local instance ridgeCovarianceResponseTangentComplete : CompleteSpace (densityTangent (n := n)) :=
  FiniteDimensional.complete ℝ _
local instance ridgeCovarianceResponseDualGroup : NormedAddCommGroup (densityTangent (n := n) →L[ℝ] ℝ) := inferInstance
local instance ridgeCovarianceResponseDualSpace : NormedSpace ℝ (densityTangent (n := n) →L[ℝ] ℝ) := inferInstance

local instance ridgeCovarianceResponseJointGroup : NormedAddCommGroup
    (selfAdjoint (Matrix ι ι ℝ) × selfAdjoint (Matrix n n ℂ)) := inferInstance
local instance ridgeCovarianceResponseJointSpace : NormedSpace ℝ
    (selfAdjoint (Matrix ι ι ℝ) × selfAdjoint (Matrix n n ℂ)) := inferInstance
local instance ridgeCovarianceResponseJointMaps : NormedAddCommGroup
    (densityTangent (n := n) →L[ℝ] (selfAdjoint (Matrix ι ι ℝ) × selfAdjoint (Matrix n n ℂ))) := inferInstance

/-- Negative density gradient in the fixed affine trace-one chart. -/
def covarianceGradientChart (m : ℕ) (hm : 1 ≤ m) (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ) (θ κ : ℝ)
    (S : selfAdjoint (Matrix n n ℂ))
    (P : selfAdjoint (Matrix ι ι ℝ) × densityTangent (n := n)) : densityTangent (n := n) →L[ℝ] ℝ :=
  -jointDensityTangentRestriction
    (fderiv ℝ (RectangularRidgeCovarianceCalculus.jointOwnerObjective m H A θ κ) (P.1, densityChart S P.2))

theorem contDiffAt_covarianceGradientChart (m : ℕ) (hm : 1 ≤ m) (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (θ κ : ℝ)
    (C : selfAdjoint (Matrix ι ι ℝ)) (S : selfAdjoint (Matrix n n ℂ))
    (hC : (C : Matrix ι ι ℝ).PosDef) (hS : (S : Matrix n n ℂ).PosDef) :
    ContDiffAt ℝ ∞ (covarianceGradientChart m hm H A θ κ S) (C, 0) := by
  have hg : ContDiffAt ℝ ∞ (fun P => fderiv ℝ (RectangularRidgeCovarianceCalculus.jointOwnerObjective m H A θ κ) P) (C, S) :=
    (RectangularRidgeCovarianceCalculus.contDiffAt_jointOwnerObjective m H A hA θ κ C S hC hS).fderiv_right (by simp)
  have hp : ContDiffAt ℝ ∞ (fun P : selfAdjoint (Matrix ι ι ℝ) × densityTangent (n := n) =>
      (P.1, densityChart S P.2)) (C, 0) :=
    contDiffAt_fst.prodMk (contDiffAt_const.add
      ((densityTangent (n := n)).subtypeL.contDiff.contDiffAt.comp (C, 0) contDiffAt_snd))
  have hg' : ContDiffAt ℝ ∞ (fun P => fderiv ℝ (RectangularRidgeCovarianceCalculus.jointOwnerObjective m H A θ κ) P)
      (C, densityChart S 0) := by simpa only [densityChart_zero] using hg
  exact ((jointDensityTangentRestriction (ι := ι) (n := n)).contDiff.contDiffAt.comp (C, 0)
    (hg'.comp (C, 0) hp)).neg

/-- On each positive covariance fiber, the actual joint gradient equals the already proved
actual density gradient for its covariance Kraus representation. -/
theorem covarianceGradientChart_eq_densityGradientChart (m : ℕ) (hm : 1 ≤ m)
    (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) (θ κ : ℝ)
    (C : selfAdjoint (Matrix ι ι ℝ)) (S : selfAdjoint (Matrix n n ℂ))
    (X : densityTangent (n := n)) (hC : (C : Matrix ι ι ℝ).PosDef)
    (hS : (densityChart S X : Matrix n n ℂ).PosDef) :
    covarianceGradientChart m hm H A θ κ S (C, X) = RectangularRidgeCalculus.gradientChart H (covarianceKraus A C) m θ κ S X := by
  have hd := ((RectangularRidgeCovarianceCalculus.contDiffAt_jointOwnerObjective m H A hA θ κ C (densityChart S X) hC hS).differentiableAt
    (by simp : (1 : WithTop ℕ∞) ≤ ∞)).hasFDerivAt
  have hp := hd.comp (densityChart S X)
    ((hasFDerivAt_const (𝕜 := ℝ) C (densityChart S X)).prodMk (hasFDerivAt_id _))
  have he : (fun T : selfAdjoint (Matrix n n ℂ) => RectangularRidgeCovarianceCalculus.jointOwnerObjective m H A θ κ (C, T)) =
      RectangularRidgeCalculus.hermitianObjective H (covarianceKraus A C) m θ κ := by
    funext T
    exact RectangularRidgeCovarianceCalculus.ownerObjective_eq_densityObjective m H A hA hC.posSemidef θ κ T
  change HasFDerivAt (fun T : selfAdjoint (Matrix n n ℂ) => RectangularRidgeCovarianceCalculus.jointOwnerObjective m H A θ κ (C, T)) _ _ at hp
  rw [he] at hp
  unfold covarianceGradientChart RectangularRidgeCalculus.gradientChart
  rw [hp.fderiv]
  congr 1

/-- Covariance block of the actual derivative of the constrained gradient. -/
def covarianceGradientCross (m : ℕ) (hm : 1 ≤ m) (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ) (θ κ : ℝ)
    (C : selfAdjoint (Matrix ι ι ℝ)) (S : selfAdjoint (Matrix n n ℂ)) :
    selfAdjoint (Matrix ι ι ℝ) →L[ℝ] (densityTangent (n := n) →L[ℝ] ℝ) :=
  (fderiv ℝ (covarianceGradientChart m hm H A θ κ S) (C, 0)).comp
    ((ContinuousLinearMap.id ℝ _).prod 0)

/-- The augmented parameter map retains covariance and records the actual density gradient. -/
def covarianceStationarityMap (m : ℕ) (hm : 1 ≤ m) (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ) (θ κ : ℝ)
    (S : selfAdjoint (Matrix n n ℂ))
    (P : selfAdjoint (Matrix ι ι ℝ) × densityTangent (n := n)) :=
  (P.1, covarianceGradientChart m hm H A θ κ S P)

/-- Its derivative is a genuine triangular continuous linear equivalence. -/
def covarianceStationarityEquiv (m : ℕ) (hm : 1 ≤ m) (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ)
    (θ κ : ℝ) (hθ : 0 < θ) (hκ : 0 < κ) (C : selfAdjoint (Matrix ι ι ℝ))
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef) :
    (selfAdjoint (Matrix ι ι ℝ) × densityTangent (n := n)) ≃L[ℝ]
      (selfAdjoint (Matrix ι ι ℝ) × (densityTangent (n := n) →L[ℝ] ℝ)) :=
  (ContinuousLinearEquiv.refl ℝ (selfAdjoint (Matrix ι ι ℝ))).skewProd
    (RectangularRidgeCalculus.tangentHessianEquiv H (covarianceKraus A C) m hm θ κ hθ hκ S hS)
    (covarianceGradientCross m hm H A θ κ C S)

theorem hasStrictFDerivAt_covarianceStationarityMap (m : ℕ) (hm : 1 ≤ m)
    (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (θ κ : ℝ) (hθ : 0 < θ) (hκ : 0 < κ) (C : selfAdjoint (Matrix ι ι ℝ))
    (S : selfAdjoint (Matrix n n ℂ)) (hC : (C : Matrix ι ι ℝ).PosDef)
    (hS : (S : Matrix n n ℂ).PosDef) :
    HasStrictFDerivAt (covarianceStationarityMap m hm H A θ κ S)
      (covarianceStationarityEquiv m hm H A θ κ hθ hκ C S hS).toContinuousLinearMap (C, 0) := by
  let J := fderiv ℝ (covarianceGradientChart m hm H A θ κ S) (C, 0)
  let E := RectangularRidgeCalculus.tangentHessianEquiv H (covarianceKraus A C) m hm θ κ hθ hκ S hS
  have hg : HasStrictFDerivAt (covarianceGradientChart m hm H A θ κ S) J (C, 0) :=
    (contDiffAt_covarianceGradientChart m hm H A hA θ κ C S hC hS).hasStrictFDerivAt (by simp)
  have hx := hg.comp (0 : densityTangent (n := n))
    ((hasStrictFDerivAt_const (𝕜 := ℝ) C (0 : densityTangent (n := n))).prodMk (hasStrictFDerivAt_id _))
  have heq : ∀ᶠ X : densityTangent (n := n) in 𝓝 0,
      covarianceGradientChart m hm H A θ κ S (C, X) = RectangularRidgeCalculus.gradientChart H (covarianceKraus A C) m θ κ S X := by
    have hc := (hasStrictFDerivAt_densityChart S 0).continuousAt
    have hp : ∀ᶠ X : densityTangent (n := n) in 𝓝 0,
        (densityChart S X : Matrix n n ℂ).PosDef :=
      hc.eventually (by simpa only [densityChart_zero] using eventually_posDef_of_posDef S hS)
    filter_upwards [hp] with X hX
    exact covarianceGradientChart_eq_densityGradientChart m hm H A hA θ κ C S X hC hX
  have hx' := hx.congr_of_eventuallyEq heq
  have hright : J.comp ((0 : densityTangent (n := n) →L[ℝ] selfAdjoint (Matrix ι ι ℝ)).prod
      (ContinuousLinearMap.id ℝ _)) = E.toContinuousLinearMap :=
    hx'.hasFDerivAt.unique
      (RectangularRidgeCalculus.hasStrictFDerivAt_gradientChart H (covarianceKraus A C) m hm θ κ hθ hκ S hS).hasFDerivAt
  have hd := (hasStrictFDerivAt_fst (𝕜 := ℝ) (p := (C, (0 : densityTangent (n := n))))).prodMk hg
  have he : (ContinuousLinearMap.fst ℝ _ _).prod J =
      (covarianceStationarityEquiv m hm H A θ κ hθ hκ C S hS).toContinuousLinearMap := by
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
    (θ κ : ℝ) (C : selfAdjoint (Matrix ι ι ℝ)) (S : selfAdjoint (Matrix n n ℂ))
    (hC : (C : Matrix ι ι ℝ).PosDef) (hS : (S : Matrix n n ℂ).PosDef) :
    ContDiffAt ℝ ∞ (covarianceStationarityMap m hm H A θ κ S) (C, 0) :=
  contDiffAt_fst.prodMk (contDiffAt_covarianceGradientChart m hm H A hA θ κ C S hC hS)

/-- The actual local inverse supplied by the ordinary Banach inverse-function theorem. -/
def covarianceStationarityLocalInverse (m : ℕ) (hm : 1 ≤ m)
    (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (θ κ : ℝ) (hθ : 0 < θ) (hκ : 0 < κ) (C : selfAdjoint (Matrix ι ι ℝ))
    (S : selfAdjoint (Matrix n n ℂ)) (hC : (C : Matrix ι ι ℝ).PosDef)
    (hS : (S : Matrix n n ℂ).PosDef) :
    (selfAdjoint (Matrix ι ι ℝ) × (densityTangent (n := n) →L[ℝ] ℝ)) →
      (selfAdjoint (Matrix ι ι ℝ) × densityTangent (n := n)) := by
  let f := covarianceStationarityMap m hm H A θ κ S
  let e := covarianceStationarityEquiv m hm H A θ κ hθ hκ C S hS
  have hf : HasStrictFDerivAt f e.toContinuousLinearMap (C, 0) :=
    hasStrictFDerivAt_covarianceStationarityMap m hm H A hA θ κ hθ hκ C S hC hS
  exact hf.localInverse f e (C, 0)

def ridgeCovarianceResponseBranch (m : ℕ) (hm : 1 ≤ m)
    (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (θ κ : ℝ) (hθ : 0 < θ) (hκ : 0 < κ) (C : selfAdjoint (Matrix ι ι ℝ))
    (S : selfAdjoint (Matrix n n ℂ)) (hC : (C : Matrix ι ι ℝ).PosDef)
    (hS : (S : Matrix n n ℂ).PosDef) (K : selfAdjoint (Matrix ι ι ℝ)) :
    selfAdjoint (Matrix n n ℂ) :=
  densityChart S ((covarianceStationarityLocalInverse m hm H A hA θ κ hθ hκ C S hC hS (K, 0)).2)

theorem covarianceStationarityMap_base (m : ℕ) (hm : 1 ≤ m)
    (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (θ κ : ℝ) (C : selfAdjoint (Matrix ι ι ℝ)) (S : selfAdjoint (Matrix n n ℂ))
    (hC : (C : Matrix ι ι ℝ).PosDef) (hS : (S : Matrix n n ℂ).PosDef)
    (hstat : densityTangentRestriction
      (fderiv ℝ (RectangularRidgeCalculus.hermitianObjective H (covarianceKraus A C) m θ κ) S) = 0) :
    covarianceStationarityMap m hm H A θ κ S (C, 0) = (C, 0) := by
  change (C, covarianceGradientChart m hm H A θ κ S (C, 0)) = (C, 0)
  rw [covarianceGradientChart_eq_densityGradientChart m hm H A hA θ κ C S 0 hC
    (by simpa only [densityChart_zero] using hS)]
  simp only [RectangularRidgeCalculus.gradientChart, densityChart_zero, hstat, neg_zero]

theorem contDiffAt_ridgeCovarianceResponseBranch (m : ℕ) (hm : 1 ≤ m)
    (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (θ κ : ℝ) (hθ : 0 < θ) (hκ : 0 < κ) (C : selfAdjoint (Matrix ι ι ℝ))
    (S : selfAdjoint (Matrix n n ℂ)) (hC : (C : Matrix ι ι ℝ).PosDef)
    (hS : (S : Matrix n n ℂ).PosDef)
    (hstat : densityTangentRestriction
      (fderiv ℝ (RectangularRidgeCalculus.hermitianObjective H (covarianceKraus A C) m θ κ) S) = 0) :
    ContDiffAt ℝ ∞ (ridgeCovarianceResponseBranch m hm H A hA θ κ hθ hκ C S hC hS) C := by
  have hf := hasStrictFDerivAt_covarianceStationarityMap m hm H A hA θ κ hθ hκ C S hC hS
  have hg := contDiffAt_covarianceStationarityMap m hm H A hA θ κ C S hC hS
  have hi : ContDiffAt ℝ ∞ (hf.localInverse _ _ (C, 0))
      (covarianceStationarityMap m hm H A θ κ S (C, 0)) := hg.to_localInverse hf.hasFDerivAt (by simp)
  rw [covarianceStationarityMap_base m hm H A hA θ κ C S hC hS hstat] at hi
  have hc : ContDiffAt ℝ ∞ (fun K : selfAdjoint (Matrix ι ι ℝ) =>
      (K, (0 : densityTangent (n := n) →L[ℝ] ℝ))) C := contDiffAt_id.prodMk contDiffAt_const
  have ht := hi.comp C hc
  exact contDiffAt_const.add ((densityTangent (n := n)).subtypeL.contDiff.contDiffAt.comp C
    (contDiffAt_snd.comp C ht))

/-- The local stationary branch equals the actual chosen global density optimizer. -/
theorem eventually_covarianceOptimizer_eq_responseBranch (m : ℕ) (hm : 1 ≤ m) [Nonempty n]
    (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (θ κ : ℝ) (hθ : 0 < θ) (hκ : 0 < κ) (C : selfAdjoint (Matrix ι ι ℝ))
    (S : selfAdjoint (Matrix n n ℂ)) (hC : (C : Matrix ι ι ℝ).PosDef)
    (hS : (S : Matrix n n ℂ).PosDef) (ht : realTrace (S : Matrix n n ℂ) = 1)
    (hstat : densityTangentRestriction
      (fderiv ℝ (RectangularRidgeCalculus.hermitianObjective H (covarianceKraus A C) m θ κ) S) = 0) :
    ∀ᶠ K : selfAdjoint (Matrix ι ι ℝ) in 𝓝 C,
      RectangularRidgeCalculus.hermitianOptimizer H (covarianceKraus A K) m θ κ =
        ridgeCovarianceResponseBranch m hm H A hA θ κ hθ hκ C S hC hS K := by
  have hf := hasStrictFDerivAt_covarianceStationarityMap m hm H A hA θ κ hθ hκ C S hC hS
  have hf0 := covarianceStationarityMap_base m hm H A hA θ κ C S hC hS hstat
  let target := fun K : selfAdjoint (Matrix ι ι ℝ) => (K, (0 : densityTangent (n := n) →L[ℝ] ℝ))
  have htarget : Tendsto target (𝓝 C) (𝓝 (covarianceStationarityMap m hm H A θ κ S (C, 0))) := by
    rw [hf0]
    exact (continuousAt_id.prodMk continuousAt_const).tendsto
  let inv := hf.localInverse (covarianceStationarityMap m hm H A θ κ S)
    (covarianceStationarityEquiv m hm H A θ κ hθ hκ C S hS) (C, 0)
  have hinv : Tendsto (fun K => inv (target K)) (𝓝 C) (𝓝 (C, 0)) :=
    hf.localInverse_tendsto.comp htarget
  have hchart : Tendsto (fun K => densityChart S ((inv (target K)).2)) (𝓝 C) (𝓝 S) := by
    have hx : Tendsto (fun K => (inv (target K)).2) (𝓝 C) (𝓝 (0 : densityTangent (n := n))) :=
      continuous_snd.continuousAt.tendsto.comp hinv
    simpa only [densityChart_zero] using (hasStrictFDerivAt_densityChart S 0).continuousAt.tendsto.comp hx
  filter_upwards [eventually_real_posDef_of_posDef C hC,
    hchart.eventually (eventually_posDef_of_posDef S hS),
    htarget.eventually hf.eventually_right_inverse] with K hK hSK heq
  change RectangularRidgeCalculus.hermitianOptimizer H (covarianceKraus A K) m θ κ = densityChart S ((inv (target K)).2)
  apply RectangularRidgeCalculus.stationary_eq_optimizer H (covarianceKraus A K) m hm θ κ hθ hκ.le _ hSK
    ((densityChart_trace S _).trans ht)
  have hfirst := congrArg Prod.fst heq
  have hgrad := congrArg Prod.snd heq
  change (inv (target K)).1 = K at hfirst
  change covarianceGradientChart m hm H A θ κ S (inv (target K)) = 0 at hgrad
  have hg : covarianceGradientChart m hm H A θ κ S (K, (inv (target K)).2) = 0 := by
    have hp : (K, (inv (target K)).2) = inv (target K) := by
      apply Prod.ext
      · exact hfirst.symm
      · rfl
    rw [hp]
    exact hgrad
  rw [covarianceGradientChart_eq_densityGradientChart m hm H A hA θ κ K S _ hK hSK] at hg
  change -densityTangentRestriction
    (fderiv ℝ (RectangularRidgeCalculus.hermitianObjective H (covarianceKraus A K) m θ κ)
      (densityChart S ((inv (target K)).2))) = 0 at hg
  exact neg_eq_zero.mp hg

/-- Actual density optimizer smoothness in positive coefficient covariances. -/
theorem contDiffAt_covarianceDensityOptimizer (m : ℕ) (hm : 1 ≤ m) [Nonempty n]
    (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {θ κ : ℝ} (hθ : 0 < θ) (hκ : 0 < κ) (C : selfAdjoint (Matrix ι ι ℝ))
    (hC : (C : Matrix ι ι ℝ).PosDef) :
    ContDiffAt ℝ ∞ (fun K : selfAdjoint (Matrix ι ι ℝ) =>
      RectangularRidgeCalculus.hermitianOptimizer H (covarianceKraus A K) m θ κ) C := by
  let S := RectangularRidgeCalculus.hermitianOptimizer H (covarianceKraus A C) m θ κ
  have hS : (S : Matrix n n ℂ).PosDef := RectangularRidgeCalculus.hermitianOptimizer_posDef H (covarianceKraus A C) m hm θ κ hθ hκ
  have ht : realTrace (S : Matrix n n ℂ) = 1 := RectangularRidgeCalculus.hermitianOptimizer_trace H (covarianceKraus A C) m θ κ
  have hstat := RectangularRidgeCalculus.hermitianOptimizer_stationary H (covarianceKraus A C) m hm θ κ hθ hκ
  exact (contDiffAt_ridgeCovarianceResponseBranch m hm H A hA θ κ hθ hκ C S hC hS hstat).congr_of_eventuallyEq
    (eventually_covarianceOptimizer_eq_responseBranch m hm H A hA θ κ hθ hκ C S hC hS ht hstat)

/-- The original supremum potential on real symmetric coefficient covariances. -/
def hermitianOwnerPotential (m : ℕ) (hm : 1 ≤ m) (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ) (θ κ : ℝ)
    (C : selfAdjoint (Matrix ι ι ℝ)) : ℝ := RectangularRidgeCovarianceCalculus.ownerPotential m H A C θ κ

theorem ownerPotential_eq_chosenObjective (m : ℕ) (hm : 1 ≤ m) [Nonempty n]
    (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (θ κ : ℝ) (C : selfAdjoint (Matrix ι ι ℝ)) (hC : (C : Matrix ι ι ℝ).PosSemidef) :
    hermitianOwnerPotential m hm H A θ κ C =
      RectangularRidgeCovarianceCalculus.ownerObjective m H A C θ κ (RectangularRidgeCalculus.hermitianOptimizer H (covarianceKraus A C) m θ κ) := by
  change RectangularRidgeCovarianceCalculus.ownerPotential m H A C θ κ = _
  rw [RectangularRidgeCovarianceCalculus.ownerPotential_eq_densityPotential m H A hA hC,
    RectangularRidgeCovarianceCalculus.ownerObjective_eq_densityObjective m H A hA hC]
  exact RectangularRidgePotential.potential_eq_optimizer H (covarianceKraus A C) m θ κ

theorem contDiffAt_hermitianOwnerPotential (m : ℕ) (hm : 1 ≤ m) [Nonempty n]
    (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {θ κ : ℝ} (hθ : 0 < θ) (hκ : 0 < κ) (C : selfAdjoint (Matrix ι ι ℝ))
    (hC : (C : Matrix ι ι ℝ).PosDef) :
    ContDiffAt ℝ ∞ (hermitianOwnerPotential m hm H A θ κ) C := by
  have hs := contDiffAt_covarianceDensityOptimizer m hm H A hA hθ hκ C hC
  have ho := RectangularRidgeCovarianceCalculus.contDiffAt_jointOwnerObjective m H A hA θ κ C
    (RectangularRidgeCalculus.hermitianOptimizer H (covarianceKraus A C) m θ κ) hC
    (RectangularRidgeCalculus.hermitianOptimizer_posDef H (covarianceKraus A C) m hm θ κ hθ hκ)
  apply (ho.comp C (contDiffAt_id.prodMk hs)).congr_of_eventuallyEq
  filter_upwards [eventually_real_posDef_of_posDef C hC] with K hK
  exact ownerPotential_eq_chosenObjective m hm H A hA θ κ K hK.posSemidef

/-- The envelope derivative of the genuine covariance-dependent supremum. -/
theorem hasFDerivAt_hermitianOwnerPotential_covariance (m : ℕ) (hm : 1 ≤ m) [Nonempty n]
    (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {θ κ : ℝ} (hθ : 0 < θ) (hκ : 0 < κ) (C : selfAdjoint (Matrix ι ι ℝ))
    (hC : (C : Matrix ι ι ℝ).PosDef) :
    HasFDerivAt (hermitianOwnerPotential m hm H A θ κ)
      (covarianceDerivativeFunctional A C (RectangularRidgeCalculus.hermitianOptimizer H (covarianceKraus A C) m θ κ)) C := by
  let S := RectangularRidgeCalculus.hermitianOptimizer H (covarianceKraus A C) m θ κ
  have hd := ((contDiffAt_hermitianOwnerPotential m hm H A hA hθ hκ C hC).differentiableAt
    (by simp : (1 : WithTop ℕ∞) ≤ ∞)).hasFDerivAt
  have hf := (RectangularRidgeCovarianceCalculus.hasStrictFDerivAt_ownerObjective_covariance m H A hA θ κ C S hC
    (RectangularRidgeCalculus.hermitianOptimizer_posDef H (covarianceKraus A C) m hm θ κ hθ hκ)).hasFDerivAt
  have hmin : IsLocalMin (fun K : selfAdjoint (Matrix ι ι ℝ) =>
      hermitianOwnerPotential m hm H A θ κ K - RectangularRidgeCovarianceCalculus.ownerObjective m H A K θ κ S) C := by
    filter_upwards [eventually_real_posDef_of_posDef C hC] with K hK
    change hermitianOwnerPotential m hm H A θ κ C - RectangularRidgeCovarianceCalculus.ownerObjective m H A C θ κ S ≤
      hermitianOwnerPotential m hm H A θ κ K - RectangularRidgeCovarianceCalculus.ownerObjective m H A K θ κ S
    rw [ownerPotential_eq_chosenObjective m hm H A hA θ κ C hC.posSemidef]
    change RectangularRidgeCovarianceCalculus.ownerObjective m H A C θ κ S - RectangularRidgeCovarianceCalculus.ownerObjective m H A C θ κ S ≤ _
    rw [sub_self]
    apply sub_nonneg.mpr
    change RectangularRidgeCovarianceCalculus.ownerObjective m H A K θ κ S ≤ RectangularRidgeCovarianceCalculus.ownerPotential m H A K θ κ
    rw [RectangularRidgeCovarianceCalculus.ownerObjective_eq_densityObjective m H A hA hK.posSemidef,
      RectangularRidgeCovarianceCalculus.ownerPotential_eq_densityPotential m H A hA hK.posSemidef]
    exact RectangularRidgePotential.objective_le_potential H (covarianceKraus A K) m θ κ
      (S := RectangularRidgePotential.optimizer H (covarianceKraus A C) m θ κ)
      (RectangularRidgePotential.optimizer_mem H (covarianceKraus A C) m θ κ)
  have hz := hmin.hasFDerivAt_eq_zero (hd.sub hf)
  rwa [sub_eq_zero.mp hz] at hd

theorem hasStrictFDerivAt_hermitianOwnerPotential_covariance (m : ℕ) (hm : 1 ≤ m) [Nonempty n]
    (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {θ κ : ℝ} (hθ : 0 < θ) (hκ : 0 < κ) (C : selfAdjoint (Matrix ι ι ℝ))
    (hC : (C : Matrix ι ι ℝ).PosDef) :
    HasStrictFDerivAt (hermitianOwnerPotential m hm H A θ κ)
      (covarianceDerivativeFunctional A C (RectangularRidgeCalculus.hermitianOptimizer H (covarianceKraus A C) m θ κ)) C :=
  (contDiffAt_hermitianOwnerPotential m hm H A hA hθ hκ C hC).hasStrictFDerivAt'
    (hasFDerivAt_hermitianOwnerPotential_covariance m hm H A hA hθ hκ C hC) (by simp)

/-- Exact covariance response of the actual optimum, including singular physical sources. -/
theorem fderiv_hermitianOwnerPotential_covariance_apply (m : ℕ) (hm : 1 ≤ m) [Nonempty n]
    (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {θ κ : ℝ} (hθ : 0 < θ) (hκ : 0 < κ) (C ΔC : selfAdjoint (Matrix ι ι ℝ))
    (hC : (C : Matrix ι ι ℝ).PosDef) :
    fderiv ℝ (hermitianOwnerPotential m hm H A θ κ) C ΔC =
      realTrace (covarianceSupportTransport A C (RectangularRidgeCalculus.hermitianOptimizer H (covarianceKraus A C) m θ κ) *
        covarianceSource A ΔC (RectangularRidgeCalculus.hermitianOptimizer H (covarianceKraus A C) m θ κ)) := by
  rw [(hasFDerivAt_hermitianOwnerPotential_covariance m hm H A hA hθ hκ C hC).fderiv]
  exact covarianceDerivativeFunctional_apply A hA C ΔC _

end
end RectangularRidgeCovarianceResponse

noncomputable section
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n]
local instance ridgeOwnerCovarianceAPICStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance ridgeOwnerCovarianceAPISpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance
local instance ridgeOwnerCovarianceAPICoeffSpace : NormedSpace ℝ (selfAdjoint (Matrix ι ι ℝ)) := inferInstance

/-- The actual mixed owner supremum, in covariance coordinates. -/
def hermitianRidgeOwnerPotential (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ)
    (m : ℕ) (θ κ : ℝ) (C : selfAdjoint (Matrix ι ι ℝ)) : ℝ :=
  regularizedOwnerPotential H A C (RectangularRidgeCovarianceCalculus.regularizer m θ κ)

theorem contDiffAt_hermitianRidgeOwnerPotential [Nonempty n]
    (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (m : ℕ) (hm : 1 ≤ m) (θ κ : ℝ) (hθ : 0 < θ) (hκ : 0 < κ)
    (C : selfAdjoint (Matrix ι ι ℝ)) (hC : (C : Matrix ι ι ℝ).PosDef) :
    ContDiffAt ℝ ∞ (hermitianRidgeOwnerPotential H A m θ κ) C :=
  RectangularRidgeCovarianceResponse.contDiffAt_hermitianOwnerPotential m hm H A hA hθ hκ C hC

theorem hasFDerivAt_hermitianRidgeOwnerPotential_covariance [Nonempty n]
    (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (m : ℕ) (hm : 1 ≤ m) (θ κ : ℝ) (hθ : 0 < θ) (hκ : 0 < κ)
    (C : selfAdjoint (Matrix ι ι ℝ)) (hC : (C : Matrix ι ι ℝ).PosDef) :
    HasFDerivAt (hermitianRidgeOwnerPotential H A m θ κ)
      (covarianceDerivativeFunctional A C
        (RectangularRidgeCalculus.hermitianOptimizer H (covarianceKraus A C) m θ κ)) C :=
  RectangularRidgeCovarianceResponse.hasFDerivAt_hermitianOwnerPotential_covariance m hm H A hA hθ hκ C hC

theorem hasStrictFDerivAt_hermitianRidgeOwnerPotential_covariance [Nonempty n]
    (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (m : ℕ) (hm : 1 ≤ m) (θ κ : ℝ) (hθ : 0 < θ) (hκ : 0 < κ)
    (C : selfAdjoint (Matrix ι ι ℝ)) (hC : (C : Matrix ι ι ℝ).PosDef) :
    HasStrictFDerivAt (hermitianRidgeOwnerPotential H A m θ κ)
      (covarianceDerivativeFunctional A C
        (RectangularRidgeCalculus.hermitianOptimizer H (covarianceKraus A C) m θ κ)) C :=
  RectangularRidgeCovarianceResponse.hasStrictFDerivAt_hermitianOwnerPotential_covariance m hm H A hA hθ hκ C hC

theorem fderiv_hermitianRidgeOwnerPotential_covariance_apply [Nonempty n]
    (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (m : ℕ) (hm : 1 ≤ m) (θ κ : ℝ) (hθ : 0 < θ) (hκ : 0 < κ)
    (C ΔC : selfAdjoint (Matrix ι ι ℝ)) (hC : (C : Matrix ι ι ℝ).PosDef) :
    fderiv ℝ (hermitianRidgeOwnerPotential H A m θ κ) C ΔC =
      realTrace (covarianceSupportTransport A C
        (RectangularRidgeCalculus.hermitianOptimizer H (covarianceKraus A C) m θ κ) *
        covarianceSource A ΔC (RectangularRidgeCalculus.hermitianOptimizer H (covarianceKraus A C) m θ κ)) :=
  RectangularRidgeCovarianceResponse.fderiv_hermitianOwnerPotential_covariance_apply m hm H A hA hθ hκ C ΔC hC

end
end MatrixSpencer
