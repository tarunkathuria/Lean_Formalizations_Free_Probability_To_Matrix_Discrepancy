import MatrixSpencer.DyadicCovarianceResponse

/-! Joint smoothness of the actual optimized potential in center and covariance. -/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
open Filter Topology

namespace MatrixSpencer
namespace DyadicJointOwnerResponse
noncomputable section
set_option maxHeartbeats 800000
set_option linter.unusedVariables false
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n]
local instance dyadicJointOwnerResponseCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance dyadicJointOwnerResponsePhysicalGroup : NormedAddCommGroup (selfAdjoint (Matrix n n ℂ)) := inferInstance
local instance dyadicJointOwnerResponseCoeffGroup : NormedAddCommGroup (selfAdjoint (Matrix ι ι ℝ)) := inferInstance
local instance dyadicJointOwnerResponsePhysicalSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance
local instance dyadicJointOwnerResponseCoeffSpace : NormedSpace ℝ (selfAdjoint (Matrix ι ι ℝ)) := inferInstance
local instance dyadicJointOwnerResponsePhysicalFinite : FiniteDimensional ℝ (selfAdjoint (Matrix n n ℂ)) :=
  inferInstanceAs (FiniteDimensional ℝ (selfAdjoint.submodule ℝ (Matrix n n ℂ)))
local instance dyadicJointOwnerResponseCoeffFinite : FiniteDimensional ℝ (selfAdjoint (Matrix ι ι ℝ)) :=
  inferInstanceAs (FiniteDimensional ℝ (selfAdjoint.submodule ℝ (Matrix ι ι ℝ)))
local instance dyadicJointOwnerResponseCoeffComplete : CompleteSpace (selfAdjoint (Matrix ι ι ℝ)) :=
  FiniteDimensional.complete ℝ _
local instance dyadicJointOwnerResponseTangentGroup : NormedAddCommGroup (densityTangent (n := n)) := inferInstance
local instance dyadicJointOwnerResponseTangentSpace : NormedSpace ℝ (densityTangent (n := n)) := inferInstance
local instance dyadicJointOwnerResponseTangentFinite : FiniteDimensional ℝ (densityTangent (n := n)) := inferInstance
local instance dyadicJointOwnerResponseTangentComplete : CompleteSpace (densityTangent (n := n)) :=
  FiniteDimensional.complete ℝ _
local instance dyadicJointOwnerResponseDualGroup : NormedAddCommGroup (densityTangent (n := n) →L[ℝ] ℝ) := inferInstance
local instance dyadicJointOwnerResponseDualSpace : NormedSpace ℝ (densityTangent (n := n) →L[ℝ] ℝ) := inferInstance

local instance dyadicJointOwnerResponseJointGroup : NormedAddCommGroup
    (selfAdjoint (Matrix ι ι ℝ) × selfAdjoint (Matrix n n ℂ)) := inferInstance
local instance dyadicJointOwnerResponseJointSpace : NormedSpace ℝ
    (selfAdjoint (Matrix ι ι ℝ) × selfAdjoint (Matrix n n ℂ)) := inferInstance
local instance dyadicJointOwnerResponseJointMaps : NormedAddCommGroup
    (densityTangent (n := n) →L[ℝ] (selfAdjoint (Matrix ι ι ℝ) × selfAdjoint (Matrix n n ℂ))) := inferInstance

/-- Vary covariance directly and encode a center shift as a density dual forcing. -/
def jointOwnerResponseTarget (m : ℕ) (hm : 1 ≤ m) (H : selfAdjoint (Matrix n n ℂ))
    (P : selfAdjoint (Matrix n n ℂ) × selfAdjoint (Matrix ι ι ℝ)) :=
  (P.2, densityCenterFunctional (P.1 - H))

def jointOwnerResponseBranch (m : ℕ) (hm : 1 ≤ m)
    (H : selfAdjoint (Matrix n n ℂ)) (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (θ : ℝ) (hθ : 0 < θ) (C : selfAdjoint (Matrix ι ι ℝ))
    (S : selfAdjoint (Matrix n n ℂ)) (hC : (C : Matrix ι ι ℝ).PosDef)
    (hS : (S : Matrix n n ℂ).PosDef)
    (P : selfAdjoint (Matrix n n ℂ) × selfAdjoint (Matrix ι ι ℝ)) :
    selfAdjoint (Matrix n n ℂ) :=
  densityChart S ((DyadicCovarianceResponse.covarianceStationarityLocalInverse m hm (H : Matrix n n ℂ) A hA θ hθ C S hC hS
    (jointOwnerResponseTarget m hm H P)).2)

theorem contDiff_jointOwnerResponseTarget (m : ℕ) (hm : 1 ≤ m) (H : selfAdjoint (Matrix n n ℂ)) :
    ContDiff ℝ ∞ (jointOwnerResponseTarget m hm (ι := ι) H) :=
  contDiff_snd.prodMk ((densityCenterFunctional (n := n)).contDiff.comp
    (contDiff_fst.sub contDiff_const))

theorem contDiffAt_jointOwnerResponseBranch (m : ℕ) (hm : 1 ≤ m)
    (H : selfAdjoint (Matrix n n ℂ)) (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (θ : ℝ) (hθ : 0 < θ) (C : selfAdjoint (Matrix ι ι ℝ))
    (S : selfAdjoint (Matrix n n ℂ)) (hC : (C : Matrix ι ι ℝ).PosDef)
    (hS : (S : Matrix n n ℂ).PosDef)
    (hstat : densityTangentRestriction
      (fderiv ℝ (hermitianDyadicDensityObjective (H : Matrix n n ℂ) (covarianceKraus A C) m θ) S) = 0) :
    ContDiffAt ℝ ∞ (jointOwnerResponseBranch m hm H A hA θ hθ C S hC hS) (H, C) := by
  have hf := DyadicCovarianceResponse.hasStrictFDerivAt_covarianceStationarityMap m hm (H : Matrix n n ℂ) A hA θ hθ C S hC hS
  have hg := DyadicCovarianceResponse.contDiffAt_covarianceStationarityMap m hm (H : Matrix n n ℂ) A hA θ C S hC hS
  have hi : ContDiffAt ℝ ∞ (hf.localInverse _ _ (C, 0))
      (DyadicCovarianceResponse.covarianceStationarityMap m hm (H : Matrix n n ℂ) A θ S (C, 0)) := hg.to_localInverse hf.hasFDerivAt (by simp)
  rw [DyadicCovarianceResponse.covarianceStationarityMap_base m hm (H : Matrix n n ℂ) A hA θ C S hC hS hstat] at hi
  have hi' : ContDiffAt ℝ ∞ (hf.localInverse _ _ (C, 0)) (jointOwnerResponseTarget m hm H (H, C)) := by
    simpa only [jointOwnerResponseTarget, sub_self, map_zero] using hi
  have ht := hi'.comp (H, C) (contDiff_jointOwnerResponseTarget m hm H).contDiffAt
  exact contDiffAt_const.add ((densityTangent (n := n)).subtypeL.contDiff.contDiffAt.comp (H, C)
    (contDiffAt_snd.comp (H, C) ht))

/-- The same inverse branch is the actual joint center/covariance optimizer. -/
theorem eventually_jointOwnerOptimizer_eq_responseBranch (m : ℕ) (hm : 1 ≤ m) [Nonempty n]
    (H : selfAdjoint (Matrix n n ℂ)) (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (θ : ℝ) (hθ : 0 < θ) (C : selfAdjoint (Matrix ι ι ℝ))
    (S : selfAdjoint (Matrix n n ℂ)) (hC : (C : Matrix ι ι ℝ).PosDef)
    (hS : (S : Matrix n n ℂ).PosDef) (ht : realTrace (S : Matrix n n ℂ) = 1)
    (hstat : densityTangentRestriction
      (fderiv ℝ (hermitianDyadicDensityObjective (H : Matrix n n ℂ) (covarianceKraus A C) m θ) S) = 0) :
    ∀ᶠ P : selfAdjoint (Matrix n n ℂ) × selfAdjoint (Matrix ι ι ℝ) in 𝓝 (H, C),
      hermitianDyadicDensityOptimizer P.1 (covarianceKraus A P.2) m θ =
        jointOwnerResponseBranch m hm H A hA θ hθ C S hC hS P := by
  have hf := DyadicCovarianceResponse.hasStrictFDerivAt_covarianceStationarityMap m hm (H : Matrix n n ℂ) A hA θ hθ C S hC hS
  have hf0 := DyadicCovarianceResponse.covarianceStationarityMap_base m hm (H : Matrix n n ℂ) A hA θ C S hC hS hstat
  let target := jointOwnerResponseTarget m hm (ι := ι) H
  have htarget : Tendsto target (𝓝 (H, C)) (𝓝 (DyadicCovarianceResponse.covarianceStationarityMap m hm (H : Matrix n n ℂ) A θ S (C, 0))) := by
    rw [hf0]
    have hc := (contDiff_jointOwnerResponseTarget m hm (ι := ι) H).continuous.continuousAt.tendsto (x := (H, C))
    simpa only [jointOwnerResponseTarget, sub_self, map_zero] using hc
  let inv := hf.localInverse (DyadicCovarianceResponse.covarianceStationarityMap m hm (H : Matrix n n ℂ) A θ S)
    (DyadicCovarianceResponse.covarianceStationarityEquiv m hm (H : Matrix n n ℂ) A θ hθ C S hS) (C, 0)
  have hinv : Tendsto (fun P => inv (target P)) (𝓝 (H, C)) (𝓝 (C, 0)) :=
    hf.localInverse_tendsto.comp htarget
  have hchart : Tendsto (fun P => densityChart S ((inv (target P)).2)) (𝓝 (H, C)) (𝓝 S) := by
    have hx : Tendsto (fun P => (inv (target P)).2) (𝓝 (H, C)) (𝓝 (0 : densityTangent (n := n))) :=
      continuous_snd.continuousAt.tendsto.comp hinv
    simpa only [densityChart_zero] using (hasStrictFDerivAt_densityChart S 0).continuousAt.tendsto.comp hx
  have hcoeff : ∀ᶠ P : selfAdjoint (Matrix n n ℂ) × selfAdjoint (Matrix ι ι ℝ) in 𝓝 (H, C),
      (P.2 : Matrix ι ι ℝ).PosDef :=
    (continuous_snd.continuousAt (x := (H, C))).eventually (eventually_real_posDef_of_posDef C hC)
  filter_upwards [hcoeff, hchart.eventually (eventually_posDef_of_posDef S hS),
    htarget.eventually hf.eventually_right_inverse] with P hP hSP heq
  change hermitianDyadicDensityOptimizer P.1 (covarianceKraus A P.2) m θ = densityChart S ((inv (target P)).2)
  apply dyadicDensity_stationary_eq_optimizer P.1 (covarianceKraus A P.2) m hm θ hθ _ hSP
    ((densityChart_trace S _).trans ht)
  rw [dyadicDensity_stationarity_center_shift (H : Matrix n n ℂ) (P.1 : Matrix n n ℂ) (covarianceKraus A P.2) m θ _ hSP]
  have hfirst := congrArg Prod.fst heq
  have hgrad := congrArg Prod.snd heq
  change (inv (target P)).1 = P.2 at hfirst
  change DyadicCovarianceResponse.covarianceGradientChart m hm (H : Matrix n n ℂ) A θ S (inv (target P)) = densityCenterFunctional (P.1 - H) at hgrad
  have hg : DyadicCovarianceResponse.covarianceGradientChart m hm (H : Matrix n n ℂ) A θ S (P.2, (inv (target P)).2) =
      densityCenterFunctional (P.1 - H) := by
    have hp : (P.2, (inv (target P)).2) = inv (target P) := by
      apply Prod.ext
      · exact hfirst.symm
      · rfl
    rw [hp]
    exact hgrad
  rw [DyadicCovarianceResponse.covarianceGradientChart_eq_densityGradientChart m hm (H : Matrix n n ℂ) A hA θ P.2 S _ hP hSP] at hg
  change -densityTangentRestriction
    (fderiv ℝ (hermitianDyadicDensityObjective (H : Matrix n n ℂ) (covarianceKraus A P.2) m θ)
      (densityChart S ((inv (target P)).2))) = densityCenterFunctional (P.1 - H) at hg
  have hz := congrArg Neg.neg hg
  simp only [neg_neg] at hz
  exact add_eq_zero_iff_eq_neg.mpr hz

/-- Actual joint optimizer, using the already constructed attained density optimizer. -/
def jointOwnerDensityOptimizer (m : ℕ) (hm : 1 ≤ m) [Nonempty n] (A : ι → Matrix n n ℂ) (θ : ℝ)
    (P : selfAdjoint (Matrix n n ℂ) × selfAdjoint (Matrix ι ι ℝ)) : selfAdjoint (Matrix n n ℂ) :=
  hermitianDyadicDensityOptimizer P.1 (covarianceKraus A P.2) m θ

theorem contDiffAt_jointOwnerDensityOptimizer (m : ℕ) (hm : 1 ≤ m) [Nonempty n]
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) {θ : ℝ} (hθ : 0 < θ)
    (H : selfAdjoint (Matrix n n ℂ)) (C : selfAdjoint (Matrix ι ι ℝ))
    (hC : (C : Matrix ι ι ℝ).PosDef) :
    ContDiffAt ℝ ∞ (jointOwnerDensityOptimizer m hm A θ) (H, C) := by
  let S := hermitianDyadicDensityOptimizer (H : Matrix n n ℂ) (covarianceKraus A C) m θ
  have hS : (S : Matrix n n ℂ).PosDef := hermitianDyadicDensityOptimizer_posDef (H : Matrix n n ℂ) (covarianceKraus A C) m hm θ hθ
  have ht : realTrace (S : Matrix n n ℂ) = 1 := hermitianDyadicDensityOptimizer_trace (H : Matrix n n ℂ) (covarianceKraus A C) m θ
  have hstat := dyadicDensityOptimizer_stationary (H : Matrix n n ℂ) (covarianceKraus A C) m hm θ hθ
  exact (contDiffAt_jointOwnerResponseBranch m hm H A hA θ hθ C S hC hS hstat).congr_of_eventuallyEq
    (eventually_jointOwnerOptimizer_eq_responseBranch m hm H A hA θ hθ C S hC hS ht hstat)

/-- The genuine supremum potential in joint Hermitian-center and symmetric-covariance coordinates. -/
def jointHermitianOwnerPotential (m : ℕ) (hm : 1 ≤ m) (A : ι → Matrix n n ℂ) (θ : ℝ)
    (P : selfAdjoint (Matrix n n ℂ) × selfAdjoint (Matrix ι ι ℝ)) : ℝ :=
  DyadicCovarianceCalculus.ownerPotential m P.1 A P.2 θ

theorem contDiffAt_jointHermitianOwnerPotential (m : ℕ) (hm : 1 ≤ m) [Nonempty n]
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) {θ : ℝ} (hθ : 0 < θ)
    (H : selfAdjoint (Matrix n n ℂ)) (C : selfAdjoint (Matrix ι ι ℝ))
    (hC : (C : Matrix ι ι ℝ).PosDef) :
    ContDiffAt ℝ ∞ (jointHermitianOwnerPotential m hm A θ) (H, C) := by
  let S := jointOwnerDensityOptimizer m hm A θ (H, C)
  have hs := contDiffAt_jointOwnerDensityOptimizer m hm A hA hθ H C hC
  have hS : (S : Matrix n n ℂ).PosDef := hermitianDyadicDensityOptimizer_posDef (H : Matrix n n ℂ) (covarianceKraus A C) m hm θ hθ
  have hi := (hermitianInclusion (n := n)).contDiff.contDiffAt.comp (H, C) hs
  have hh : ContDiffAt ℝ ∞ (fun P : selfAdjoint (Matrix n n ℂ) × selfAdjoint (Matrix ι ι ℝ) =>
      (P.1 : Matrix n n ℂ)) (H, C) := hermitianInclusion.contDiff.contDiffAt.comp (H, C) contDiffAt_fst
  have hl := realTraceCLM.contDiff.contDiffAt.comp (H, C) (hh.mul hi)
  have hf := (contDiffAt_covarianceFidelity A hA C S hC hS).comp (H, C) (contDiffAt_snd.prodMk hs)
  have ht := ContDiffAt.comp (g := dyadicTsallisPotential m θ) (f := jointOwnerDensityOptimizer m hm A θ) (H, C)
    (contDiffAt_dyadicTsallisPotential m θ S hS) hs
  apply ((hl.add hf).add ht).congr_of_eventuallyEq
  filter_upwards [(continuous_snd.continuousAt (x := (H, C))).eventually (eventually_real_posDef_of_posDef C hC)] with P hP
  exact DyadicCovarianceResponse.ownerPotential_eq_chosenObjective m hm (P.1 : Matrix n n ℂ) A hA θ P.2 hP.posSemidef

/-- Joint optimizer smoothness throughout the positive coefficient cone. -/
theorem contDiffOn_jointOwnerDensityOptimizer (m : ℕ) (hm : 1 ≤ m) [Nonempty n]
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) {θ : ℝ} (hθ : 0 < θ) :
    ContDiffOn ℝ ∞ (jointOwnerDensityOptimizer m hm A θ)
      {P | (P.2 : Matrix ι ι ℝ).PosDef} := by
  intro P hP
  exact (contDiffAt_jointOwnerDensityOptimizer m hm A hA hθ P.1 P.2 hP).contDiffWithinAt

/-- Joint smoothness on the full center space times the positive coefficient cone. -/
theorem contDiffOn_jointHermitianOwnerPotential (m : ℕ) (hm : 1 ≤ m) [Nonempty n]
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) {θ : ℝ} (hθ : 0 < θ) :
    ContDiffOn ℝ ∞ (jointHermitianOwnerPotential m hm A θ)
      {P | (P.2 : Matrix ι ι ℝ).PosDef} := by
  intro P hP
  exact (contDiffAt_jointHermitianOwnerPotential m hm A hA hθ P.1 P.2 hP).contDiffWithinAt

end
end DyadicJointOwnerResponse

noncomputable section
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n]
local instance dyadicJointOwnerAPICStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance dyadicJointOwnerAPISpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance
local instance dyadicJointOwnerAPICoeffSpace : NormedSpace ℝ (selfAdjoint (Matrix ι ι ℝ)) := inferInstance

/-- The actual dyadic supremum in joint center/covariance coordinates. -/
def jointHermitianDyadicOwnerPotential (A : ι → Matrix n n ℂ) (m : ℕ) (θ : ℝ)
    (P : selfAdjoint (Matrix n n ℂ) × selfAdjoint (Matrix ι ι ℝ)) : ℝ :=
  regularizedOwnerPotential P.1 A P.2 (dyadicTsallisRegularizer m θ)

def jointDyadicOwnerDensityOptimizer [Nonempty n] (A : ι → Matrix n n ℂ) (m : ℕ) (θ : ℝ)
    (P : selfAdjoint (Matrix n n ℂ) × selfAdjoint (Matrix ι ι ℝ)) :
    selfAdjoint (Matrix n n ℂ) :=
  hermitianDyadicDensityOptimizer P.1 (covarianceKraus A P.2) m θ

theorem contDiffAt_jointDyadicOwnerDensityOptimizer [Nonempty n]
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (hθ : 0 < θ)
    (H : selfAdjoint (Matrix n n ℂ)) (C : selfAdjoint (Matrix ι ι ℝ))
    (hC : (C : Matrix ι ι ℝ).PosDef) :
    ContDiffAt ℝ ∞ (jointDyadicOwnerDensityOptimizer A m θ) (H, C) :=
  DyadicJointOwnerResponse.contDiffAt_jointOwnerDensityOptimizer m hm A hA hθ H C hC

theorem contDiffAt_jointHermitianDyadicOwnerPotential [Nonempty n]
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (hθ : 0 < θ)
    (H : selfAdjoint (Matrix n n ℂ)) (C : selfAdjoint (Matrix ι ι ℝ))
    (hC : (C : Matrix ι ι ℝ).PosDef) :
    ContDiffAt ℝ ∞ (jointHermitianDyadicOwnerPotential A m θ) (H, C) :=
  DyadicJointOwnerResponse.contDiffAt_jointHermitianOwnerPotential m hm A hA hθ H C hC

theorem contDiffOn_jointDyadicOwnerDensityOptimizer [Nonempty n]
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (hθ : 0 < θ) :
    ContDiffOn ℝ ∞ (jointDyadicOwnerDensityOptimizer A m θ)
      {P | (P.2 : Matrix ι ι ℝ).PosDef} :=
  DyadicJointOwnerResponse.contDiffOn_jointOwnerDensityOptimizer m hm A hA hθ

theorem contDiffOn_jointHermitianDyadicOwnerPotential [Nonempty n]
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (hθ : 0 < θ) :
    ContDiffOn ℝ ∞ (jointHermitianDyadicOwnerPotential A m θ)
      {P | (P.2 : Matrix ι ι ℝ).PosDef} :=
  DyadicJointOwnerResponse.contDiffOn_jointHermitianOwnerPotential m hm A hA hθ

end
end MatrixSpencer
