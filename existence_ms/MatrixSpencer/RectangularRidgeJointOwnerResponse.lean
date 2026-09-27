import MatrixSpencer.RectangularRidgeCovarianceResponse

/-! Joint smoothness of the actual optimized potential in center and covariance. -/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
open Filter Topology

namespace MatrixSpencer
namespace RectangularRidgeJointOwnerResponse
noncomputable section
set_option maxHeartbeats 300000
attribute [local irreducible] RectangularRidgePotential.optimizer
set_option linter.unusedVariables false
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n]
local instance ridgeJointOwnerResponseCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance ridgeJointOwnerResponsePhysicalGroup : NormedAddCommGroup (selfAdjoint (Matrix n n ℂ)) := inferInstance
local instance ridgeJointOwnerResponseCoeffGroup : NormedAddCommGroup (selfAdjoint (Matrix ι ι ℝ)) := inferInstance
local instance ridgeJointOwnerResponsePhysicalSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance
local instance ridgeJointOwnerResponseCoeffSpace : NormedSpace ℝ (selfAdjoint (Matrix ι ι ℝ)) := inferInstance
local instance ridgeJointOwnerResponsePhysicalFinite : FiniteDimensional ℝ (selfAdjoint (Matrix n n ℂ)) :=
  inferInstanceAs (FiniteDimensional ℝ (selfAdjoint.submodule ℝ (Matrix n n ℂ)))
local instance ridgeJointOwnerResponseCoeffFinite : FiniteDimensional ℝ (selfAdjoint (Matrix ι ι ℝ)) :=
  inferInstanceAs (FiniteDimensional ℝ (selfAdjoint.submodule ℝ (Matrix ι ι ℝ)))
local instance ridgeJointOwnerResponseCoeffComplete : CompleteSpace (selfAdjoint (Matrix ι ι ℝ)) :=
  FiniteDimensional.complete ℝ _
local instance ridgeJointOwnerResponseTangentGroup : NormedAddCommGroup (densityTangent (n := n)) := inferInstance
local instance ridgeJointOwnerResponseTangentSpace : NormedSpace ℝ (densityTangent (n := n)) := inferInstance
local instance ridgeJointOwnerResponseTangentFinite : FiniteDimensional ℝ (densityTangent (n := n)) := inferInstance
local instance ridgeJointOwnerResponseTangentComplete : CompleteSpace (densityTangent (n := n)) :=
  FiniteDimensional.complete ℝ _
local instance ridgeJointOwnerResponseDualGroup : NormedAddCommGroup (densityTangent (n := n) →L[ℝ] ℝ) := inferInstance
local instance ridgeJointOwnerResponseDualSpace : NormedSpace ℝ (densityTangent (n := n) →L[ℝ] ℝ) := inferInstance

local instance ridgeJointOwnerResponseJointGroup : NormedAddCommGroup
    (selfAdjoint (Matrix ι ι ℝ) × selfAdjoint (Matrix n n ℂ)) := inferInstance
local instance ridgeJointOwnerResponseJointSpace : NormedSpace ℝ
    (selfAdjoint (Matrix ι ι ℝ) × selfAdjoint (Matrix n n ℂ)) := inferInstance
local instance ridgeJointOwnerResponseJointMaps : NormedAddCommGroup
    (densityTangent (n := n) →L[ℝ] (selfAdjoint (Matrix ι ι ℝ) × selfAdjoint (Matrix n n ℂ))) := inferInstance

/-- Vary covariance directly and encode a center shift as a density dual forcing. -/
def jointOwnerResponseTarget (m : ℕ) (hm : 1 ≤ m) (H : selfAdjoint (Matrix n n ℂ))
    (P : selfAdjoint (Matrix n n ℂ) × selfAdjoint (Matrix ι ι ℝ)) :=
  (P.2, densityCenterFunctional (P.1 - H))

def jointOwnerResponseBranch (m : ℕ) (hm : 1 ≤ m)
    (H : selfAdjoint (Matrix n n ℂ)) (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (θ κ : ℝ) (hθ : 0 < θ) (hκ : 0 < κ) (C : selfAdjoint (Matrix ι ι ℝ))
    (S : selfAdjoint (Matrix n n ℂ)) (hC : (C : Matrix ι ι ℝ).PosDef)
    (hS : (S : Matrix n n ℂ).PosDef)
    (P : selfAdjoint (Matrix n n ℂ) × selfAdjoint (Matrix ι ι ℝ)) :
    selfAdjoint (Matrix n n ℂ) :=
  densityChart S ((RectangularRidgeCovarianceResponse.covarianceStationarityLocalInverse m hm (H : Matrix n n ℂ) A hA θ κ hθ hκ C S hC hS
    (jointOwnerResponseTarget m hm H P)).2)

theorem contDiff_jointOwnerResponseTarget (m : ℕ) (hm : 1 ≤ m) (H : selfAdjoint (Matrix n n ℂ)) :
    ContDiff ℝ ∞ (jointOwnerResponseTarget m hm (ι := ι) H) :=
  contDiff_snd.prodMk ((densityCenterFunctional (n := n)).contDiff.comp
    (contDiff_fst.sub contDiff_const))

set_option maxHeartbeats 800000 in
theorem contDiffAt_jointOwnerResponseBranch (m : ℕ) (hm : 1 ≤ m)
    (H : selfAdjoint (Matrix n n ℂ)) (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (θ κ : ℝ) (hθ : 0 < θ) (hκ : 0 < κ) (C : selfAdjoint (Matrix ι ι ℝ))
    (S : selfAdjoint (Matrix n n ℂ)) (hC : (C : Matrix ι ι ℝ).PosDef)
    (hS : (S : Matrix n n ℂ).PosDef)
    (hstat : densityTangentRestriction
      (fderiv ℝ (RectangularRidgeCalculus.hermitianObjective (H : Matrix n n ℂ) (covarianceKraus A C) m θ κ) S) = 0) :
    ContDiffAt ℝ ∞ (jointOwnerResponseBranch m hm H A hA θ κ hθ hκ C S hC hS) (H, C) := by
  have hf := RectangularRidgeCovarianceResponse.hasStrictFDerivAt_covarianceStationarityMap m hm (H : Matrix n n ℂ) A hA θ κ hθ hκ C S hC hS
  have hg := RectangularRidgeCovarianceResponse.contDiffAt_covarianceStationarityMap m hm (H : Matrix n n ℂ) A hA θ κ C S hC hS
  have hi : ContDiffAt ℝ ∞ (hf.localInverse _ _ (C, 0))
      (RectangularRidgeCovarianceResponse.covarianceStationarityMap m hm (H : Matrix n n ℂ) A θ κ S (C, 0)) := hg.to_localInverse hf.hasFDerivAt (by simp)
  rw [RectangularRidgeCovarianceResponse.covarianceStationarityMap_base m hm (H : Matrix n n ℂ) A hA θ κ C S hC hS hstat] at hi
  have hi' : ContDiffAt ℝ ∞ (hf.localInverse _ _ (C, 0)) (jointOwnerResponseTarget m hm H (H, C)) := by
    simpa only [jointOwnerResponseTarget, sub_self, map_zero] using hi
  have ht := hi'.comp (H, C) (contDiff_jointOwnerResponseTarget m hm H).contDiffAt
  exact contDiffAt_const.add ((densityTangent (n := n)).subtypeL.contDiff.contDiffAt.comp (H, C)
    (contDiffAt_snd.comp (H, C) ht))

/-- The same inverse branch is the actual joint center/covariance optimizer. -/
theorem eventually_jointOwnerOptimizer_eq_responseBranch (m : ℕ) (hm : 1 ≤ m) [Nonempty n]
    (H : selfAdjoint (Matrix n n ℂ)) (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (θ κ : ℝ) (hθ : 0 < θ) (hκ : 0 < κ) (C : selfAdjoint (Matrix ι ι ℝ))
    (S : selfAdjoint (Matrix n n ℂ)) (hC : (C : Matrix ι ι ℝ).PosDef)
    (hS : (S : Matrix n n ℂ).PosDef) (ht : realTrace (S : Matrix n n ℂ) = 1)
    (hstat : densityTangentRestriction
      (fderiv ℝ (RectangularRidgeCalculus.hermitianObjective (H : Matrix n n ℂ) (covarianceKraus A C) m θ κ) S) = 0) :
    ∀ᶠ P : selfAdjoint (Matrix n n ℂ) × selfAdjoint (Matrix ι ι ℝ) in 𝓝 (H, C),
      RectangularRidgeCalculus.hermitianOptimizer (P.1 : Matrix n n ℂ) (covarianceKraus A P.2) m θ κ =
        jointOwnerResponseBranch m hm H A hA θ κ hθ hκ C S hC hS P := by
  have hf := RectangularRidgeCovarianceResponse.hasStrictFDerivAt_covarianceStationarityMap m hm (H : Matrix n n ℂ) A hA θ κ hθ hκ C S hC hS
  have hf0 := RectangularRidgeCovarianceResponse.covarianceStationarityMap_base m hm (H : Matrix n n ℂ) A hA θ κ C S hC hS hstat
  let target := jointOwnerResponseTarget m hm (ι := ι) H
  have htarget : Tendsto target (𝓝 (H, C)) (𝓝 (RectangularRidgeCovarianceResponse.covarianceStationarityMap m hm (H : Matrix n n ℂ) A θ κ S (C, 0))) := by
    rw [hf0]
    have hc := (contDiff_jointOwnerResponseTarget m hm (ι := ι) H).continuous.continuousAt.tendsto (x := (H, C))
    simpa only [jointOwnerResponseTarget, sub_self, map_zero] using hc
  let inv := hf.localInverse (RectangularRidgeCovarianceResponse.covarianceStationarityMap m hm (H : Matrix n n ℂ) A θ κ S)
    (RectangularRidgeCovarianceResponse.covarianceStationarityEquiv m hm (H : Matrix n n ℂ) A θ κ hθ hκ C S hS) (C, 0)
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
  change RectangularRidgeCalculus.hermitianOptimizer (P.1 : Matrix n n ℂ) (covarianceKraus A P.2) m θ κ = densityChart S ((inv (target P)).2)
  apply RectangularRidgeCalculus.stationary_eq_optimizer (P.1 : Matrix n n ℂ) (covarianceKraus A P.2) m hm θ κ hθ hκ.le _ hSP
    ((densityChart_trace S _).trans ht)
  rw [RectangularRidgeCalculus.stationarity_center_shift (H : Matrix n n ℂ) (P.1 : Matrix n n ℂ) (covarianceKraus A P.2) m θ κ _ hSP]
  have hfirst := congrArg Prod.fst heq
  have hgrad := congrArg Prod.snd heq
  change (inv (target P)).1 = P.2 at hfirst
  change RectangularRidgeCovarianceResponse.covarianceGradientChart m hm (H : Matrix n n ℂ) A θ κ S (inv (target P)) = densityCenterFunctional (P.1 - H) at hgrad
  have hg : RectangularRidgeCovarianceResponse.covarianceGradientChart m hm (H : Matrix n n ℂ) A θ κ S (P.2, (inv (target P)).2) =
      densityCenterFunctional (P.1 - H) := by
    have hp : (P.2, (inv (target P)).2) = inv (target P) := by
      apply Prod.ext
      · exact hfirst.symm
      · rfl
    rw [hp]
    exact hgrad
  rw [RectangularRidgeCovarianceResponse.covarianceGradientChart_eq_densityGradientChart m hm (H : Matrix n n ℂ) A hA θ κ P.2 S _ hP hSP] at hg
  change -densityTangentRestriction
    (fderiv ℝ (RectangularRidgeCalculus.hermitianObjective (H : Matrix n n ℂ) (covarianceKraus A P.2) m θ κ)
      (densityChart S ((inv (target P)).2))) = densityCenterFunctional (P.1 - H) at hg
  have hz := congrArg Neg.neg hg
  simp only [neg_neg] at hz
  exact add_eq_zero_iff_eq_neg.mpr hz

/-- Actual joint optimizer, using the already constructed attained density optimizer. -/
def jointOwnerDensityOptimizer (m : ℕ) (hm : 1 ≤ m) [Nonempty n] (A : ι → Matrix n n ℂ) (θ κ : ℝ)
    (P : selfAdjoint (Matrix n n ℂ) × selfAdjoint (Matrix ι ι ℝ)) : selfAdjoint (Matrix n n ℂ) :=
  RectangularRidgeCalculus.hermitianOptimizer (P.1 : Matrix n n ℂ) (covarianceKraus A P.2) m θ κ

theorem contDiffAt_jointOwnerDensityOptimizer (m : ℕ) (hm : 1 ≤ m) [Nonempty n]
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) {θ κ : ℝ} (hθ : 0 < θ) (hκ : 0 < κ)
    (H : selfAdjoint (Matrix n n ℂ)) (C : selfAdjoint (Matrix ι ι ℝ))
    (hC : (C : Matrix ι ι ℝ).PosDef) :
    ContDiffAt ℝ ∞ (jointOwnerDensityOptimizer m hm A θ κ) (H, C) := by
  let S := RectangularRidgeCalculus.hermitianOptimizer (H : Matrix n n ℂ) (covarianceKraus A C) m θ κ
  have hS : (S : Matrix n n ℂ).PosDef := RectangularRidgeCalculus.hermitianOptimizer_posDef (H : Matrix n n ℂ) (covarianceKraus A C) m hm θ κ hθ hκ
  have ht : realTrace (S : Matrix n n ℂ) = 1 := RectangularRidgeCalculus.hermitianOptimizer_trace (H : Matrix n n ℂ) (covarianceKraus A C) m θ κ
  have hstat := RectangularRidgeCalculus.hermitianOptimizer_stationary (H : Matrix n n ℂ) (covarianceKraus A C) m hm θ κ hθ hκ
  exact (contDiffAt_jointOwnerResponseBranch m hm H A hA θ κ hθ hκ C S hC hS hstat).congr_of_eventuallyEq
    (eventually_jointOwnerOptimizer_eq_responseBranch m hm H A hA θ κ hθ hκ C S hC hS ht hstat)

/-- The genuine supremum potential in joint Hermitian-center and symmetric-covariance coordinates. -/
def jointHermitianOwnerPotential (m : ℕ) (hm : 1 ≤ m) (A : ι → Matrix n n ℂ) (θ κ : ℝ)
    (P : selfAdjoint (Matrix n n ℂ) × selfAdjoint (Matrix ι ι ℝ)) : ℝ :=
  RectangularRidgeCovarianceCalculus.ownerPotential m P.1 A P.2 θ κ

theorem contDiffAt_jointHermitianOwnerPotential (m : ℕ) (hm : 1 ≤ m) [Nonempty n]
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) {θ κ : ℝ} (hθ : 0 < θ) (hκ : 0 < κ)
    (H : selfAdjoint (Matrix n n ℂ)) (C : selfAdjoint (Matrix ι ι ℝ))
    (hC : (C : Matrix ι ι ℝ).PosDef) :
    ContDiffAt ℝ ∞ (jointHermitianOwnerPotential m hm A θ κ) (H, C) := by
  let S := jointOwnerDensityOptimizer m hm A θ κ (H, C)
  have hs := contDiffAt_jointOwnerDensityOptimizer m hm A hA hθ hκ H C hC
  have hS : (S : Matrix n n ℂ).PosDef := RectangularRidgeCalculus.hermitianOptimizer_posDef (H : Matrix n n ℂ) (covarianceKraus A C) m hm θ κ hθ hκ
  have hi := (hermitianInclusion (n := n)).contDiff.contDiffAt.comp (H, C) hs
  have hh : ContDiffAt ℝ ∞ (fun P : selfAdjoint (Matrix n n ℂ) × selfAdjoint (Matrix ι ι ℝ) =>
      (P.1 : Matrix n n ℂ)) (H, C) := hermitianInclusion.contDiff.contDiffAt.comp (H, C) contDiffAt_fst
  have hl := realTraceCLM.contDiff.contDiffAt.comp (H, C) (hh.mul hi)
  have hf := (contDiffAt_covarianceFidelity A hA C S hC hS).comp (H, C) (contDiffAt_snd.prodMk hs)
  have ht := ContDiffAt.comp (g := fun S => dyadicTsallisPotential m θ S + tsallisPotential κ S)
    (f := jointOwnerDensityOptimizer m hm A θ κ) (H, C)
    ((contDiffAt_dyadicTsallisPotential m θ S hS).add (contDiffAt_tsallisPotential κ S hS)) hs
  apply ((hl.add hf).add ht).congr_of_eventuallyEq
  filter_upwards [(continuous_snd.continuousAt (x := (H, C))).eventually (eventually_real_posDef_of_posDef C hC)] with P hP
  exact RectangularRidgeCovarianceResponse.ownerPotential_eq_chosenObjective m hm (P.1 : Matrix n n ℂ) A hA θ κ P.2 hP.posSemidef

/-- Joint optimizer smoothness throughout the positive coefficient cone. -/
theorem contDiffOn_jointOwnerDensityOptimizer (m : ℕ) (hm : 1 ≤ m) [Nonempty n]
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) {θ κ : ℝ} (hθ : 0 < θ) (hκ : 0 < κ) :
    ContDiffOn ℝ ∞ (jointOwnerDensityOptimizer m hm A θ κ)
      {P | (P.2 : Matrix ι ι ℝ).PosDef} := by
  intro P hP
  exact (contDiffAt_jointOwnerDensityOptimizer m hm A hA hθ hκ P.1 P.2 hP).contDiffWithinAt

/-- Joint smoothness on the full center space times the positive coefficient cone. -/
theorem contDiffOn_jointHermitianOwnerPotential (m : ℕ) (hm : 1 ≤ m) [Nonempty n]
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) {θ κ : ℝ} (hθ : 0 < θ) (hκ : 0 < κ) :
    ContDiffOn ℝ ∞ (jointHermitianOwnerPotential m hm A θ κ)
      {P | (P.2 : Matrix ι ι ℝ).PosDef} := by
  intro P hP
  exact (contDiffAt_jointHermitianOwnerPotential m hm A hA hθ hκ P.1 P.2 hP).contDiffWithinAt

end
end RectangularRidgeJointOwnerResponse

noncomputable section
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n]
local instance ridgeJointOwnerAPICStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance ridgeJointOwnerAPISpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance
local instance ridgeJointOwnerAPICoeffSpace : NormedSpace ℝ (selfAdjoint (Matrix ι ι ℝ)) := inferInstance

/-- The actual mixed supremum in joint center/covariance coordinates. -/
def jointHermitianRidgeOwnerPotential (A : ι → Matrix n n ℂ) (m : ℕ) (θ κ : ℝ)
    (P : selfAdjoint (Matrix n n ℂ) × selfAdjoint (Matrix ι ι ℝ)) : ℝ :=
  regularizedOwnerPotential P.1 A P.2 (RectangularRidgeCovarianceCalculus.regularizer m θ κ)

def jointRidgeOwnerDensityOptimizer [Nonempty n] (A : ι → Matrix n n ℂ) (m : ℕ) (θ κ : ℝ)
    (P : selfAdjoint (Matrix n n ℂ) × selfAdjoint (Matrix ι ι ℝ)) :
    selfAdjoint (Matrix n n ℂ) :=
  RectangularRidgeCalculus.hermitianOptimizer (P.1 : Matrix n n ℂ) (covarianceKraus A P.2) m θ κ

theorem contDiffAt_jointRidgeOwnerDensityOptimizer [Nonempty n]
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (m : ℕ) (hm : 1 ≤ m) (θ κ : ℝ) (hθ : 0 < θ) (hκ : 0 < κ)
    (H : selfAdjoint (Matrix n n ℂ)) (C : selfAdjoint (Matrix ι ι ℝ))
    (hC : (C : Matrix ι ι ℝ).PosDef) :
    ContDiffAt ℝ ∞ (jointRidgeOwnerDensityOptimizer A m θ κ) (H, C) :=
  RectangularRidgeJointOwnerResponse.contDiffAt_jointOwnerDensityOptimizer m hm A hA hθ hκ H C hC

theorem contDiffAt_jointHermitianRidgeOwnerPotential [Nonempty n]
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (m : ℕ) (hm : 1 ≤ m) (θ κ : ℝ) (hθ : 0 < θ) (hκ : 0 < κ)
    (H : selfAdjoint (Matrix n n ℂ)) (C : selfAdjoint (Matrix ι ι ℝ))
    (hC : (C : Matrix ι ι ℝ).PosDef) :
    ContDiffAt ℝ ∞ (jointHermitianRidgeOwnerPotential A m θ κ) (H, C) :=
  RectangularRidgeJointOwnerResponse.contDiffAt_jointHermitianOwnerPotential m hm A hA hθ hκ H C hC

theorem contDiffOn_jointRidgeOwnerDensityOptimizer [Nonempty n]
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (m : ℕ) (hm : 1 ≤ m) (θ κ : ℝ) (hθ : 0 < θ) (hκ : 0 < κ) :
    ContDiffOn ℝ ∞ (jointRidgeOwnerDensityOptimizer A m θ κ)
      {P | (P.2 : Matrix ι ι ℝ).PosDef} :=
  RectangularRidgeJointOwnerResponse.contDiffOn_jointOwnerDensityOptimizer m hm A hA hθ hκ

theorem contDiffOn_jointHermitianRidgeOwnerPotential [Nonempty n]
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (m : ℕ) (hm : 1 ≤ m) (θ κ : ℝ) (hθ : 0 < θ) (hκ : 0 < κ) :
    ContDiffOn ℝ ∞ (jointHermitianRidgeOwnerPotential A m θ κ)
      {P | (P.2 : Matrix ι ι ℝ).PosDef} :=
  RectangularRidgeJointOwnerResponse.contDiffOn_jointHermitianOwnerPotential m hm A hA hθ hκ

end
end MatrixSpencer
