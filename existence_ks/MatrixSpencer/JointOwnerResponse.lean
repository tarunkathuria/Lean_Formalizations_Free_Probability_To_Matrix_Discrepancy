import MatrixSpencer.CovarianceResponse

/-! Joint smoothness of the actual optimized potential in center and covariance. -/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
open Filter Topology

namespace MatrixSpencer
noncomputable section
set_option maxHeartbeats 800000
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n]
local instance jointOwnerResponseCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance jointOwnerResponsePhysicalGroup : NormedAddCommGroup (selfAdjoint (Matrix n n ℂ)) := inferInstance
local instance jointOwnerResponseCoeffGroup : NormedAddCommGroup (selfAdjoint (Matrix ι ι ℝ)) := inferInstance
local instance jointOwnerResponsePhysicalSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance
local instance jointOwnerResponseCoeffSpace : NormedSpace ℝ (selfAdjoint (Matrix ι ι ℝ)) := inferInstance
local instance jointOwnerResponsePhysicalFinite : FiniteDimensional ℝ (selfAdjoint (Matrix n n ℂ)) :=
  inferInstanceAs (FiniteDimensional ℝ (selfAdjoint.submodule ℝ (Matrix n n ℂ)))
local instance jointOwnerResponseCoeffFinite : FiniteDimensional ℝ (selfAdjoint (Matrix ι ι ℝ)) :=
  inferInstanceAs (FiniteDimensional ℝ (selfAdjoint.submodule ℝ (Matrix ι ι ℝ)))
local instance jointOwnerResponseCoeffComplete : CompleteSpace (selfAdjoint (Matrix ι ι ℝ)) :=
  FiniteDimensional.complete ℝ _
local instance jointOwnerResponseTangentGroup : NormedAddCommGroup (densityTangent (n := n)) := inferInstance
local instance jointOwnerResponseTangentSpace : NormedSpace ℝ (densityTangent (n := n)) := inferInstance
local instance jointOwnerResponseTangentFinite : FiniteDimensional ℝ (densityTangent (n := n)) := inferInstance
local instance jointOwnerResponseTangentComplete : CompleteSpace (densityTangent (n := n)) :=
  FiniteDimensional.complete ℝ _
local instance jointOwnerResponseDualGroup : NormedAddCommGroup (densityTangent (n := n) →L[ℝ] ℝ) := inferInstance
local instance jointOwnerResponseDualSpace : NormedSpace ℝ (densityTangent (n := n) →L[ℝ] ℝ) := inferInstance

local instance jointOwnerResponseJointGroup : NormedAddCommGroup
    (selfAdjoint (Matrix ι ι ℝ) × selfAdjoint (Matrix n n ℂ)) := inferInstance
local instance jointOwnerResponseJointSpace : NormedSpace ℝ
    (selfAdjoint (Matrix ι ι ℝ) × selfAdjoint (Matrix n n ℂ)) := inferInstance
local instance jointOwnerResponseJointMaps : NormedAddCommGroup
    (densityTangent (n := n) →L[ℝ] (selfAdjoint (Matrix ι ι ℝ) × selfAdjoint (Matrix n n ℂ))) := inferInstance

/-- Vary covariance directly and encode a center shift as a density dual forcing. -/
def jointOwnerResponseTarget (H : selfAdjoint (Matrix n n ℂ))
    (P : selfAdjoint (Matrix n n ℂ) × selfAdjoint (Matrix ι ι ℝ)) :=
  (P.2, densityCenterFunctional (P.1 - H))

def jointOwnerResponseBranch
    (H : selfAdjoint (Matrix n n ℂ)) (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (θ : ℝ) (hθ : 0 < θ) (C : selfAdjoint (Matrix ι ι ℝ))
    (S : selfAdjoint (Matrix n n ℂ)) (hC : (C : Matrix ι ι ℝ).PosDef)
    (hS : (S : Matrix n n ℂ).PosDef)
    (P : selfAdjoint (Matrix n n ℂ) × selfAdjoint (Matrix ι ι ℝ)) :
    selfAdjoint (Matrix n n ℂ) :=
  densityChart S ((covarianceStationarityLocalInverse (H : Matrix n n ℂ) A hA θ hθ C S hC hS
    (jointOwnerResponseTarget H P)).2)

theorem contDiff_jointOwnerResponseTarget (H : selfAdjoint (Matrix n n ℂ)) :
    ContDiff ℝ ∞ (jointOwnerResponseTarget (ι := ι) H) :=
  contDiff_snd.prodMk ((densityCenterFunctional (n := n)).contDiff.comp
    (contDiff_fst.sub contDiff_const))

theorem contDiffAt_jointOwnerResponseBranch
    (H : selfAdjoint (Matrix n n ℂ)) (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (θ : ℝ) (hθ : 0 < θ) (C : selfAdjoint (Matrix ι ι ℝ))
    (S : selfAdjoint (Matrix n n ℂ)) (hC : (C : Matrix ι ι ℝ).PosDef)
    (hS : (S : Matrix n n ℂ).PosDef)
    (hstat : densityTangentRestriction
      (fderiv ℝ (hermitianDensityObjective (H : Matrix n n ℂ) (covarianceKraus A C) θ) S) = 0) :
    ContDiffAt ℝ ∞ (jointOwnerResponseBranch H A hA θ hθ C S hC hS) (H, C) := by
  have hf := hasStrictFDerivAt_covarianceStationarityMap (H : Matrix n n ℂ) A hA θ hθ C S hC hS
  have hg := contDiffAt_covarianceStationarityMap (H : Matrix n n ℂ) A hA θ C S hC hS
  have hi : ContDiffAt ℝ ∞ (hf.localInverse _ _ (C, 0))
      (covarianceStationarityMap (H : Matrix n n ℂ) A θ S (C, 0)) := hg.to_localInverse hf.hasFDerivAt (by simp)
  rw [covarianceStationarityMap_base (H : Matrix n n ℂ) A hA θ C S hC hS hstat] at hi
  have hi' : ContDiffAt ℝ ∞ (hf.localInverse _ _ (C, 0)) (jointOwnerResponseTarget H (H, C)) := by
    simpa only [jointOwnerResponseTarget, sub_self, map_zero] using hi
  have ht := hi'.comp (H, C) (contDiff_jointOwnerResponseTarget H).contDiffAt
  exact contDiffAt_const.add ((densityTangent (n := n)).subtypeL.contDiff.contDiffAt.comp (H, C)
    (contDiffAt_snd.comp (H, C) ht))

/-- The same inverse branch is the actual joint center/covariance optimizer. -/
theorem eventually_jointOwnerOptimizer_eq_responseBranch [Nonempty n]
    (H : selfAdjoint (Matrix n n ℂ)) (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (θ : ℝ) (hθ : 0 < θ) (C : selfAdjoint (Matrix ι ι ℝ))
    (S : selfAdjoint (Matrix n n ℂ)) (hC : (C : Matrix ι ι ℝ).PosDef)
    (hS : (S : Matrix n n ℂ).PosDef) (ht : realTrace (S : Matrix n n ℂ) = 1)
    (hstat : densityTangentRestriction
      (fderiv ℝ (hermitianDensityObjective (H : Matrix n n ℂ) (covarianceKraus A C) θ) S) = 0) :
    ∀ᶠ P : selfAdjoint (Matrix n n ℂ) × selfAdjoint (Matrix ι ι ℝ) in 𝓝 (H, C),
      hermitianDensityOptimizer P.1 (covarianceKraus A P.2) θ =
        jointOwnerResponseBranch H A hA θ hθ C S hC hS P := by
  have hf := hasStrictFDerivAt_covarianceStationarityMap (H : Matrix n n ℂ) A hA θ hθ C S hC hS
  have hf0 := covarianceStationarityMap_base (H : Matrix n n ℂ) A hA θ C S hC hS hstat
  let target := jointOwnerResponseTarget (ι := ι) H
  have htarget : Tendsto target (𝓝 (H, C)) (𝓝 (covarianceStationarityMap (H : Matrix n n ℂ) A θ S (C, 0))) := by
    rw [hf0]
    have hc := (contDiff_jointOwnerResponseTarget (ι := ι) H).continuous.continuousAt.tendsto (x := (H, C))
    simpa only [jointOwnerResponseTarget, sub_self, map_zero] using hc
  let inv := hf.localInverse (covarianceStationarityMap (H : Matrix n n ℂ) A θ S)
    (covarianceStationarityEquiv (H : Matrix n n ℂ) A θ hθ C S hS) (C, 0)
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
  change hermitianDensityOptimizer P.1 (covarianceKraus A P.2) θ = densityChart S ((inv (target P)).2)
  apply density_stationary_eq_optimizer_source_unrestricted P.1 (covarianceKraus A P.2) hθ _ hSP
    ((densityChart_trace S _).trans ht)
  rw [density_stationarity_center_shift_source_unrestricted (H : Matrix n n ℂ) (P.1 : Matrix n n ℂ) (covarianceKraus A P.2) θ _ hSP]
  have hfirst := congrArg Prod.fst heq
  have hgrad := congrArg Prod.snd heq
  change (inv (target P)).1 = P.2 at hfirst
  change covarianceGradientChart (H : Matrix n n ℂ) A θ S (inv (target P)) = densityCenterFunctional (P.1 - H) at hgrad
  have hg : covarianceGradientChart (H : Matrix n n ℂ) A θ S (P.2, (inv (target P)).2) =
      densityCenterFunctional (P.1 - H) := by
    have hp : (P.2, (inv (target P)).2) = inv (target P) := by
      apply Prod.ext
      · exact hfirst.symm
      · rfl
    rw [hp]
    exact hgrad
  rw [covarianceGradientChart_eq_densityGradientChart (H : Matrix n n ℂ) A hA θ P.2 S _ hP hSP] at hg
  change -densityTangentRestriction
    (fderiv ℝ (hermitianDensityObjective (H : Matrix n n ℂ) (covarianceKraus A P.2) θ)
      (densityChart S ((inv (target P)).2))) = densityCenterFunctional (P.1 - H) at hg
  have hz := congrArg Neg.neg hg
  simp only [neg_neg] at hz
  exact add_eq_zero_iff_eq_neg.mpr hz

/-- Actual joint optimizer, using the already constructed attained density optimizer. -/
def jointOwnerDensityOptimizer [Nonempty n] (A : ι → Matrix n n ℂ) (θ : ℝ)
    (P : selfAdjoint (Matrix n n ℂ) × selfAdjoint (Matrix ι ι ℝ)) : selfAdjoint (Matrix n n ℂ) :=
  hermitianDensityOptimizer P.1 (covarianceKraus A P.2) θ

theorem contDiffAt_jointOwnerDensityOptimizer [Nonempty n]
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) {θ : ℝ} (hθ : 0 < θ)
    (H : selfAdjoint (Matrix n n ℂ)) (C : selfAdjoint (Matrix ι ι ℝ))
    (hC : (C : Matrix ι ι ℝ).PosDef) :
    ContDiffAt ℝ ∞ (jointOwnerDensityOptimizer A θ) (H, C) := by
  let S := hermitianDensityOptimizer (H : Matrix n n ℂ) (covarianceKraus A C) θ
  have hS : (S : Matrix n n ℂ).PosDef := hermitianDensityOptimizer_posDef (H : Matrix n n ℂ) (covarianceKraus A C) hθ
  have ht : realTrace (S : Matrix n n ℂ) = 1 := hermitianDensityOptimizer_trace (H : Matrix n n ℂ) (covarianceKraus A C) θ
  have hstat := densityOptimizer_stationary_source_unrestricted (H : Matrix n n ℂ) (covarianceKraus A C) hθ
  exact (contDiffAt_jointOwnerResponseBranch H A hA θ hθ C S hC hS hstat).congr_of_eventuallyEq
    (eventually_jointOwnerOptimizer_eq_responseBranch H A hA θ hθ C S hC hS ht hstat)

/-- The genuine supremum potential in joint Hermitian-center and symmetric-covariance coordinates. -/
def jointHermitianOwnerPotential (A : ι → Matrix n n ℂ) (θ : ℝ)
    (P : selfAdjoint (Matrix n n ℂ) × selfAdjoint (Matrix ι ι ℝ)) : ℝ :=
  ownerPotential P.1 A P.2 θ

theorem contDiffAt_jointHermitianOwnerPotential [Nonempty n]
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) {θ : ℝ} (hθ : 0 < θ)
    (H : selfAdjoint (Matrix n n ℂ)) (C : selfAdjoint (Matrix ι ι ℝ))
    (hC : (C : Matrix ι ι ℝ).PosDef) :
    ContDiffAt ℝ ∞ (jointHermitianOwnerPotential A θ) (H, C) := by
  let S := jointOwnerDensityOptimizer A θ (H, C)
  have hs := contDiffAt_jointOwnerDensityOptimizer A hA hθ H C hC
  have hS : (S : Matrix n n ℂ).PosDef := hermitianDensityOptimizer_posDef (H : Matrix n n ℂ) (covarianceKraus A C) hθ
  have hi := (hermitianInclusion (n := n)).contDiff.contDiffAt.comp (H, C) hs
  have hh : ContDiffAt ℝ ∞ (fun P : selfAdjoint (Matrix n n ℂ) × selfAdjoint (Matrix ι ι ℝ) =>
      (P.1 : Matrix n n ℂ)) (H, C) := hermitianInclusion.contDiff.contDiffAt.comp (H, C) contDiffAt_fst
  have hl := realTraceCLM.contDiff.contDiffAt.comp (H, C) (hh.mul hi)
  have hf := (contDiffAt_covarianceFidelity A hA C S hC hS).comp (H, C) (contDiffAt_snd.prodMk hs)
  have ht := ContDiffAt.comp (g := tsallisPotential θ) (f := jointOwnerDensityOptimizer A θ) (H, C)
    (contDiffAt_tsallisPotential θ S hS) hs
  apply ((hl.add hf).add ht).congr_of_eventuallyEq
  filter_upwards [(continuous_snd.continuousAt (x := (H, C))).eventually (eventually_real_posDef_of_posDef C hC)] with P hP
  exact ownerPotential_eq_chosenObjective (P.1 : Matrix n n ℂ) A hA θ P.2 hP.posSemidef

/-- Joint optimizer smoothness throughout the positive coefficient cone. -/
theorem contDiffOn_jointOwnerDensityOptimizer [Nonempty n]
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) {θ : ℝ} (hθ : 0 < θ) :
    ContDiffOn ℝ ∞ (jointOwnerDensityOptimizer A θ)
      {P | (P.2 : Matrix ι ι ℝ).PosDef} := by
  intro P hP
  exact (contDiffAt_jointOwnerDensityOptimizer A hA hθ P.1 P.2 hP).contDiffWithinAt

/-- Joint smoothness on the full center space times the positive coefficient cone. -/
theorem contDiffOn_jointHermitianOwnerPotential [Nonempty n]
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) {θ : ℝ} (hθ : 0 < θ) :
    ContDiffOn ℝ ∞ (jointHermitianOwnerPotential A θ)
      {P | (P.2 : Matrix ι ι ℝ).PosDef} := by
  intro P hP
  exact (contDiffAt_jointHermitianOwnerPotential A hA hθ P.1 P.2 hP).contDiffWithinAt

end
end MatrixSpencer
