import MatrixSpencer.JointOwnerResponse
import MatrixSpencer.KSLocalDescent
import MatrixSpencer.KSSafeRetirement

/-!
# Moving-transport majorants for the full-cube owner argument

A legal transport completion makes the first derivative of its linear
majorant center vanish. The second derivative of the optimized majorant
then involves only the first derivative of the actual density potential.
This is the direct majorant form of the shifted-square Hessian bound.
-/

open Matrix Filter Topology
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff

noncomputable section
namespace MatrixSpencer.KSMovingOwnerHessian

set_option maxHeartbeats 800000

section CriticalComposition
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- When a center curve has zero velocity, the response Hessian contributes
zero. This identity is proved by the second-order chain rule. -/
theorem iteratedDeriv_two_comp_of_critical (f : E → ℝ) (G : ℝ → E)
    (hf : ContDiffAt ℝ 2 f (G 0)) (hG : ContDiffAt ℝ 2 G 0)
    (hzero : deriv G 0 = 0) :
    iteratedDeriv 2 (fun t => f (G t)) 0 = fderiv ℝ f (G 0) (iteratedDeriv 2 G 0) := by
  have h := iteratedDeriv_vcomp_two hf hG
  simpa only [Function.comp_def, hzero, iteratedFDeriv_two_apply, map_zero,
    ContinuousLinearMap.zero_apply, zero_add] using h

/-- A touching smooth majorant with negative curvature excludes a local
minimum of the actual value; the actual value need not be differentiable. -/
theorem not_isLocalMin_of_critical_majorant (actual : ℝ → ℝ) (f : E → ℝ)
    (G : ℝ → E) (hf : ContDiffAt ℝ 2 f (G 0)) (hG : ContDiffAt ℝ 2 G 0)
    (hzero : deriv G 0 = 0) (hcontact : actual 0 = f (G 0))
    (hmajorant : ∀ᶠ t in 𝓝 (0 : ℝ), actual t ≤ f (G t))
    (hnegative : fderiv ℝ f (G 0) (iteratedDeriv 2 G 0) < 0) :
    ¬ IsLocalMin actual 0 := by
  intro hmin
  have hm : IsLocalMin (fun t => f (G t)) 0 := by
    filter_upwards [hmin, hmajorant] with t ht hmaj
    rw [hcontact] at ht
    exact ht.trans hmaj
  have hsecond := iteratedDeriv_two_comp_of_critical f G hf hG hzero
  have hneg : fderiv ℝ (fderiv ℝ (fun t => f (G t))) 0 (1 : ℝ) 1 < 0 := by
    have hn : iteratedDeriv 2 (fun t => f (G t)) 0 < 0 := by rw [hsecond]; exact hnegative
    simpa only [iteratedDeriv, iteratedFDeriv_two_apply] using hn
  exact ks_not_isLocalMin_of_hessian_neg (fun t => f (G t)) 0 1 (hf.comp 0 hG) hneg hm

end CriticalComposition

section ActualMajorant
open KSSafeRetirement
variable {ι n m : Type*} [Fintype ι] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m] [Nonempty n]

local instance movingMajorantCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance movingMajorantSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) :=
  inferInstance

/-- The actual source-free Tsallis potential has the actual optimizing
density as its gradient along a critical center curve. -/
theorem basePotential_second_derivative (G : ℝ → selfAdjoint (Matrix n n ℂ))
    {θ : ℝ} (hθ : 0 < θ) (hG : ContDiffAt ℝ 2 G 0) (hzero : deriv G 0 = 0) :
    iteratedDeriv 2 (fun t => baseHermitianPotential θ (G t)) 0 =
      realTrace (densityOptimizer (G 0) zeroKraus θ *
        ((iteratedDeriv 2 G (0 : ℝ) : selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ)) := by
  rw [baseHermitianPotential_eq]
  have hf : ContDiffAt ℝ 2 (hermitianDensityPotential (zeroKraus (n := n)) θ) (G 0) :=
    (contDiffAt_hermitianDensityPotential_source_unrestricted (G 0) zeroKraus hθ).of_le
      (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  rw [iteratedDeriv_two_comp_of_critical _ _ hf hG hzero,
    (hasFDerivAt_hermitianDensityPotential_source_unrestricted (G 0) zeroKraus hθ).fderiv]
  rfl

/-- A moving supported transport gives a concrete exclusion of local
minimality for the actual full-density potential. The only calculus
conditions concern the explicit majorant center `G`; no Hessian formula
or local-descent conclusion for the actual value is assumed. -/
theorem actual_not_isLocalMin_of_moving_transport
    (H : ℝ → Matrix n n ℂ) (B : ℝ → ι → Matrix n n ℂ)
    (V : Matrix n m ℂ) (hV : Vᴴ * V = 1) (Z : ℝ → Matrix m m ℂ)
    (G : ℝ → selfAdjoint (Matrix n n ℂ)) {θ : ℝ} (hθ : 0 < θ)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (ht : realTrace (S : Matrix n n ℂ) = 1)
    (hmax : ∀ T ∈ densitySet,
      densityObjective (H 0) (B 0) θ T ≤ densityObjective (H 0) (B 0) θ S)
    (hcontact : (G 0 : Matrix n n ℂ) = H 0 + actualSupportedGradient (B 0) S)
    (hZ : ∀ᶠ t in 𝓝 (0 : ℝ), (Z t).PosDef)
    (hsupport : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ X ∈ densitySet,
      V * (Vᴴ * krausChannel (B t) X * V) * Vᴴ = krausChannel (B t) X)
    (hcenter : ∀ᶠ t in 𝓝 (0 : ℝ),
      (G t : Matrix n n ℂ) = H t + supportedGradient (B t) V (Z t))
    (hG : ContDiffAt ℝ 2 G 0) (hzero : deriv G 0 = 0)
    (hnegative : realTrace ((S : Matrix n n ℂ) *
      ((iteratedDeriv 2 G (0 : ℝ) : selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ)) < 0) :
    ¬ IsLocalMin (fun t => densityPotential (H t) (B t) θ) 0 := by
  have hf : ContDiffAt ℝ 2 (hermitianDensityPotential (zeroKraus (n := n)) θ) (G 0) :=
    (contDiffAt_hermitianDensityPotential_source_unrestricted (G 0) zeroKraus hθ).of_le
      (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  apply not_isLocalMin_of_critical_majorant _ (hermitianDensityPotential zeroKraus θ)
    G hf hG hzero
  · simp only [hermitianDensityPotential]
    rw [hcontact]
    simpa only [baseDensityPotential, zeroKraus] using
      (basePotential_contact (H 0) (B 0) hθ S hS ht hmax).symm
  · filter_upwards [hZ, hsupport, hcenter] with t htZ htSupport htCenter
    simp only [hermitianDensityPotential]
    rw [htCenter]
    simpa only [baseDensityPotential, zeroKraus] using
      densityPotential_le_supported (H t) (B t) V hV htZ θ htSupport
  · rw [(hasFDerivAt_hermitianDensityPotential_source_unrestricted
      (G 0) zeroKraus hθ).fderiv]
    have hopt := baseOptimizer_eq_actual (H 0) (B 0) hθ S hS ht hmax
    have hopt' : densityOptimizer (G 0) zeroKraus θ = (S : Matrix n n ℂ) := by
      rw [hcontact]
      exact congrArg (fun X : selfAdjoint (Matrix n n ℂ) => (X : Matrix n n ℂ)) hopt
    change realTrace (densityOptimizer (G 0) zeroKraus θ *
      ((iteratedDeriv 2 G (0 : ℝ) : selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ)) < 0
    rw [hopt']
    exact hnegative

end ActualMajorant

section OwnerCoefficients

/-- The exact natural owner multiplied by a linearly moving transport probe. -/
def ownerProbe (u x h q r t : ℝ) : ℝ := u * (1 - (x + t * h) ^ 2) * (q + t * r)

def ownerProbeVelocity (u x h q r t : ℝ) : ℝ :=
  u * ((-2 * h * (x + t * h)) * (q + t * r) + (1 - (x + t * h) ^ 2) * r)

theorem hasDerivAt_ownerProbe (u x h q r t : ℝ) :
    HasDerivAt (ownerProbe u x h q r) (ownerProbeVelocity u x h q r t) t := by
  have hx := (hasDerivAt_const t x).add ((hasDerivAt_id t).mul_const h)
  have hq := (hasDerivAt_const t q).add ((hasDerivAt_id t).mul_const r)
  have hd := ((hasDerivAt_const t u).mul ((hasDerivAt_const t (1 : ℝ)).sub (hx.pow 2))).mul hq
  convert hd using 1
  dsimp [ownerProbe, ownerProbeVelocity]
  ring

theorem hasDerivAt_ownerProbeVelocity_zero (u x h q r : ℝ) :
    HasDerivAt (ownerProbeVelocity u x h q r)
      (-2 * u * h ^ 2 * q - 4 * u * x * h * r) 0 := by
  have hx := (hasDerivAt_const (0 : ℝ) x).add ((hasDerivAt_id (0 : ℝ)).mul_const h)
  have hq := (hasDerivAt_const (0 : ℝ) q).add ((hasDerivAt_id (0 : ℝ)).mul_const r)
  have hd := (((hx.const_mul (-2 * h)).mul hq).add
    (((hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub (hx.pow 2)).mul_const r)).const_mul u
  convert hd using 1
  dsimp [ownerProbeVelocity]
  ring

theorem iteratedDeriv_two_ownerProbe (u x h q r : ℝ) :
    iteratedDeriv 2 (ownerProbe u x h q r) 0 = -2 * u * h ^ 2 * q - 4 * u * x * h * r := by
  have he : deriv (ownerProbe u x h q r) = ownerProbeVelocity u x h q r :=
    funext fun t => (hasDerivAt_ownerProbe u x h q r t).deriv
  change iteratedDeriv (1 + 1) (ownerProbe u x h q r) 0 = _
  rw [iteratedDeriv_succ, iteratedDeriv_one, he]
  exact (hasDerivAt_ownerProbeVelocity_zero u x h q r).deriv

end OwnerCoefficients

section InverseLine
variable {n : Type*} [Fintype n] [DecidableEq n]

local instance movingOwnerCStar : CStarAlgebra (Matrix n n ℂ) := {}

def transportLine (Z U : Matrix n n ℂ) (t : ℝ) : Matrix n n ℂ := Z + t • U

def inverseLine (Z U : Matrix n n ℂ) (t : ℝ) : Matrix n n ℂ := (transportLine Z U t)⁻¹

def inverseVelocity (Z U : Matrix n n ℂ) (t : ℝ) : Matrix n n ℂ :=
  -(inverseLine Z U t * U * inverseLine Z U t)

theorem hasDerivAt_transportLine (Z U : Matrix n n ℂ) (t : ℝ) :
    HasDerivAt (transportLine Z U) U t := by
  simpa only [transportLine, one_smul, zero_add] using
    (hasDerivAt_const t Z).add ((hasDerivAt_id t).smul_const U)

theorem hasDerivAt_inverseLine (Z U : Matrix n n ℂ) (t : ℝ)
    (hZ : IsUnit (transportLine Z U t)) :
    HasDerivAt (inverseLine Z U)
      (-(inverseLine Z U t * U * inverseLine Z U t)) t := by
  have h := (hasStrictFDerivAt_matrixInverse (transportLine Z U t) hZ).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_transportLine Z U t)
  simpa only [inverseLine, Function.comp_def, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.mulLeftRight_apply] using h

theorem contDiffAt_inverseLine (Z U : Matrix n n ℂ) (hZ : IsUnit Z) :
    ContDiffAt ℝ ∞ (inverseLine Z U) 0 := by
  have hline : ContDiffAt ℝ ∞ (transportLine Z U) 0 :=
    contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const)
  have hi : ContDiffAt ℝ ∞ (fun A : Matrix n n ℂ => A⁻¹) (transportLine Z U 0) := by
    simpa only [transportLine, zero_smul, add_zero] using contDiffAt_matrixInverse Z hZ
  exact hi.comp 0 hline

theorem iteratedDeriv_two_inverseLine (Z U : Matrix n n ℂ) (hZ : IsUnit Z) :
    iteratedDeriv 2 (inverseLine Z U) 0 = (2 : ℝ) • (Z⁻¹ * U * Z⁻¹ * U * Z⁻¹) := by
  have hZ0 : IsUnit (transportLine Z U 0) := by simpa [transportLine] using hZ
  have hd := hasDerivAt_inverseLine Z U 0 hZ0
  have hsecond := ((hd.mul_const U).mul hd).neg
  have hevent : ∀ᶠ t in 𝓝 (0 : ℝ), IsUnit (transportLine Z U t) := by
    exact (hasDerivAt_transportLine Z U 0).continuousAt.eventually
      (Units.isOpen.mem_nhds hZ0)
  have heq : deriv (inverseLine Z U) =ᶠ[𝓝 (0 : ℝ)]
      (fun t => -(inverseLine Z U t * U * inverseLine Z U t)) := by
    filter_upwards [hevent] with t ht
    exact (hasDerivAt_inverseLine Z U t ht).deriv
  have h := (hsecond.congr_of_eventuallyEq heq).deriv
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  rw [h]
  simp only [inverseLine, transportLine, zero_smul, add_zero]
  rw [show (2 : ℝ) = 1 + 1 from by norm_num, add_smul, one_smul]
  noncomm_ring

theorem hasDerivAt_inverseVelocity_zero (Z U : Matrix n n ℂ) (hZ : IsUnit Z) :
    HasDerivAt (inverseVelocity Z U)
      ((2 : ℝ) • (Z⁻¹ * U * Z⁻¹ * U * Z⁻¹)) 0 := by
  have hZ0 : IsUnit (transportLine Z U 0) := by simpa [transportLine] using hZ
  have hd := hasDerivAt_inverseLine Z U 0 hZ0
  have hh := ((hd.mul_const U).mul hd).neg
  convert hh using 1
  dsimp only [inverseLine, transportLine]
  simp only [zero_smul, add_zero]
  rw [show (2 : ℝ) = 1 + 1 from by norm_num, add_smul, one_smul]
  noncomm_ring

theorem eventually_posDef_transportLine {Z U : Matrix n n ℂ}
    (hZ : Z.PosDef) (hU : U.IsHermitian) :
    ∀ᶠ t in 𝓝 (0 : ℝ), (transportLine Z U t).PosDef := by
  let ZH : selfAdjoint (Matrix n n ℂ) := ⟨Z, hZ.isHermitian⟩
  let UH : selfAdjoint (Matrix n n ℂ) := ⟨U, hU⟩
  have hc : Continuous (fun t : ℝ => ZH + t • UH) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have ht : Tendsto (fun t : ℝ => ZH + t • UH) (𝓝 0) (𝓝 ZH) := by
    simpa only [zero_smul, add_zero] using hc.continuousAt.tendsto (x := (0 : ℝ))
  exact ht.eventually (eventually_posDef_of_posDef ZH hZ)

end InverseLine

section ExplicitCenter
variable {ι n E : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
local instance centerCurveCStar : CStarAlgebra (Matrix n n ℂ) := {}

/-- The explicit transport-majorant center, before any optimization.
`embed` extends the transport inverse from the fixed support. -/
def centerCurve (embed : Matrix n n ℂ →L[ℝ] E) (H K : E) (A : ι → E)
    (Z U : Matrix n n ℂ) (u : ℝ) (x h q r : ι → ℝ) (t : ℝ) : E :=
  H + t • K + embed (inverseLine Z U t) +
    ∑ i, ownerProbe u (x i) (h i) (q i) (r i) t • A i

def centerVelocity (embed : Matrix n n ℂ →L[ℝ] E) (K : E) (A : ι → E)
    (Z U : Matrix n n ℂ) (u : ℝ) (x h q r : ι → ℝ) (t : ℝ) : E :=
  K + embed (inverseVelocity Z U t) +
    ∑ i, ownerProbeVelocity u (x i) (h i) (q i) (r i) t • A i

def centerAcceleration (embed : Matrix n n ℂ →L[ℝ] E) (A : ι → E)
    (Z U : Matrix n n ℂ) (u : ℝ) (x h q r : ι → ℝ) : E :=
  (2 : ℝ) • embed (Z⁻¹ * U * Z⁻¹ * U * Z⁻¹) +
    ∑ i, (-2 * u * (h i) ^ 2 * q i - 4 * u * x i * h i * r i) • A i

theorem hasDerivAt_centerCurve (embed : Matrix n n ℂ →L[ℝ] E)
    (H K : E) (A : ι → E) (Z U : Matrix n n ℂ) (u : ℝ)
    (x h q r : ι → ℝ) (t : ℝ) (hZ : IsUnit (transportLine Z U t)) :
    HasDerivAt (centerCurve embed H K A Z U u x h q r)
      (centerVelocity embed K A Z U u x h q r t) t := by
  have hlinear := (hasDerivAt_const t H).add ((hasDerivAt_id t).smul_const K)
  have hi := embed.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_inverseLine Z U t hZ)
  have hs := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    (hasDerivAt_ownerProbe u (x i) (h i) (q i) (r i) t).smul_const (A i))
  simpa only [centerCurve, centerVelocity, inverseVelocity, one_smul, zero_add] using
    (hlinear.add hi).add hs

theorem hasDerivAt_centerVelocity_zero (embed : Matrix n n ℂ →L[ℝ] E)
    (K : E) (A : ι → E) (Z U : Matrix n n ℂ) (hZ : IsUnit Z) (u : ℝ)
    (x h q r : ι → ℝ) :
    HasDerivAt (centerVelocity embed K A Z U u x h q r)
      (centerAcceleration embed A Z U u x h q r) 0 := by
  have hi := embed.hasFDerivAt.comp_hasDerivAt 0 (hasDerivAt_inverseVelocity_zero Z U hZ)
  have hs := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    (hasDerivAt_ownerProbeVelocity_zero u (x i) (h i) (q i) (r i)).smul_const (A i))
  simpa only [centerVelocity, centerAcceleration, map_smul, zero_add] using
    ((hasDerivAt_const (0 : ℝ) K).add hi).add hs

theorem iteratedDeriv_two_centerCurve (embed : Matrix n n ℂ →L[ℝ] E)
    (H K : E) (A : ι → E) (Z U : Matrix n n ℂ) (hZ : IsUnit Z) (u : ℝ)
    (x h q r : ι → ℝ) :
    iteratedDeriv 2 (centerCurve embed H K A Z U u x h q r) 0 =
      centerAcceleration embed A Z U u x h q r := by
  have hZ0 : IsUnit (transportLine Z U 0) := by simpa [transportLine] using hZ
  have hevent : ∀ᶠ t in 𝓝 (0 : ℝ), IsUnit (transportLine Z U t) :=
    (hasDerivAt_transportLine Z U 0).continuousAt.eventually (Units.isOpen.mem_nhds hZ0)
  have heq : deriv (centerCurve embed H K A Z U u x h q r) =ᶠ[𝓝 (0 : ℝ)]
      centerVelocity embed K A Z U u x h q r := by
    filter_upwards [hevent] with t ht
    exact (hasDerivAt_centerCurve embed H K A Z U u x h q r t ht).deriv
  change iteratedDeriv (1 + 1) (centerCurve embed H K A Z U u x h q r) 0 = _
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  exact ((hasDerivAt_centerVelocity_zero embed K A Z U hZ u x h q r).congr_of_eventuallyEq heq).deriv

theorem contDiffAt_centerCurve (embed : Matrix n n ℂ →L[ℝ] E)
    (H K : E) (A : ι → E) (Z U : Matrix n n ℂ) (hZ : IsUnit Z) (u : ℝ)
    (x h q r : ι → ℝ) :
    ContDiffAt ℝ ∞ (centerCurve embed H K A Z U u x h q r) 0 := by
  have hi := embed.contDiff.contDiffAt.comp 0 (contDiffAt_inverseLine Z U hZ)
  have hs : ContDiffAt ℝ ∞ (fun t : ℝ =>
      ∑ i, ownerProbe u (x i) (h i) (q i) (r i) t • A i) 0 := by
    unfold ownerProbe
    fun_prop
  exact ((contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const)).add hi).add hs

end ExplicitCenter

section ExplicitActualMajorant
open KSSafeRetirement
variable {ι κ n m : Type*} [Fintype ι] [Fintype κ] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m] [Nonempty n]
local instance explicitMajorantCStar {s : Type*} [Fintype s] [DecidableEq s] :
    CStarAlgebra (Matrix s s ℂ) := {}
local instance explicitMajorantSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) :=
  inferInstance

/-- The natural-owner moving-transport criterion with every derivative and
regularity assertion discharged. The remaining assumptions are explicit
matrix-source identities, the exact legal-completion equation (zero center
velocity), and the finite trace inequality for the chosen completion. -/
theorem actual_not_isLocalMin_of_explicit_center
    (Hactual : ℝ → Matrix n n ℂ) (B : ℝ → κ → Matrix n n ℂ)
    (V : Matrix n m ℂ) (hV : Vᴴ * V = 1)
    (embed : Matrix m m ℂ →L[ℝ] selfAdjoint (Matrix n n ℂ))
    (H K : selfAdjoint (Matrix n n ℂ)) (A : ι → selfAdjoint (Matrix n n ℂ))
    (Z U : Matrix m m ℂ) (hZ : Z.PosDef) (hU : U.IsHermitian)
    (u : ℝ) (x h q r : ι → ℝ) {θ : ℝ} (hθ : 0 < θ)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (ht : realTrace (S : Matrix n n ℂ) = 1)
    (hmax : ∀ T ∈ densitySet,
      densityObjective (Hactual 0) (B 0) θ T ≤ densityObjective (Hactual 0) (B 0) θ S)
    (hcontact : ((centerCurve embed H K A Z U u x h q r 0 : selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ) =
      Hactual 0 + actualSupportedGradient (B 0) S)
    (hsupport : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ X ∈ densitySet,
      V * (Vᴴ * krausChannel (B t) X * V) * Vᴴ = krausChannel (B t) X)
    (hcenter : ∀ᶠ t in 𝓝 (0 : ℝ),
      ((centerCurve embed H K A Z U u x h q r t : selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ) =
        Hactual t + supportedGradient (B t) V (transportLine Z U t))
    (hlegal : centerVelocity embed K A Z U u x h q r 0 = 0)
    (hnegative : realTrace ((S : Matrix n n ℂ) *
      ((centerAcceleration embed A Z U u x h q r : selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ)) < 0) :
    ¬ IsLocalMin (fun t => densityPotential (Hactual t) (B t) θ) 0 := by
  let G := centerCurve embed H K A Z U u x h q r
  have hG : ContDiffAt ℝ 2 G 0 :=
    (contDiffAt_centerCurve embed H K A Z U hZ.isUnit u x h q r).of_le
      (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have hZ0 : IsUnit (transportLine Z U 0) := by simpa [transportLine] using hZ.isUnit
  have hcritical : deriv G 0 = 0 := by
    rw [(hasDerivAt_centerCurve embed H K A Z U u x h q r 0 hZ0).deriv]
    exact hlegal
  apply actual_not_isLocalMin_of_moving_transport Hactual B V hV (transportLine Z U)
    G hθ S hS ht hmax hcontact (eventually_posDef_transportLine hZ hU) hsupport hcenter hG hcritical
  change realTrace ((S : Matrix n n ℂ) *
    ((iteratedDeriv 2 G (0 : ℝ) : selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ)) < 0
  rw [iteratedDeriv_two_centerCurve embed H K A Z U hZ.isUnit u x h q r]
  exact hnegative

end ExplicitActualMajorant
end MatrixSpencer.KSMovingOwnerHessian
