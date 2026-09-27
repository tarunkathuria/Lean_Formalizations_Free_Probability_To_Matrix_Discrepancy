import SeamlessKS.TransportCurve
import MatrixSpencer.KSHessianContact

/-!
# Actual scalar derivatives from the supported transport majorant

The actual smooth density potential touches the proved explicit majorant.
Consequently its first derivative vanishes and its second derivative is at
most the exact transport acceleration pairing. This exposes the actual
Hessian rather than only excluding local minimality.
-/

open Matrix Filter Topology
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
noncomputable section
namespace SeamlessKS.SupportedHessian

open MatrixSpencer MatrixSpencer.KSMovingOwnerHessian
open MatrixSpencer.KSSupportedCenterCurve SeamlessKS.TransportCurve

variable {ι n m κ : Type*} [Fintype ι] [Fintype n] [Fintype m] [Fintype κ]
  [DecidableEq n] [DecidableEq m] [Nonempty n]
local instance {k : Type*} [Fintype k] [DecidableEq k] : CStarAlgebra (Matrix k k ℂ) := {}

theorem deriv_zero_and_second_le_of_supported_curve
    (Hactual : ℝ → Matrix n n ℂ) (L : ℝ → κ → Matrix n n ℂ)
    (V : Matrix n m ℂ) (hV : Vᴴ * V = 1)
    (H K : selfAdjoint (Matrix n n ℂ)) (A : ι → selfAdjoint (Matrix n n ℂ))
    {Z U : Matrix m m ℂ} (hZ : Z.PosDef) (hU : U.IsHermitian)
    (c cv : ι → ℝ → ℝ) (ca q r : ι → ℝ)
    (hc : ∀ i t, HasDerivAt (c i) (cv i t) t)
    (hv : ∀ i, HasDerivAt (cv i) (ca i) 0)
    (hc2 : ∀ i, ContDiffAt ℝ 2 (c i) 0) {θ : ℝ} (hθ : 0 < θ)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (ht : realTrace (S : Matrix n n ℂ) = 1)
    (hmax : ∀ T ∈ densitySet,
      densityObjective (Hactual 0) (L 0) θ T ≤ densityObjective (Hactual 0) (L 0) θ S)
    (hM : (Vᴴ * krausChannel (L 0) S * V).PosDef)
    (hsolve : Z * (Vᴴ * krausChannel (L 0) S * V) * Z = Vᴴ * (S : Matrix n n ℂ) * V)
    (hsupport0 : ∀ X : Matrix n n ℂ, X.PosSemidef →
      V * (Vᴴ * krausChannel (L 0) X * V) * Vᴴ = krausChannel (L 0) X)
    (hsupport : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ X ∈ densitySet,
      V * (Vᴴ * krausChannel (L t) X * V) * Vᴴ = krausChannel (L t) X)
    (hcenter : ∀ᶠ t in 𝓝 (0 : ℝ),
      ((SeamlessKS.TransportCurve.centerCurve (embedding V) H K A Z U c q r t : selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ) =
        Hactual t + KSSafeRetirement.supportedGradient (L t) V (transportLine Z U t))
    (hlegal : SeamlessKS.TransportCurve.centerVelocity (embedding V) K A Z U c cv q r 0 = 0)
    (hactual : ContDiffAt ℝ 2 (fun t => densityPotential (Hactual t) (L t) θ) 0) :
    deriv (fun t => densityPotential (Hactual t) (L t) θ) 0 = 0 ∧
    iteratedDeriv 2 (fun t => densityPotential (Hactual t) (L t) θ) 0 ≤
      realTrace ((S : Matrix n n ℂ) *
        ((SeamlessKS.TransportCurve.centerAcceleration (embedding V) A Z U (fun i => cv i 0) ca q r :
          selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ)) := by
  let G := SeamlessKS.TransportCurve.centerCurve (embedding V) H K A Z U c q r
  let f := hermitianDensityPotential (KSSafeRetirement.zeroKraus (n := n)) θ
  let g := fun t => densityPotential (Hactual t) (L t) θ
  have hG : ContDiffAt ℝ 2 G 0 :=
    SeamlessKS.TransportCurve.contDiffAt_centerCurve (embedding V) H K A Z U hZ.isUnit c q r hc2
  have hZ0 : IsUnit (transportLine Z U 0) := by
    simpa only [transportLine, zero_smul, add_zero] using hZ.isUnit
  have hcritical : deriv G 0 = 0 := by
    rw [(SeamlessKS.TransportCurve.hasDerivAt_centerCurve (embedding V) H K A Z U c cv q r 0 hZ0 (fun i => hc i 0)).deriv]
    exact hlegal
  have hcenter0 : (G 0 : Matrix n n ℂ) =
      Hactual 0 + KSSafeRetirement.supportedGradient (L 0) V Z := by
    simpa only [transportLine, zero_smul, add_zero] using hcenter.self_of_nhds
  have hf : ContDiffAt ℝ 2 f (G 0) :=
    (contDiffAt_hermitianDensityPotential_source_unrestricted
      (G 0) KSSafeRetirement.zeroKraus hθ).of_le
        (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have hcontact : g 0 = f (G 0) := by
    dsimp only [g, f, hermitianDensityPotential]
    rw [hcenter0]
    simpa only [baseDensityPotential, KSSafeRetirement.zeroKraus] using
      (KSArbitraryTransportContact.basePotential_contact (Hactual 0) (L 0) V hV hθ
        S hS ht hmax hZ hM hsolve hsupport0).symm
  have hmajorant : ∀ᶠ t in 𝓝 (0 : ℝ), g t ≤ f (G t) := by
    filter_upwards [eventually_posDef_transportLine hZ hU, hsupport, hcenter] with t htZ htSupp htCent
    dsimp only [g, f, hermitianDensityPotential]
    rw [htCent]
    simpa only [baseDensityPotential, KSSafeRetirement.zeroKraus] using
      KSSafeRetirement.densityPotential_le_supported (Hactual t) (L t) V hV htZ θ htSupp
  have hpair : fderiv ℝ f (G 0) (iteratedDeriv 2 G 0) =
      realTrace ((S : Matrix n n ℂ) *
        ((SeamlessKS.TransportCurve.centerAcceleration (embedding V) A Z U (fun i => cv i 0) ca q r :
          selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ)) := by
    rw [(hasFDerivAt_hermitianDensityPotential_source_unrestricted
      (G 0) KSSafeRetirement.zeroKraus hθ).fderiv]
    have hopt := KSArbitraryTransportContact.baseOptimizer_eq_actual (Hactual 0) (L 0)
      V hV hθ S hS ht hmax hZ hM hsolve hsupport0
    have hopt' : densityOptimizer (G 0) KSSafeRetirement.zeroKraus θ = (S : Matrix n n ℂ) := by
      rw [hcenter0]
      exact congrArg (fun X : selfAdjoint (Matrix n n ℂ) => (X : Matrix n n ℂ)) hopt
    change realTrace (densityOptimizer (G 0) KSSafeRetirement.zeroKraus θ *
      ((iteratedDeriv 2 G (0 : ℝ) : selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ)) = _
    rw [hopt', SeamlessKS.TransportCurve.iteratedDeriv_two_centerCurve (embedding V) H K A Z U hZ.isUnit c cv ca q r hc hv]
  have hcomp := hf.comp 0 hG
  have hfirst := KSHessianContact.fderiv_eq_of_touching_majorant
    (fun t => f (G t)) g 0 hcomp hactual hmajorant hcontact
  have hsecond := KSHessianContact.hessian_le_of_touching_majorant
    (fun t => f (G t)) g 0 1 hcomp hactual hmajorant hcontact
  constructor
  · change deriv g 0 = 0
    rw [deriv, hfirst]
    change deriv (f ∘ G) 0 = 0
    rw [fderiv_comp_deriv 0 (hf.differentiableAt (by norm_num))
      (hG.differentiableAt (by norm_num)), hcritical, map_zero]
  · change iteratedDeriv 2 g 0 ≤ _
    have hle : iteratedDeriv 2 g 0 ≤ iteratedDeriv 2 (fun t => f (G t)) 0 := by
      simpa only [iteratedDeriv, iteratedFDeriv_two_apply] using hsecond
    rw [iteratedDeriv_two_comp_of_critical f G hf hG hcritical, hpair] at hle
    exact hle

end SeamlessKS.SupportedHessian
