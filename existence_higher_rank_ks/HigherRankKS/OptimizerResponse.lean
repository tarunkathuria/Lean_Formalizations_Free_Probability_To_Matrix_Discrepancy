import MatrixSpencer.OptimizerResponse
import HigherRankKS.Optimizer
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-!
# Parameterized response on the full density tangent

The inverse function theorem is applied to a triangular map retaining the
external parameter. Analytic hypotheses are stated on actual derivatives.
-/

open Matrix MatrixSpencer Filter Set
open scoped Topology MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff

noncomputable section
namespace HigherRankKS.OptimizerResponse

section Density
variable {n : Type*} [Fintype n] [DecidableEq n]
local instance responseCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance responseNormedSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance
local instance responseFinite : FiniteDimensional ℝ (selfAdjoint (Matrix n n ℂ)) :=
  inferInstanceAs (FiniteDimensional ℝ (selfAdjoint.submodule ℝ (Matrix n n ℂ)))
local instance responseTangentGroup : NormedAddCommGroup (densityTangent (n := n)) := inferInstance
local instance responseTangentSpace : NormedSpace ℝ (densityTangent (n := n)) := inferInstance
local instance responseTangentFinite : FiniteDimensional ℝ (densityTangent (n := n)) := inferInstance
local instance responseTangentComplete : CompleteSpace (densityTangent (n := n)) :=
  FiniteDimensional.complete ℝ _

/-- Full ambient trace-one density domain in real Hermitian coordinates. -/
def densityDomain : Set (selfAdjoint (Matrix n n ℂ)) :=
  {S | (S : Matrix n n ℂ) ∈ densitySet}

/-- A faithful attained maximizer is stationary on the full trace-zero tangent. -/
theorem faithful_maximizer_stationary
    (f : selfAdjoint (Matrix n n ℂ) → ℝ) (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) (ht : realTrace (S : Matrix n n ℂ) = 1)
    (hd : DifferentiableAt ℝ f S)
    (hmax : ∀ T ∈ densityDomain, f T ≤ f S) :
    densityTangentRestriction (fderiv ℝ f S) = 0 := by
  have hlocal : IsLocalMax (f ∘ densityChart S) 0 := by
    filter_upwards [eventually_densityChart_mem S hS ht] with X hX
    simpa only [Function.comp_apply, densityChart_zero] using hmax (densityChart S X) hX
  have hd' : HasFDerivAt f (fderiv ℝ f S) (densityChart S 0) := by simpa using hd.hasFDerivAt
  exact hlocal.hasFDerivAt_eq_zero
    (hd'.comp 0 (hasStrictFDerivAt_densityChart S 0).hasFDerivAt)

/-- Concavity makes a stationary density a global maximum, including singular competitors. -/
theorem stationary_isMaxOn
    (f : selfAdjoint (Matrix n n ℂ) → ℝ) (hf : ConcaveOn ℝ densityDomain f)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : S ∈ densityDomain)
    (hd : DifferentiableAt ℝ f S)
    (hstat : densityTangentRestriction (fderiv ℝ f S) = 0) :
    ∀ T ∈ densityDomain, f T ≤ f S := by
  intro T hT
  have hbound := concaveOn_le_tangent hf hS hT hd.hasFDerivAt
  have hzero : realTrace ((T - S : selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ) = 0 := by
    change realTrace ((T : Matrix n n ℂ) - (S : Matrix n n ℂ)) = 0
    rw [realTrace_sub, hT.2, hS.2, sub_self]
  let X : densityTangent (n := n) := ⟨T - S, (mem_densityTangent_iff _).mpr hzero⟩
  have hz := DFunLike.congr_fun hstat X
  change fderiv ℝ f S (T - S) = 0 at hz
  rwa [hz, add_zero] at hbound

/-- The actual constrained negative Hessian, retaining all ambient density directions. -/
def negativeTangentHessian (f : selfAdjoint (Matrix n n ℂ) → ℝ)
    (S : selfAdjoint (Matrix n n ℂ)) :
    densityTangent (n := n) →L[ℝ] (densityTangent (n := n) →L[ℝ] ℝ) :=
  densityTangentRestriction.comp
    ((-fderiv ℝ (fderiv ℝ f) S).comp (densityTangent (n := n)).subtypeL)

/-- Strict negative curvature constructs an isomorphism to the tangent dual. -/
def tangentHessianEquiv (f : selfAdjoint (Matrix n n ℂ) → ℝ)
    (S : selfAdjoint (Matrix n n ℂ))
    (hneg : ∀ X : densityTangent (n := n), X ≠ 0 →
      fderiv ℝ (fderiv ℝ f) S X X < 0) :
    densityTangent (n := n) ≃L[ℝ] (densityTangent (n := n) →L[ℝ] ℝ) :=
  positiveBilinearEquiv (negativeTangentHessian f S) (fun X hX => by
    change 0 < -fderiv ℝ (fderiv ℝ f) S X X
    exact neg_pos.mpr (hneg X hX))

set_option maxHeartbeats 800000 in
/-- The affine density chart preserves the actual Hessian in every tangent
direction; no support compression is made in this identity. -/
theorem densityChart_hessian_apply
    (f : selfAdjoint (Matrix n n ℂ) → ℝ) (S : selfAdjoint (Matrix n n ℂ))
    (hf : ContDiffAt ℝ ∞ f S) (X Y : densityTangent (n := n)) :
    fderiv ℝ (fderiv ℝ (fun Z => f (densityChart S Z))) 0 X Y =
      fderiv ℝ (fderiv ℝ f) S X Y := by
  have hdiff : ∀ᶠ Z in 𝓝 (0 : densityTangent (n := n)),
      DifferentiableAt ℝ f (densityChart S Z) := by
    have hevent := (hf.of_le (by simp : (1 : WithTop ℕ∞) ≤ ∞)).eventually (by norm_num)
    have hc : Tendsto (densityChart S) (𝓝 0) (𝓝 S) := by
      simpa only [densityChart_zero] using (hasStrictFDerivAt_densityChart S 0).continuousAt.tendsto
    filter_upwards [hc.eventually hevent] with Z hZ
    exact hZ.differentiableAt le_rfl
  have heq : (fun Z => densityTangentRestriction (fderiv ℝ f (densityChart S Z))) =ᶠ[𝓝 0]
      fderiv ℝ (fun Z => f (densityChart S Z)) := by
    filter_upwards [hdiff] with Z hZ
    exact (hZ.hasFDerivAt.comp Z (hasStrictFDerivAt_densityChart S Z).hasFDerivAt).fderiv.symm
  have hd : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) S) (densityChart S 0) := by
    simpa only [densityChart_zero] using
      ((hf.fderiv_right (by simp : (∞ : WithTop ℕ∞) + 1 ≤ ∞)).differentiableAt
        (by simp)).hasFDerivAt
  have hc := (densityTangentRestriction (n := n)).hasFDerivAt.comp 0
    (hd.comp 0 (hasStrictFDerivAt_densityChart S 0).hasFDerivAt)
  have hderiv := (hc.congr_of_eventuallyEq heq.symm).fderiv
  exact DFunLike.congr_fun (DFunLike.congr_fun hderiv X) Y

/-- The root regularizer has strictly negative actual Hessian on every
nonzero ambient Hermitian direction. -/
theorem tsallis_hessian_neg (θ : ℝ) (hθ : 0 < θ)
    (S X : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (hX : X ≠ 0) : fderiv ℝ (fderiv ℝ (tsallisPotential θ)) S X X < 0 := by
  rw [fderiv_fderiv_tsallisPotential_apply θ hθ.ne' S X X hS]
  apply neg_neg_of_pos
  rw [realTrace_mul_comm]
  exact negativeTsallisHessian_quadratic_pos θ hθ S X hS hX

end Density

section Implicit
variable {E V W : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The parameterized implicit function theorem, proved by inverting the
triangular map `(x,y) ↦ (x,G(x,y))`. -/
theorem exists_smooth_implicit_branch
    (G : E × V → W) (x₀ : E) (hG : ContDiffAt ℝ ∞ G (x₀, 0))
    (hzero : G (x₀, 0) = 0) (e : V ≃L[ℝ] W)
    (he : (fderiv ℝ G (x₀, 0)).comp (ContinuousLinearMap.inr ℝ E V) =
      e.toContinuousLinearMap) :
    ∃ g : E → V, g x₀ = 0 ∧ ContDiffAt ℝ ∞ g x₀ ∧
      ∀ᶠ x in 𝓝 x₀, G (x, g x) = 0 := by
  let D := fderiv ℝ G (x₀, 0)
  let eF : (E × V) ≃L[ℝ] (E × W) :=
    (ContinuousLinearEquiv.refl ℝ E).skewProd e
      (D.comp (ContinuousLinearMap.inl ℝ E V))
  let F : E × V → E × W := fun z => (z.1, G z)
  have hF : ContDiffAt ℝ ∞ F (x₀, 0) := contDiffAt_fst.prodMk hG
  have hFd : HasFDerivAt F eF.toContinuousLinearMap (x₀, 0) := by
    have h := (hasFDerivAt_fst (p := (x₀, (0 : V)))).prodMk
      (hG.differentiableAt (by simp)).hasFDerivAt
    have heF : eF.toContinuousLinearMap =
        (ContinuousLinearMap.fst ℝ E V).prod (fderiv ℝ G (x₀, 0)) := by
      apply ContinuousLinearMap.ext
      intro z
      apply Prod.ext
      · rfl
      · change e z.2 + D (z.1, 0) = D z
        have hv : D (0, z.2) = e z.2 := DFunLike.congr_fun he z.2
        rw [← hv, ← map_add]
        congr 1
        ext <;> simp
    rw [heF]
    exact h
  have hFzero : F (x₀, 0) = (x₀, 0) := by simp [F, hzero]
  let inv := hF.localInverse hFd (by simp : (1 : WithTop ℕ∞) ≤ ∞)
  have hi : ContDiffAt ℝ ∞ inv (x₀, 0) := by
    simpa only [hFzero] using hF.to_localInverse hFd (by simp : (1 : WithTop ℕ∞) ≤ ∞)
  have hi0 : inv (x₀, 0) = (x₀, 0) := by
    simpa only [hFzero] using hF.localInverse_apply_image hFd (by simp : (1 : WithTop ℕ∞) ≤ ∞)
  have hright : ∀ᶠ z in 𝓝 (x₀, (0 : W)), F (inv z) = z := by
    simpa only [hFzero] using
      (hF.hasStrictFDerivAt' hFd (by simp : (1 : WithTop ℕ∞) ≤ ∞)).eventually_right_inverse
  let g : E → V := fun x => (inv (x, 0)).2
  have hg : ContDiffAt ℝ ∞ g x₀ :=
    contDiffAt_snd.comp x₀ (hi.comp x₀ (contDiffAt_id.prodMk contDiffAt_const))
  refine ⟨g, ?_, hg, ?_⟩
  · change (inv (x₀, 0)).2 = 0
    rw [hi0]
  · have ht : Tendsto (fun x : E => (x, (0 : W))) (𝓝 x₀) (𝓝 (x₀, 0)) :=
      continuousAt_id.tendsto.prodMk_nhds continuousAt_const.tendsto
    filter_upwards [ht.eventually hright] with x hx
    have hfirst : (inv (x, 0)).1 = x := congrArg Prod.fst hx
    have hsecond : G ((inv (x, 0)).1, (inv (x, 0)).2) = 0 := congrArg Prod.snd hx
    rwa [hfirst] at hsecond

omit [CompleteSpace E] [CompleteSpace V] in
/-- Differentiating the proved implicit equation gives the actual response
as the inverse vertical derivative applied to the external forcing. -/
theorem implicit_branch_fderiv_apply
    (G : E × V → W) (g : E → V) (x₀ : E) (hg0 : g x₀ = 0)
    (hG : DifferentiableAt ℝ G (x₀, 0)) (hg : DifferentiableAt ℝ g x₀)
    (hroot : ∀ᶠ x in 𝓝 x₀, G (x, g x) = 0)
    (e : V ≃L[ℝ] W)
    (he : (fderiv ℝ G (x₀, 0)).comp (ContinuousLinearMap.inr ℝ E V) =
      e.toContinuousLinearMap) (v : E) :
    fderiv ℝ g x₀ v = -e.symm (fderiv ℝ G (x₀, 0) (v, 0)) := by
  have hG' : HasFDerivAt G (fderiv ℝ G (x₀, 0)) (x₀, g x₀) := by
    simpa only [hg0] using hG.hasFDerivAt
  have hc := hG'.comp x₀ ((hasFDerivAt_id x₀).prodMk hg.hasFDerivAt)
  have hz := (hasFDerivAt_const (𝕜 := ℝ) (0 : W) x₀).congr_of_eventuallyEq hroot
  have heq := DFunLike.congr_fun (hc.unique hz) v
  change fderiv ℝ G (x₀, 0) (v, fderiv ℝ g x₀ v) = 0 at heq
  have hv := DFunLike.congr_fun he (fderiv ℝ g x₀ v)
  change fderiv ℝ G (x₀, 0) (0, fderiv ℝ g x₀ v) = e (fderiv ℝ g x₀ v) at hv
  have hsum : fderiv ℝ G (x₀, 0) (v, 0) + e (fderiv ℝ g x₀ v) = 0 := by
    rw [← hv, ← map_add]
    simpa only [Prod.mk_add_mk, add_zero, zero_add] using heq
  apply e.injective
  simpa only [map_neg, e.apply_symm_apply] using (eq_neg_of_add_eq_zero_right hsum)

end Implicit

section StationaryBranch
variable {E V : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- Strictly negative actual Hessian gives a smooth stationary branch for a
jointly smooth scalar objective with arbitrary external parameters. -/
theorem exists_smooth_stationary_branch
    (f : E × V → ℝ) (x₀ : E) (hf : ContDiffAt ℝ ∞ f (x₀, 0))
    (hzero : fderiv ℝ (fun y => f (x₀, y)) 0 = 0)
    (hneg : ∀ v : V, v ≠ 0 →
      fderiv ℝ (fderiv ℝ (fun y => f (x₀, y))) 0 v v < 0) :
    ∃ g : E → V, g x₀ = 0 ∧ ContDiffAt ℝ ∞ g x₀ ∧
      ∀ᶠ x in 𝓝 x₀, fderiv ℝ (fun y => f (x, y)) (g x) = 0 := by
  letI : CompleteSpace V := FiniteDimensional.complete ℝ V
  let G : E × V → (V →L[ℝ] ℝ) := fun z => -fderiv ℝ (fun y => f (z.1, y)) z.2
  have haux : ContDiffAt ℝ ∞
      (Function.uncurry (fun (z : E × V) (y : V) => f (z.1, y))) ((x₀, 0), 0) :=
    hf.comp ((x₀, (0 : V)), (0 : V))
      ((contDiffAt_fst.comp ((x₀, (0 : V)), (0 : V)) contDiffAt_fst).prodMk contDiffAt_snd)
  have hG : ContDiffAt ℝ ∞ G (x₀, 0) :=
    (haux.fderiv contDiffAt_snd (by simp : (∞ : WithTop ℕ∞) + 1 ≤ ∞)).neg
  have hslice : ContDiffAt ℝ ∞ (fun y => f (x₀, y)) 0 :=
    hf.comp 0 (contDiffAt_const.prodMk contDiffAt_id)
  let A := -fderiv ℝ (fderiv ℝ (fun y => f (x₀, y))) 0
  have hA : ∀ v : V, v ≠ 0 → 0 < A v v := fun v hv => neg_pos.mpr (hneg v hv)
  let e := positiveBilinearEquiv A hA
  have he : (fderiv ℝ G (x₀, 0)).comp (ContinuousLinearMap.inr ℝ E V) =
      e.toContinuousLinearMap := by
    have hleft := (hG.differentiableAt (by simp)).hasFDerivAt.comp 0
      ((hasFDerivAt_const (x₀ : E) (0 : V)).prodMk (hasFDerivAt_id (0 : V)))
    have hright := ((hslice.fderiv_right (by simp : (∞ : WithTop ℕ∞) + 1 ≤ ∞)).differentiableAt
      (by simp)).hasFDerivAt.neg
    exact hleft.unique hright
  obtain ⟨g, hg0, hg, hstat⟩ := exists_smooth_implicit_branch G x₀ hG
    (by simp [G, hzero]) e he
  refine ⟨g, hg0, hg, ?_⟩
  filter_upwards [hstat] with x hx
  exact neg_eq_zero.mp hx

end StationaryBranch

section DensityBranch
variable {n E : Type*} [Fintype n] [DecidableEq n]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
local instance branchCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance branchNormedSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance
local instance branchFinite : FiniteDimensional ℝ (selfAdjoint (Matrix n n ℂ)) :=
  inferInstanceAs (FiniteDimensional ℝ (selfAdjoint.submodule ℝ (Matrix n n ℂ)))
local instance branchTangentGroup : NormedAddCommGroup (densityTangent (n := n)) := inferInstance
local instance branchTangentSpace : NormedSpace ℝ (densityTangent (n := n)) := inferInstance
local instance branchTangentFinite : FiniteDimensional ℝ (densityTangent (n := n)) := inferInstance

/-- A faithful maximizer of a jointly smooth concave density objective has a
smooth local optimizing branch whenever its actual constrained Hessian is
strictly negative. Every comparison is over the full ambient density set. -/
theorem exists_smooth_density_optimizer
    (f : E × selfAdjoint (Matrix n n ℂ) → ℝ) (x₀ : E)
    (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) (ht : realTrace (S : Matrix n n ℂ) = 1)
    (hf : ContDiffAt ℝ ∞ f (x₀, S))
    (hmax : ∀ T ∈ densityDomain, f (x₀, T) ≤ f (x₀, S))
    (hconc : ∀ᶠ x in 𝓝 x₀, ConcaveOn ℝ densityDomain (fun T => f (x, T)))
    (hneg : ∀ X : densityTangent (n := n), X ≠ 0 →
      fderiv ℝ (fderiv ℝ (fun Y => f (x₀, densityChart S Y))) 0 X X < 0) :
    ∃ s : E → selfAdjoint (Matrix n n ℂ),
      s x₀ = S ∧ ContDiffAt ℝ ∞ s x₀ ∧
      ContDiffAt ℝ ∞ (fun x => f (x, s x)) x₀ ∧
      ∀ᶠ x in 𝓝 x₀,
        (s x : Matrix n n ℂ).PosDef ∧ s x ∈ densityDomain ∧
        densityTangentRestriction (fderiv ℝ (fun T => f (x, T)) (s x)) = 0 ∧
        ∀ T ∈ densityDomain, f (x, T) ≤ f (x, s x) := by
  let φ : E × densityTangent (n := n) → ℝ := fun z => f (z.1, densityChart S z.2)
  have hchart : ContDiff ℝ ∞ (densityChart S) :=
    contDiff_const.add (densityTangent (n := n)).subtypeL.contDiff
  have hφ : ContDiffAt ℝ ∞ φ (x₀, 0) := by
    have hmap : ContDiffAt ℝ ∞
        (fun z : E × densityTangent (n := n) => (z.1, densityChart S z.2)) (x₀, 0) :=
      contDiffAt_fst.prodMk (hchart.contDiffAt.comp (x₀, 0) contDiffAt_snd)
    have hf' : ContDiffAt ℝ ∞ f (x₀, densityChart S 0) := by simpa using hf
    exact hf'.comp (x₀, 0) hmap
  have hslice : ContDiffAt ℝ ∞ (fun Y => φ (x₀, Y)) 0 :=
    hφ.comp 0 (contDiffAt_const.prodMk contDiffAt_id)
  have hlocal : IsLocalMax (fun Y => φ (x₀, Y)) 0 := by
    filter_upwards [eventually_densityChart_mem S hS ht] with Y hY
    simpa only [φ, densityChart_zero] using hmax (densityChart S Y) hY
  have hzero := hlocal.hasFDerivAt_eq_zero (hslice.differentiableAt (by simp)).hasFDerivAt
  obtain ⟨g, hg0, hg, hgstat⟩ := exists_smooth_stationary_branch φ x₀ hφ hzero hneg
  let s : E → selfAdjoint (Matrix n n ℂ) := fun x => densityChart S (g x)
  have hs0 : s x₀ = S := by simp [s, hg0]
  have hs : ContDiffAt ℝ ∞ s x₀ := hchart.contDiffAt.comp x₀ hg
  have hgraph : ContDiffAt ℝ ∞ (fun x => (x, s x)) x₀ := contDiffAt_id.prodMk hs
  have hvalue : ContDiffAt ℝ ∞ (fun x => f (x, s x)) x₀ := by
    have hf' : ContDiffAt ℝ ∞ f (x₀, s x₀) := by rwa [hs0]
    exact hf'.comp x₀ hgraph
  have hpos : ∀ᶠ x in 𝓝 x₀, (s x : Matrix n n ℂ).PosDef := by
    have hs' : Tendsto s (𝓝 x₀) (𝓝 S) := by simpa only [hs0] using hs.continuousAt.tendsto
    exact hs'.eventually (eventually_posDef_of_posDef S hS)
  have hdiff : ∀ᶠ x in 𝓝 x₀, DifferentiableAt ℝ f (x, s x) := by
    have hevent := (hf.of_le (by simp : (1 : WithTop ℕ∞) ≤ ∞)).eventually (by norm_num)
    have hgraph' : Tendsto (fun x => (x, s x)) (𝓝 x₀) (𝓝 (x₀, S)) := by
      simpa only [hs0] using hgraph.continuousAt.tendsto
    filter_upwards [hgraph'.eventually hevent] with x hx
    exact hx.differentiableAt le_rfl
  refine ⟨s, hs0, hs, hvalue, ?_⟩
  filter_upwards [hpos, hdiff, hconc, hgstat] with x hxpos hxdiff hxconc hxstat
  have hxs : s x ∈ densityDomain :=
    ⟨hxpos.posSemidef, (densityChart_trace S (g x)).trans ht⟩
  have hdx : DifferentiableAt ℝ (fun T => f (x, T)) (s x) :=
    hxdiff.comp (s x) ((differentiableAt_const x).prodMk differentiableAt_id)
  have hstationary : densityTangentRestriction (fderiv ℝ (fun T => f (x, T)) (s x)) = 0 := by
    have hchain := hdx.hasFDerivAt.comp (g x) (hasStrictFDerivAt_densityChart S (g x)).hasFDerivAt
    have heq := hchain.fderiv
    change fderiv ℝ (fun Y => φ (x, Y)) (g x) =
      densityTangentRestriction (fderiv ℝ (fun T => f (x, T)) (s x)) at heq
    exact heq.symm.trans hxstat
  exact ⟨hxpos, hxs, hstationary, stationary_isMaxOn _ hxconc _ hxs hdx hstationary⟩

/-- Any selected optimizer agrees locally with the implicit branch. Strict
concavity supplies the uniqueness, so the selected optimizer and optimized
value are genuinely smooth functions of the external parameter. -/
theorem contDiffAt_density_optimizer
    (f : E × selfAdjoint (Matrix n n ℂ) → ℝ) (x₀ : E)
    (σ : E → selfAdjoint (Matrix n n ℂ))
    (hS : (σ x₀ : Matrix n n ℂ).PosDef)
    (hf : ContDiffAt ℝ ∞ f (x₀, σ x₀))
    (hσ : ∀ᶠ x in 𝓝 x₀, σ x ∈ densityDomain ∧
      ∀ T ∈ densityDomain, f (x, T) ≤ f (x, σ x))
    (hconc : ∀ᶠ x in 𝓝 x₀, StrictConcaveOn ℝ densityDomain (fun T => f (x, T)))
    (hneg : ∀ X : densityTangent (n := n), X ≠ 0 →
      fderiv ℝ (fderiv ℝ (fun Y => f (x₀, densityChart (σ x₀) Y))) 0 X X < 0) :
    ContDiffAt ℝ ∞ σ x₀ ∧ ContDiffAt ℝ ∞ (fun x => f (x, σ x)) x₀ := by
  have hσ₀ := hσ.self_of_nhds
  obtain ⟨s, _, hs, hv, hopt⟩ := exists_smooth_density_optimizer f x₀ (σ x₀) hS
    hσ₀.1.2 hf hσ₀.2 (hconc.mono fun _ h => h.concaveOn) hneg
  have heq : σ =ᶠ[𝓝 x₀] s := by
    filter_upwards [hσ, hconc, hopt] with x hx hc ho
    exact hc.eq_of_isMaxOn hx.2 ho.2.2.2 hx.1 ho.2.1
  refine ⟨hs.congr_of_eventuallyEq heq, hv.congr_of_eventuallyEq ?_⟩
  filter_upwards [heq] with x hx
  rw [hx]

/-- The actual supremum over all densities is smooth near a faithful
nondegenerate maximizer; no optimizer selection is assumed. -/
theorem contDiffAt_density_sup
    (f : E × selfAdjoint (Matrix n n ℂ) → ℝ) (x₀ : E)
    (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) (ht : realTrace (S : Matrix n n ℂ) = 1)
    (hf : ContDiffAt ℝ ∞ f (x₀, S))
    (hmax : ∀ T ∈ densityDomain, f (x₀, T) ≤ f (x₀, S))
    (hconc : ∀ᶠ x in 𝓝 x₀, ConcaveOn ℝ densityDomain (fun T => f (x, T)))
    (hneg : ∀ X : densityTangent (n := n), X ≠ 0 →
      fderiv ℝ (fderiv ℝ (fun Y => f (x₀, densityChart S Y))) 0 X X < 0) :
    ContDiffAt ℝ ∞
      (fun x => sSup ((fun T => f (x, T)) '' (densityDomain (n := n)))) x₀ := by
  obtain ⟨s, _, _, hv, hopt⟩ := exists_smooth_density_optimizer f x₀ S hS ht hf hmax hconc hneg
  apply hv.congr_of_eventuallyEq
  filter_upwards [hopt] with x hx
  apply IsGreatest.csSup_eq
  refine ⟨⟨s x, hx.2.1, rfl⟩, ?_⟩
  rintro _ ⟨T, hT, rfl⟩
  exact hx.2.2.2 T hT

end DensityBranch

end HigherRankKS.OptimizerResponse
