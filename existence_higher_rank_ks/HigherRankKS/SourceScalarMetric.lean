import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Tactic

/-!
# The scalar metric estimate from homogeneity and concavity

The derivatives in this file are the actual Fréchet derivatives.  Euler's
identities are obtained by differentiating the power-homogeneity identity;
the derivative bound then follows by testing the negative Hessian on a
two-dimensional pencil.  No derivative estimate is supplied as an oracle.
-/

open Set Filter
open scoped Topology ContDiff

noncomputable section
namespace HigherRankKS.SourceScalarMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Euler's identity follows by differentiating the actual function along
the positive ray through the basepoint. -/
theorem euler_first (f : E → ℝ) (α : ℝ) (x : E)
    (hfd : DifferentiableAt ℝ f x)
    (hhom : ∀ t : ℝ, 0 < t → f (t • x) = t ^ α * f x) :
    fderiv ℝ f x x = α * f x := by
  have hleft : HasDerivAt (fun t : ℝ => f (t • x)) (fderiv ℝ f x x) 1 := by
    have hfd' : HasFDerivAt f (fderiv ℝ f x) ((1 : ℝ) • x) := by simpa using hfd.hasFDerivAt
    simpa only [one_smul] using
      hfd'.comp_hasDerivAt (1 : ℝ) ((hasDerivAt_id (1 : ℝ)).smul_const x)
  have hright : HasDerivAt (fun t : ℝ => t ^ α * f x) (α * f x) 1 := by
    simpa using (Real.hasDerivAt_rpow_const (x := (1 : ℝ)) (p := α)
      (Or.inl one_ne_zero)).mul_const (f x)
  have heq : (fun t : ℝ => f (t • x)) =ᶠ[𝓝 1] (fun t => t ^ α * f x) := by
    filter_upwards [eventually_gt_nhds (by norm_num : (0 : ℝ) < 1)] with t ht
    exact hhom t ht
  exact (hleft.congr_of_eventuallyEq heq.symm).unique hright

/-- Differentiating Euler's identity in the basepoint gives the radial
mixed Hessian identity.  Homogeneity is required on a neighborhood only. -/
theorem euler_second (f : E → ℝ) (α : ℝ) (x U : E)
    (hf : ContDiffAt ℝ 2 f x)
    (hhom : ∀ᶠ y in 𝓝 x, ∀ t : ℝ, 0 < t → f (t • y) = t ^ α * f y) :
    fderiv ℝ (fderiv ℝ f) x U x = (α - 1) * fderiv ℝ f x U := by
  have hd : DifferentiableAt ℝ f x := hf.differentiableAt (by norm_num)
  have hdd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (show (1 : WithTop ℕ∞) + 1 ≤ 2 by norm_num)).differentiableAt
      (by norm_num)
  have heuler : (fun y => fderiv ℝ f y y) =ᶠ[𝓝 x] (fun y => α * f y) := by
    filter_upwards [hhom, hf.eventually (by simp)] with y hy hfy
    exact euler_first f α y (hfy.differentiableAt (by norm_num)) hy
  have hleft := hdd.hasFDerivAt.clm_apply (hasFDerivAt_id (𝕜 := ℝ) x)
  have hright := hd.hasFDerivAt.const_mul α
  have heq := congrArg (fun L : E →L[ℝ] ℝ => L U)
    ((hleft.congr_of_eventuallyEq heuler.symm).unique hright)
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, id_eq] at heq
  linarith

/-- Cauchy--Schwarz for a negative semidefinite symmetric continuous
bilinear form, including degenerate forms. -/
theorem negative_bilinear_cauchy (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hsym : ∀ U V, B U V = B V U) (hneg : ∀ U, B U U ≤ 0) (U V : E) :
    (B U V) ^ 2 ≤ B U U * B V V := by
  have hpoly : ∀ t : ℝ, B V V * (t * t) + (2 * B U V) * t + B U U ≤ 0 := by
    intro t
    have h := hneg (U + t • V)
    simp only [map_add, map_smul, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul, hsym V U] at h
    nlinarith
  have hdisc := discrim_le_zero_of_nonpos hpoly
  unfold discrim at hdisc
  nlinarith

/-- A concave homogeneous function of degree below one pays for its
actual first derivative with its actual negative Hessian. -/
theorem homogeneous_derivative_sq_le (f : E → ℝ) {α : ℝ} (hα : α < 1)
    (x U : E) (hf : ContDiffAt ℝ 2 f x)
    (hhom : ∀ᶠ y in 𝓝 x, ∀ t : ℝ, 0 < t → f (t • y) = t ^ α * f y)
    (hneg : ∀ V, fderiv ℝ (fderiv ℝ f) x V V ≤ 0) :
    |fderiv ℝ f x U| ^ 2 ≤ α / (1 - α) * f x *
      (-fderiv ℝ (fderiv ℝ f) x U U) := by
  have hsym := hf.isSymmSndFDerivAt (by norm_num)
  have hfirst := euler_first f α x (hf.differentiableAt (by norm_num))
    (Filter.Eventually.self_of_nhds hhom)
  have hradial := euler_second f α x x hf hhom
  rw [hfirst] at hradial
  have hcross := euler_second f α x U hf hhom
  have hcs := negative_bilinear_cauchy (fderiv ℝ (fderiv ℝ f) x)
    (fun V W => hsym.eq V W) hneg U x
  rw [hcross, hradial] at hcs
  have hβ : 0 < 1 - α := sub_pos.mpr hα
  have hscaled : (1 - α) * ((1 - α) * (fderiv ℝ f x U) ^ 2) ≤
      (1 - α) * (α * f x * (-fderiv ℝ (fderiv ℝ f) x U U)) := by
    nlinarith [hcs]
  have hcancel := (mul_le_mul_iff_right₀ hβ).mp hscaled
  rw [sq_abs]
  calc
    (fderiv ℝ f x U) ^ 2 ≤
        (α * f x * (-fderiv ℝ (fderiv ℝ f) x U U)) / (1 - α) := by
      apply (le_div_iff₀ hβ).mpr
      nlinarith [hcancel]
    _ = _ := by ring

/-- Centering a degree-one function removes exactly its scalar first
derivative.  This is obtained from Euler's identity, not assumed. -/
theorem degree_one_centered_first (g : E → ℝ) (x U : E) (a : ℝ)
    (hg : DifferentiableAt ℝ g x)
    (hhom : ∀ t : ℝ, 0 < t → g (t • x) = t * g x) :
    fderiv ℝ g x (U - a • x) = fderiv ℝ g x U - a * g x := by
  have heuler := euler_first g 1 x hg (by simpa using hhom)
  simp only [one_mul] at heuler
  rw [map_sub, map_smul, smul_eq_mul, heuler]

/-- The Hessian of a degree-one function is unchanged by removing any
radial component from a variation. -/
theorem degree_one_centered_second (g : E → ℝ) (x U : E) (a : ℝ)
    (hg : ContDiffAt ℝ 2 g x)
    (hhom : ∀ᶠ y in 𝓝 x, ∀ t : ℝ, 0 < t → g (t • y) = t * g y) :
    fderiv ℝ (fderiv ℝ g) x (U - a • x) (U - a • x) =
      fderiv ℝ (fderiv ℝ g) x U U := by
  have hradial (V : E) : fderiv ℝ (fderiv ℝ g) x V x = 0 := by
    simpa using euler_second g 1 x V hg (by simpa using hhom)
  have hsym := hg.isSymmSndFDerivAt (by norm_num)
  have hleft (V : E) : fderiv ℝ (fderiv ℝ g) x x V = 0 := by
    rw [hsym.eq, hradial]
  simp only [map_sub, map_smul, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, hradial, hleft, mul_zero,
    sub_zero]

/-- The actual directional Hessian is the actual second derivative along
the affine line. -/
theorem iteratedDeriv_two_line (f : E → ℝ) (x V : E)
    (hf : ContDiffAt ℝ 2 f x) :
    iteratedDeriv 2 (fun t : ℝ => f (x + t • V)) 0 =
      fderiv ℝ (fderiv ℝ f) x V V := by
  let γ : ℝ → E := fun t => x + t • V
  have hγ : ContDiff ℝ 2 γ := contDiff_const.add (contDiff_id.smul contDiff_const)
  have hdγ : deriv γ = fun _ => V := by
    funext t
    simpa only [one_smul, zero_add] using
      ((hasDerivAt_const t x).add ((hasDerivAt_id t).smul_const V)).deriv
  have hddγ : iteratedDeriv 2 γ 0 = 0 := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, hdγ]
    simp
  have hfγ : ContDiffAt ℝ 2 f (γ 0) := by simpa [γ] using hf
  have h := iteratedDeriv_vcomp_two hfγ hγ.contDiffAt
  simpa only [γ, Function.comp_def, zero_smul, add_zero, hdγ, hddγ,
    iteratedFDeriv_two_apply, map_zero, add_zero] using h

/-- Ordinary concavity on an open set implies that the actual Hessian
is negative semidefinite.  This follows from monotonicity of the derivative
on every affine line through the point. -/
theorem hessian_nonpos_of_concave (f : E → ℝ) {D : Set E} (hD : IsOpen D)
    (hconc : ConcaveOn ℝ D f) (hd : ∀ y ∈ D, DifferentiableAt ℝ f y)
    {x : E} (hx : x ∈ D) (hf : ContDiffAt ℝ 2 f x) (V : E) :
    fderiv ℝ (fderiv ℝ f) x V V ≤ 0 := by
  let γ : ℝ → E := fun t => x + t • V
  let S : Set ℝ := γ ⁻¹' D
  have hγ : ContDiff ℝ 2 γ := contDiff_const.add (contDiff_id.smul contDiff_const)
  have hS : IsOpen S := hD.preimage hγ.continuous
  have hzero : (0 : ℝ) ∈ S := by simpa [S, γ] using hx
  have haffine (s t a b : ℝ) (hab : a + b = 1) :
      γ (a • s + b • t) = a • γ s + b • γ t := by
    dsimp [γ]
    calc
      x + (a • s + b • t) • V = (a + b) • x + (a * s + b * t) • V := by rw [hab, one_smul]; rfl
      _ = _ := by module
  have hc : ConcaveOn ℝ S (fun t => f (γ t)) := by
    constructor
    · intro s hs t ht a b ha hb hab
      change γ (a • s + b • t) ∈ D
      rw [haffine s t a b hab]
      exact hconc.1 hs ht ha hb hab
    · intro s hs t ht a b ha hb hab
      change a • f (γ s) + b • f (γ t) ≤ f (γ (a • s + b • t))
      rw [haffine s t a b hab]
      exact hconc.2 hs ht ha hb hab
  have hdiff (t : ℝ) (ht : t ∈ S) : DifferentiableAt ℝ (fun t => f (γ t)) t :=
    (hd (γ t) ht).comp t (hγ.differentiable (by norm_num) t)
  have hanti := hc.antitoneOn_deriv hdiff
  have hnonpos := hanti.derivWithin_nonpos (x := (0 : ℝ))
  rw [derivWithin_of_isOpen hS hzero] at hnonpos
  have hhess := iteratedDeriv_two_line f x V hf
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one] at hhess
  rw [← hhess]
  exact hnonpos


def source (β : ℝ) (p : E →L[ℝ] ℝ) (f : E → ℝ) (x : E) : ℝ :=
  (p x) ^ β * f x

theorem source_contDiffAt (β : ℝ) (p : E →L[ℝ] ℝ) (f : E → ℝ) (x : E)
    (hp : 0 < p x) (hf : ContDiffAt ℝ 2 f x) :
    ContDiffAt ℝ 2 (source β p f) x := by
  exact ((Real.contDiffAt_rpow_const_of_ne hp.ne').comp x p.contDiff.contDiffAt).mul hf

/-- Multiplying degrees `β` and `1-β` gives actual degree-one
homogeneity of the source in a neighborhood of a positive trace point. -/
theorem source_homogeneous (β : ℝ) (p : E →L[ℝ] ℝ) (f : E → ℝ) (x : E)
    (hp : 0 < p x)
    (hhom : ∀ᶠ y in 𝓝 x, ∀ t : ℝ, 0 < t → f (t • y) = t ^ (1 - β) * f y) :
    ∀ᶠ y in 𝓝 x, ∀ t : ℝ, 0 < t → source β p f (t • y) = t * source β p f y := by
  filter_upwards [hhom, p.continuous.continuousAt.eventually
    (isOpen_Ioi.mem_nhds hp)] with y hy hpy
  intro t ht
  simp only [source, map_smul, smul_eq_mul, hy t ht,
    Real.mul_rpow ht.le hpy.le]
  have hpow : t ^ β * t ^ (1 - β) = t := by
    rw [← Real.rpow_add ht]
    simp
  calc
    (t ^ β * (p y) ^ β) * (t ^ (1 - β) * f y) =
        (t ^ β * t ^ (1 - β)) * ((p y) ^ β * f y) := by ring
    _ = _ := by rw [hpow]

/-- On a trace-zero variation the scalar trace factor is constant along
the entire affine line, so the first derivative scales exactly. -/
theorem source_first_on_kernel (β : ℝ) (p : E →L[ℝ] ℝ) (f : E → ℝ)
    (x V : E) (hp : 0 < p x) (hf : ContDiffAt ℝ 2 f x) (hV : p V = 0) :
    fderiv ℝ (source β p f) x V = (p x) ^ β * fderiv ℝ f x V := by
  have hline : HasDerivAt (fun t : ℝ => x + t • V) V 0 := by
    simpa only [one_smul, zero_add] using (hasDerivAt_const (0 : ℝ) x).add
      ((hasDerivAt_id (0 : ℝ)).smul_const V)
  have hs := (source_contDiffAt β p f x hp hf).differentiableAt (by norm_num)
  have hds : HasDerivAt (fun t : ℝ => source β p f (x + t • V))
      (fderiv ℝ (source β p f) x V) 0 := by
    have hs' : HasFDerivAt (source β p f) (fderiv ℝ (source β p f) x)
        (x + (0 : ℝ) • V) := by simpa only [zero_smul, add_zero] using hs.hasFDerivAt
    exact hs'.comp_hasDerivAt 0 hline
  have hdf : HasDerivAt (fun t : ℝ => f (x + t • V)) (fderiv ℝ f x V) 0 := by
    have hf' : HasFDerivAt f (fderiv ℝ f x) (x + (0 : ℝ) • V) := by
      simpa only [zero_smul, add_zero] using (hf.differentiableAt (by norm_num)).hasFDerivAt
    exact hf'.comp_hasDerivAt 0 hline
  have heq : (fun t : ℝ => source β p f (x + t • V)) =
      fun t => (p x) ^ β * f (x + t • V) := by
    funext t
    simp [source, hV]
  rw [heq] at hds
  exact hds.unique (hdf.const_mul ((p x) ^ β))

/-- The same constant-along-line argument applies to the actual Hessian. -/
theorem source_second_on_kernel (β : ℝ) (p : E →L[ℝ] ℝ) (f : E → ℝ)
    (x V : E) (hp : 0 < p x) (hf : ContDiffAt ℝ 2 f x) (hV : p V = 0) :
    fderiv ℝ (fderiv ℝ (source β p f)) x V V =
      (p x) ^ β * fderiv ℝ (fderiv ℝ f) x V V := by
  have heq : (fun t : ℝ => source β p f (x + t • V)) =
      fun t => (p x) ^ β * f (x + t • V) := by
    funext t
    simp [source, hV]
  have hline : ContDiffAt ℝ 2 (fun t : ℝ => f (x + t • V)) 0 := by
    have hf' : ContDiffAt ℝ 2 f (x + (0 : ℝ) • V) := by
      simpa only [zero_smul, add_zero] using hf
    exact hf'.comp 0 (contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const))
  rw [← iteratedDeriv_two_line (source β p f) x V (source_contDiffAt β p f x hp hf),
    heq, iteratedDeriv_const_mul hline, iteratedDeriv_two_line f x V hf]


theorem source_centered_derivative_sq_le (p : E →L[ℝ] ℝ) (f : E → ℝ)
    {β : ℝ} (hβ : 0 < β) (x U : E) (hp : 0 < p x)
    (hf : ContDiffAt ℝ 2 f x)
    (hhom : ∀ᶠ y in 𝓝 x, ∀ t : ℝ, 0 < t → f (t • y) = t ^ (1 - β) * f y)
    (hneg : ∀ V, fderiv ℝ (fderiv ℝ f) x V V ≤ 0) :
    |fderiv ℝ (source β p f) x U - (p U / p x) * source β p f x| ^ 2 ≤
      (1 - β) / β * source β p f x *
        (-fderiv ℝ (fderiv ℝ (source β p f)) x U U) := by
  let a : ℝ := p U / p x
  let V : E := U - a • x
  have hV : p V = 0 := by
    simp only [V, a, map_sub, map_smul, smul_eq_mul]
    rw [div_mul_cancel₀ _ hp.ne', sub_self]
  have hg := source_contDiffAt β p f x hp hf
  have hghom := source_homogeneous β p f x hp hhom
  have hfirst := degree_one_centered_first (source β p f) x U a
    (hg.differentiableAt (by norm_num)) (Filter.Eventually.self_of_nhds hghom)
  have hsecond := degree_one_centered_second (source β p f) x U a hg hghom
  have hkernel₁ := source_first_on_kernel β p f x V hp hf hV
  have hkernel₂ := source_second_on_kernel β p f x V hp hf hV
  have hbound := homogeneous_derivative_sq_le f (by linarith : 1 - β < 1) x V hf hhom hneg
  have hscaled := mul_le_mul_of_nonneg_left hbound (sq_nonneg ((p x) ^ β))
  change |fderiv ℝ (source β p f) x U - a * source β p f x| ^ 2 ≤ _
  rw [← hfirst, ← hsecond]
  change |fderiv ℝ (source β p f) x V| ^ 2 ≤
    (1 - β) / β * source β p f x * (-fderiv ℝ (fderiv ℝ (source β p f)) x V V)
  rw [hkernel₁, hkernel₂, source, sq_abs]
  rw [sq_abs] at hscaled
  have hden : 1 - (1 - β) = β := by ring
  rw [hden] at hscaled
  nlinarith [hscaled]

/-- A version stated using ordinary concavity and smoothness on an open
carrier domain, with no derivative inequalities among the hypotheses. -/
theorem source_centered_derivative_sq_le_of_concave
    (p : E →L[ℝ] ℝ) (f : E → ℝ) {D : Set E} (hD : IsOpen D)
    (hconc : ConcaveOn ℝ D f) (hf : ContDiffOn ℝ 2 f D)
    {β : ℝ} (hβ : 0 < β)
    (hhom : ∀ y ∈ D, ∀ t : ℝ, 0 < t → f (t • y) = t ^ (1 - β) * f y)
    (x U : E) (hx : x ∈ D) (hp : 0 < p x) :
    |fderiv ℝ (source β p f) x U - (p U / p x) * source β p f x| ^ 2 ≤
      (1 - β) / β * source β p f x *
        (-fderiv ℝ (fderiv ℝ (source β p f)) x U U) := by
  have hfx : ContDiffAt ℝ 2 f x := (hf x hx).contDiffAt (hD.mem_nhds hx)
  apply source_centered_derivative_sq_le p f hβ x U hp hfx
  · filter_upwards [hD.mem_nhds hx] with y hy
    exact hhom y hy
  · intro V
    exact hessian_nonpos_of_concave f hD hconc
      (fun y hy => ((hf y hy).contDiffAt (hD.mem_nhds hy)).differentiableAt (by norm_num))
      hx hfx V

/-- The same hypotheses make the actual source curvature cost nonnegative. -/
theorem source_negative_second_nonneg (β : ℝ) (p : E →L[ℝ] ℝ) (f : E → ℝ)
    (x U : E) (hp : 0 < p x) (hf : ContDiffAt ℝ 2 f x)
    (hhom : ∀ᶠ y in 𝓝 x, ∀ t : ℝ, 0 < t → f (t • y) = t ^ (1 - β) * f y)
    (hneg : ∀ V, fderiv ℝ (fderiv ℝ f) x V V ≤ 0) :
    0 ≤ -fderiv ℝ (fderiv ℝ (source β p f)) x U U := by
  let a : ℝ := p U / p x
  let V : E := U - a • x
  have hV : p V = 0 := by
    simp only [V, a, map_sub, map_smul, smul_eq_mul]
    rw [div_mul_cancel₀ _ hp.ne', sub_self]
  have hcenter := degree_one_centered_second (source β p f) x U a
    (source_contDiffAt β p f x hp hf) (source_homogeneous β p f x hp hhom)
  rw [← hcenter]
  change 0 ≤ -fderiv ℝ (fderiv ℝ (source β p f)) x V V
  rw [source_second_on_kernel β p f x V hp hf hV]
  exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos (Real.rpow_pos_of_pos hp β).le (hneg V))

end HigherRankKS.SourceScalarMetric
