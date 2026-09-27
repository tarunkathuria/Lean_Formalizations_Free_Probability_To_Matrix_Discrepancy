import HigherRankKS.MatrixPowerDifferential
import HigherRankKS.CarrierDerivative

/-!
# Actual centered derivatives of the nonlinear carrier

The trace normalization removes the radial direction exactly. Both identities
below concern the actual Fréchet derivatives, obtained by smoothness and Euler's
identity; no derivative or Hessian formula is assumed.
-/

open Matrix MatrixSpencer Set Filter
open scoped Topology ContDiff MatrixOrder ComplexOrder Matrix.Norms.L2Operator

noncomputable section
namespace HigherRankKS.CarrierMetric

section Normalization
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem hasDerivAt_line (f : E → F) (x V : E) (hf : DifferentiableAt ℝ f x) :
    HasDerivAt (fun t : ℝ => f (x + t • V)) (fderiv ℝ f x V) 0 := by
  have hd : HasFDerivAt f (fderiv ℝ f x) (x + (0 : ℝ) • V) := by
    simpa only [zero_smul, add_zero] using hf.hasFDerivAt
  simpa only [zero_add, one_smul] using hd.comp_hasDerivAt (0 : ℝ)
    ((hasDerivAt_const (0 : ℝ) x).add ((hasDerivAt_id (0 : ℝ)).smul_const V))

private def weighted (β : ℝ) (p : E →L[ℝ] ℝ) (f : E → F) (x : E) : F :=
  (p x) ^ β • f x

private theorem weighted_smooth (β : ℝ) (p : E →L[ℝ] ℝ) (f : E → F)
    (x : E) (hp : 0 < p x) (hf : ContDiffAt ℝ 2 f x) :
    ContDiffAt ℝ 2 (weighted β p f) x :=
  ((Real.contDiffAt_rpow_const_of_ne hp.ne').comp x p.contDiff.contDiffAt).smul hf

private theorem first_on_kernel (β : ℝ) (p : E →L[ℝ] ℝ) (f : E → F)
    (x V : E) (hp : 0 < p x) (hf : ContDiffAt ℝ 2 f x) (hV : p V = 0) :
    fderiv ℝ (weighted β p f) x V = (p x) ^ β • fderiv ℝ f x V := by
  have hline : HasDerivAt (fun t : ℝ => x + t • V) V 0 := by
    simpa only [one_smul, zero_add] using (hasDerivAt_const (0 : ℝ) x).add
      ((hasDerivAt_id (0 : ℝ)).smul_const V)
  have hds : HasDerivAt (fun t : ℝ => weighted β p f (x + t • V))
      (fderiv ℝ (weighted β p f) x V) 0 := by
    have hd : HasFDerivAt (weighted β p f) (fderiv ℝ (weighted β p f) x)
        (x + (0 : ℝ) • V) := by
      simpa using ((weighted_smooth β p f x hp hf).differentiableAt (by norm_num)).hasFDerivAt
    exact hd.comp_hasDerivAt 0 hline
  have hdf : HasDerivAt (fun t : ℝ => f (x + t • V)) (fderiv ℝ f x V) 0 := by
    have hd : HasFDerivAt f (fderiv ℝ f x) (x + (0 : ℝ) • V) := by
      simpa using (hf.differentiableAt (by norm_num)).hasFDerivAt
    exact hd.comp_hasDerivAt 0 hline
  have heq : (fun t : ℝ => weighted β p f (x + t • V)) =
      fun t => (p x) ^ β • f (x + t • V) := by
    funext t
    simp [weighted, hV]
  rw [heq] at hds
  exact hds.unique (hdf.const_smul ((p x) ^ β))

private theorem second_on_kernel (β : ℝ) (p : E →L[ℝ] ℝ) (f : E → F)
    (x V : E) (hp : 0 < p x) (hf : ContDiffAt ℝ 2 f x) (hV : p V = 0) :
    fderiv ℝ (fderiv ℝ (weighted β p f)) x V V =
      (p x) ^ β • fderiv ℝ (fderiv ℝ f) x V V := by
  have heq : (fun t : ℝ => weighted β p f (x + t • V)) =
      fun t => (p x) ^ β • f (x + t • V) := by
    funext t
    simp [weighted, hV]
  have hline : ContDiffAt ℝ 2 (fun t : ℝ => f (x + t • V)) 0 := by
    have hf' : ContDiffAt ℝ 2 f (x + (0 : ℝ) • V) := by simpa using hf
    exact hf'.comp 0 (contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const))
  rw [← MatrixPowerDifferential.iteratedDeriv_two_line (weighted β p f) x V
      (weighted_smooth β p f x hp hf), heq]
  have hh := iteratedDeriv_const_smul hline ((p x) ^ β)
  change iteratedDeriv 2 (((p x) ^ β) • fun t : ℝ => f (x + t • V)) 0 = _
  rw [hh, MatrixPowerDifferential.iteratedDeriv_two_line f x V hf]

private theorem weighted_homogeneous (β : ℝ) (p : E →L[ℝ] ℝ) (f : E → F)
    (x : E) (hp : 0 < p x)
    (hhom : ∀ᶠ y in 𝓝 x, ∀ t : ℝ, 0 < t → f (t • y) = t ^ (1 - β) • f y) :
    ∀ᶠ y in 𝓝 x, ∀ t : ℝ, 0 < t → weighted β p f (t • y) = t • weighted β p f y := by
  filter_upwards [hhom, p.continuous.continuousAt.eventually
    (isOpen_Ioi.mem_nhds hp)] with y hy hpy
  intro t ht
  simp only [weighted, map_smul, smul_eq_mul, hy t ht, Real.mul_rpow ht.le hpy.le,
    smul_smul]
  congr 1
  have hpow : t ^ β * t ^ (1 - β) = t := by
    rw [← Real.rpow_add ht]
    simp
  calc
    (t ^ β * (p y) ^ β) * t ^ (1 - β) =
        (t ^ β * t ^ (1 - β)) * (p y) ^ β := by ring
    _ = _ := by rw [hpow]

/-- Exact trace-normalized first and second derivatives for a homogeneous power. -/
theorem centered_derivatives (β : ℝ) (p : E →L[ℝ] ℝ) (f : E → F)
    (x U : E) (hp : 0 < p x) (hf : ContDiffAt ℝ 2 f x)
    (hhom : ∀ᶠ y in 𝓝 x, ∀ t : ℝ, 0 < t → f (t • y) = t ^ (1 - β) • f y) :
    let a := p U / p x
    let V := U - a • x
    fderiv ℝ (fun y => (p y) ^ β • f y) x U - a • ((p x) ^ β • f x) =
        (p x) ^ β • fderiv ℝ f x V ∧
      fderiv ℝ (fderiv ℝ (fun y => (p y) ^ β • f y)) x U U =
        (p x) ^ β • fderiv ℝ (fderiv ℝ f) x V V := by
  let a := p U / p x
  let V := U - a • x
  have hV : p V = 0 := by
    simp only [V, a, map_sub, map_smul, smul_eq_mul]
    rw [div_mul_cancel₀ _ hp.ne', sub_self]
  have hg := weighted_smooth β p f x hp hf
  have hghom := weighted_homogeneous β p f x hp hhom
  have hfirst : fderiv ℝ (weighted β p f) x V =
      fderiv ℝ (weighted β p f) x U - a • weighted β p f x := by
    have heuler := MatrixPowerDifferential.euler_first (weighted β p f) 1 x
      (hg.differentiableAt (by norm_num)) (by simpa using Filter.Eventually.self_of_nhds hghom)
    simpa [V, map_sub, map_smul] using congrArg
      (fun z : F => fderiv ℝ (weighted β p f) x U - a • z) heuler
  have hsecond : fderiv ℝ (fderiv ℝ (weighted β p f)) x V V =
      fderiv ℝ (fderiv ℝ (weighted β p f)) x U U := by
    have hradial (W : E) : fderiv ℝ (fderiv ℝ (weighted β p f)) x W x = 0 := by
      simpa using MatrixPowerDifferential.euler_second (weighted β p f) 1 x W hg
        (by simpa using hghom)
    have hsym := hg.isSymmSndFDerivAt (by norm_num)
    have hleft (W : E) : fderiv ℝ (fderiv ℝ (weighted β p f)) x x W = 0 := by
      rw [hsym.eq, hradial]
    simp only [V, map_sub, map_smul, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply, hradial, hleft, smul_zero, sub_zero]
  exact ⟨hfirst.symm.trans (first_on_kernel β p f x V hp hf hV),
    hsecond.symm.trans (second_on_kernel β p f x V hp hf hV)⟩

end Normalization

variable {n : Type*} [Fintype n] [DecidableEq n]
local instance carrierMetricCStar : CStarAlgebra (Matrix n n ℂ) := {}

/-- Actual carrier as a map from Hermitian inputs to ambient matrices. -/
def carrier (β : ℝ) (M : selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ :=
  carrierPower β (M : Matrix n n ℂ)

abbrev first (β : ℝ) (M U : selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ :=
  fderiv ℝ (carrier β) M U

abbrev second (β : ℝ) (M U V : selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ :=
  fderiv ℝ (fderiv ℝ (carrier β)) M U V

/-- Smoothness of the full carrier for every exponent strictly between zero and one. -/
theorem smooth {β : ℝ} (hβ : β ∈ Ioo 0 1)
    (M : selfAdjoint (Matrix n n ℂ)) (hM : (M : Matrix n n ℂ).PosDef) :
    ContDiffAt ℝ ∞ (carrier β) M := by
  rcases isEmpty_or_nonempty n with he | hn
  · letI := he
    have heq : carrier (n := n) β = fun _ => 0 := by funext X; exact Subsingleton.elim _ _
    rw [heq]
    exact contDiffAt_const
  · letI := hn
    have hp : 0 < realTrace (M : Matrix n n ℂ) := (Complex.pos_iff.mp hM.trace_pos).1
    let ht := (realTraceCLM (n := n)).comp (hermitianInclusion (n := n))
    have hp' : ht M ≠ 0 := hp.ne'
    have hs : ContDiffAt ℝ ∞ (fun X => (ht X) ^ β) M :=
      ht.contDiff.contDiffAt.rpow_const_of_ne (p := β) hp'
    exact hs.smul (MatrixPowerDifferential.smooth
      (α := 1 - β) ⟨by linarith [hβ.2], by linarith [hβ.1]⟩ M hM)

/-- The two centering identities used by the carrier metric estimate. -/
theorem centered [Nonempty n] {β : ℝ} (hβ : β ∈ Ioo 0 1)
    (M U : selfAdjoint (Matrix n n ℂ)) (hM : (M : Matrix n n ℂ).PosDef) :
    let p := realTrace (M : Matrix n n ℂ)
    let a := realTrace (U : Matrix n n ℂ) / p
    let V := U - a • M
    first β M U - a • carrier β M = p ^ β • MatrixPowerDifferential.first (1 - β) M V ∧
      second β M U U = p ^ β • MatrixPowerDifferential.second (1 - β) M V V := by
  have hp : 0 < realTrace (M : Matrix n n ℂ) := (Complex.pos_iff.mp hM.trace_pos).1
  apply centered_derivatives β ((realTraceCLM (n := n)).comp (hermitianInclusion (n := n)))
    (MatrixPowerDifferential.power (1 - β)) M U hp
    ((MatrixPowerDifferential.smooth (α := 1 - β) ⟨by linarith [hβ.2], by linarith [hβ.1]⟩ M hM).of_le (WithTop.coe_le_coe.mpr le_top))
  filter_upwards [eventually_posDef_of_posDef M hM] with X hX
  intro t ht
  exact matrix_rpow_smul hX.posSemidef ht.le (by linarith [hβ.2])

/-- Differentiating the actual affine carrier curve realizes its Fréchet derivative. -/
theorem hasDerivAt_curve {β : ℝ} (hβ : β ∈ Ioo 0 1)
    (M U : selfAdjoint (Matrix n n ℂ)) (hM : (M : Matrix n n ℂ).PosDef) :
    HasDerivAt (fun t : ℝ => carrierPower β ((M : Matrix n n ℂ) + t • (U : Matrix n n ℂ)))
      (first β M U) 0 := by
  exact hasDerivAt_line (carrier β) M U ((smooth hβ M hM).differentiableAt (by simp))

/-- The positive trace-factor part is a lower bound for the actual derivative;
there is no differentiability premise. -/
theorem first_lower [Nonempty n] {β : ℝ} (hβ : β ∈ Ioo 0 1)
    (M U : selfAdjoint (Matrix n n ℂ)) (hM : (M : Matrix n n ℂ).PosDef)
    (hU : (U : Matrix n n ℂ).PosSemidef) :
    (β * (realTrace (M : Matrix n n ℂ)) ^ (β - 1) * realTrace (U : Matrix n n ℂ)) •
      CFC.rpow (M : Matrix n n ℂ) (1 - β) ≤ first β M U := by
  have hp : 0 < realTrace (M : Matrix n n ℂ) := (Complex.pos_iff.mp hM.trace_pos).1
  have hpower : HasDerivAt
      (fun t : ℝ => CFC.rpow ((M : Matrix n n ℂ) + t • (U : Matrix n n ℂ)) (1 - β))
      (MatrixPowerDifferential.first (1 - β) M U) 0 := by
    exact hasDerivAt_line (MatrixPowerDifferential.power (1 - β)) M U
      ((MatrixPowerDifferential.smooth (α := 1 - β)
        ⟨by linarith [hβ.2], by linarith [hβ.1]⟩ M hM).differentiableAt (by simp))

  exact carrierPower_derivative_lower hβ.1.le hβ.2.le hp hU hpower (hasDerivAt_curve hβ M U hM)

/-- Euler's degree-one identity for the actual carrier derivative. -/
theorem first_radial {β : ℝ} (hβ : β ∈ Ioo 0 1)
    (M : selfAdjoint (Matrix n n ℂ)) (hM : (M : Matrix n n ℂ).PosDef) :
    first β M M = carrier β M := by
  have h := MatrixPowerDifferential.euler_first (carrier β) 1 M
    ((smooth hβ M hM).differentiableAt (by simp)) (by
      intro t ht
      simpa only [Real.rpow_one] using carrierPower_smul hβ.1 hβ.2 ht.le hM.posSemidef)
  simpa only [one_smul] using h

/-- Pairing the actual derivative against a positive output probe preserves
its explicit trace-factor lower bound. -/
theorem trace_first_lower [Nonempty n] {β : ℝ} (hβ : β ∈ Ioo 0 1)
    (M U : selfAdjoint (Matrix n n ℂ)) (hM : (M : Matrix n n ℂ).PosDef)
    (hU : (U : Matrix n n ℂ).PosSemidef)
    (W : Matrix n n ℂ) (hW : W.PosSemidef) :
    β * (realTrace (W * carrier β M) / realTrace (M : Matrix n n ℂ)) *
        realTrace (U : Matrix n n ℂ) ≤ realTrace (W * first β M U) := by
  have hp : 0 < realTrace (M : Matrix n n ℂ) := (Complex.pos_iff.mp hM.trace_pos).1
  have h := realTrace_mul_mono hW (first_lower hβ M U hM hU)
  simp only [Matrix.mul_smul, realTrace_smul] at h
  have he : β * (realTrace (W * carrier β M) / realTrace (M : Matrix n n ℂ)) *
      realTrace (U : Matrix n n ℂ) =
      β * (realTrace (M : Matrix n n ℂ)) ^ (β - 1) * realTrace (U : Matrix n n ℂ) *
        realTrace (W * CFC.rpow (M : Matrix n n ℂ) (1 - β)) := by
    rw [carrier, carrierPower, Matrix.mul_smul, realTrace_smul, Real.rpow_sub_one hp.ne']
    change β * ((realTrace (M : Matrix n n ℂ) ^ β *
      realTrace (W * CFC.rpow (M : Matrix n n ℂ) (1 - β))) /
        realTrace (M : Matrix n n ℂ)) * realTrace (U : Matrix n n ℂ) =
      β * (realTrace (M : Matrix n n ℂ) ^ β / realTrace (M : Matrix n n ℂ)) *
        realTrace (U : Matrix n n ℂ) * realTrace (W * CFC.rpow (M : Matrix n n ℂ) (1 - β))
    ring
  exact he.symm ▸ h

end HigherRankKS.CarrierMetric
