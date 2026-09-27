import MatrixSpencer.KSActualEnvelope
import MatrixSpencer.KSFourthDifference

/-! Real polarization of the actual second and third derivatives. -/
noncomputable section
open Filter Set
open scoped Topology ContDiff
namespace AugmentedHigherRankKS.JointPolarization
set_option maxHeartbeats 800000
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
local instance : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

theorem second_polarization (A : E →L[ℝ] E →L[ℝ] ℝ)
    (hs : ∀ u v, A u v = A v u) (u v : E) :
    4 * A u v = A (u+v) (u+v) - A (u-v) (u-v) := by
  simp only [map_add, map_sub, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply]
  rw [hs v u]
  ring

theorem third_polarization (A : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (hs₁ : ∀ u v w, A u v w = A v u w)
    (hs₂ : ∀ u v w, A u v w = A u w v) (u v w : E) :
    24 * A u v w =
      A (u+v+w) (u+v+w) (u+v+w) - A (u+v-w) (u+v-w) (u+v-w) -
      A (u-v+w) (u-v+w) (u-v+w) + A (u-v-w) (u-v-w) (u-v-w) := by
  simp only [map_add, map_sub, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply]
  have h1 := hs₁ v u w
  have h2 := hs₁ w u v
  have h3 := hs₁ w v u
  have h4 := hs₂ u w v
  have h5 := hs₂ v w u
  linarith

theorem second_norm_le (A : E →L[ℝ] E →L[ℝ] ℝ) {C : ℝ}
    (hC : 0 ≤ C) (hs : ∀ u v, A u v = A v u)
    (hd : ∀ v, |A v v| ≤ C * ‖v‖ ^ 2) : ‖A‖ ≤ 2*C := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro u hu
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro v hv
  have hp : ‖u+v‖ ≤ 2 := by simpa only [hu,hv, one_add_one_eq_two] using norm_add_le u v
  have hm : ‖u-v‖ ≤ 2 := by simpa only [hu,hv, one_add_one_eq_two] using norm_sub_le u v
  have hp' : |A (u+v) (u+v)| ≤ 4*C :=
    (hd _).trans (by calc
      _ ≤ C * (2:ℝ)^2 := by gcongr
      _ = _ := by ring)
  have hm' : |A (u-v) (u-v)| ≤ 4*C :=
    (hd _).trans (by calc
      _ ≤ C * (2:ℝ)^2 := by gcongr
      _ = _ := by ring)
  have he := second_polarization A hs u v
  rw [Real.norm_eq_abs]
  obtain ⟨hpl,hpu⟩ := abs_le.mp hp'
  obtain ⟨hml,hmu⟩ := abs_le.mp hm'
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem third_norm_le (A : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) {C : ℝ}
    (hC : 0 ≤ C)
    (hs₁ : ∀ u v w, A u v w = A v u w)
    (hs₂ : ∀ u v w, A u v w = A u w v)
    (hd : ∀ v, |A v v v| ≤ C * ‖v‖ ^ 3) : ‖A‖ ≤ 9/2*C := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro u hu
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro v hv
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro w hw
  have hav : ‖u+v‖ ≤ 2 := by simpa only [hu,hv, one_add_one_eq_two] using norm_add_le u v
  have hsv : ‖u-v‖ ≤ 2 := by simpa only [hu,hv, one_add_one_eq_two] using norm_sub_le u v
  have hpp : ‖u+v+w‖ ≤ 3 := (norm_add_le _ _).trans (by linarith)
  have hpm : ‖u+v-w‖ ≤ 3 := (norm_sub_le _ _).trans (by linarith)
  have hmp : ‖u-v+w‖ ≤ 3 := (norm_add_le _ _).trans (by linarith)
  have hmm : ‖u-v-w‖ ≤ 3 := (norm_sub_le _ _).trans (by linarith)
  have hb (z : E) (hz : ‖z‖ ≤ 3) : |A z z z| ≤ 27*C := by
    calc _ ≤ C * ‖z‖^3 := hd z
         _ ≤ C * (3:ℝ)^3 := by gcongr
         _ = _ := by ring
  have he := third_polarization A hs₁ hs₂ u v w
  obtain ⟨h1,h2⟩ := abs_le.mp (hb _ hpp)
  obtain ⟨h3,h4⟩ := abs_le.mp (hb _ hpm)
  obtain ⟨h5,h6⟩ := abs_le.mp (hb _ hmp)
  obtain ⟨h7,h8⟩ := abs_le.mp (hb _ hmm)
  rw [Real.norm_eq_abs]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem line_second_at (f : E → ℝ) (x v : E) (t : ℝ)
    (hf : ContDiffAt ℝ 2 f (x+t • v)) :
    iteratedDeriv 2 (fun s : ℝ => f (x+s • v)) t =
      fderiv ℝ (fderiv ℝ f) (x+t • v) v v := by
  have hd (s : ℝ) : deriv (fun u : ℝ => x+u • v) s = v := by
    simpa using (((hasDerivAt_id s).smul_const v).const_add x).deriv
  have hd₂ : iteratedDeriv 2 (fun u : ℝ => x+u • v) t = 0 := by
    rw [show 2 = 1+1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    rw [show deriv (fun u : ℝ => x+u • v) = fun _ => v from funext hd]
    simp
  have hG : ContDiffAt ℝ 2 (fun u : ℝ => x+u • v) t := by fun_prop
  have hh := iteratedDeriv_vcomp_two hf hG
  simpa only [Function.comp_def, hd t, hd₂, iteratedFDeriv_two_apply,
    map_zero, add_zero] using hh

theorem line_third (f : E → ℝ) (x v : E) (hf : ContDiffAt ℝ 3 f x) :
    iteratedDeriv 3 (fun t : ℝ => f (x+t • v)) 0 =
      fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x v v v := by
  have ht : Tendsto (fun t : ℝ => x+t • v) (𝓝 0) (𝓝 x) := by
    simpa using (show ContinuousAt (fun t : ℝ => x+t • v) 0 by fun_prop).tendsto
  have he : iteratedDeriv 2 (fun t : ℝ => f (x+t • v)) =ᶠ[𝓝 0]
      (fun t : ℝ => fderiv ℝ (fderiv ℝ f) (x+t • v) v v) := by
    filter_upwards [ht.eventually (hf.eventually (by norm_num))] with t hft
    exact line_second_at f x v t (hft.of_le (by norm_num))
  have hff := ((hf.fderiv_right (by norm_num : (2 : WithTop ℕ∞)+1 ≤ 3)).fderiv_right
    (by norm_num : (1 : WithTop ℕ∞)+1 ≤ 2)).differentiableAt le_rfl
  have hg : HasDerivAt (fun t : ℝ => x+t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hff' : HasFDerivAt (fderiv ℝ (fderiv ℝ f))
      (fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x) (x+(0:ℝ) • v) := by
    simpa only [zero_smul,add_zero] using hff.hasFDerivAt
  have hh := ((hff'.comp_hasDerivAt 0 hg).clm_apply
    (hasDerivAt_const 0 v)).clm_apply (hasDerivAt_const 0 v)
  rw [show 3 = 2+1 from rfl, iteratedDeriv_succ]
  rw [he.deriv_eq]
  simpa only [zero_smul, add_zero, map_zero, zero_add,
    ContinuousLinearMap.add_apply] using hh.deriv

theorem third_swap_first (f : E → ℝ) (x : E) (hf : ContDiffAt ℝ 3 f x)
    (u v w : E) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x u v w =
    fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x v u w := by
  have hs := (hf.fderiv_right (by norm_num : (2 : WithTop ℕ∞)+1 ≤ 3)).isSymmSndFDerivAt
    (by norm_num)
  exact congrArg (fun L : E →L[ℝ] ℝ => L w) (hs.eq u v)

theorem third_swap_last (f : E → ℝ) (x : E) (hf : ContDiffAt ℝ 3 f x)
    (u v w : E) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x u v w =
    fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x u w v := by
  have he : (fun y => fderiv ℝ (fderiv ℝ f) y v w) =ᶠ[𝓝 x]
      (fun y => fderiv ℝ (fderiv ℝ f) y w v) := by
    filter_upwards [hf.eventually (by norm_num)] with y hy
    exact (hy.isSymmSndFDerivAt (by norm_num)).eq v w
  have hff := ((hf.fderiv_right (by norm_num : (2 : WithTop ℕ∞)+1 ≤ 3)).fderiv_right
    (by norm_num : (1 : WithTop ℕ∞)+1 ≤ 2)).differentiableAt le_rfl
  have hvw := (hff.hasFDerivAt.clm_apply (hasFDerivAt_const v x)).clm_apply
    (hasFDerivAt_const w x)
  have hwv := (hff.hasFDerivAt.clm_apply (hasFDerivAt_const w x)).clm_apply
    (hasFDerivAt_const v x)
  have hh := (hvw.congr_of_eventuallyEq he.symm).unique hwv
  have := congrArg (fun L : E →L[ℝ] ℝ => L u) hh
  simpa using this

theorem second_derivative_norm (f : E → ℝ) (x : E) (hf : ContDiffAt ℝ 2 f x)
    {C : ℝ} (hC : 0 ≤ C)
    (hline : ∀ v, |iteratedDeriv 2 (fun t : ℝ => f (x+t • v)) 0| ≤ C*‖v‖^2) :
    ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ 2*C := by
  apply second_norm_le _ hC (fun u v => (hf.isSymmSndFDerivAt (by norm_num)).eq u v)
  intro v
  simpa only [MatrixSpencer.KSFourthDifference.line_second f x v hf] using hline v

theorem third_derivative_norm (f : E → ℝ) (x : E) (hf : ContDiffAt ℝ 3 f x)
    {C : ℝ} (hC : 0 ≤ C)
    (hline : ∀ v, |iteratedDeriv 3 (fun t : ℝ => f (x+t • v)) 0| ≤ C*‖v‖^3) :
    ‖fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x‖ ≤ 9/2*C := by
  apply third_norm_le _ hC (third_swap_first f x hf) (third_swap_last f x hf)
  intro v
  simpa only [line_third f x v hf] using hline v

end AugmentedHigherRankKS.JointPolarization
