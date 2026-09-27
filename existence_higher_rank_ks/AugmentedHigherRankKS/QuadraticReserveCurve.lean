import AugmentedHigherRankKS.FourBlockSourceDerivatives

/-! The actual reserve curve and its first two derivatives. -/

open scoped ContDiff
noncomputable section
namespace AugmentedHigherRankKS.QuadraticReserveCurve

variable {ι : Type*}

def curve (c : ι → ℝ) (a : ℝ) (h : ι → ℝ) (t : ℝ) : ι → ℝ :=
  fun i => c i - a * t ^ 2 * (h i) ^ 2

@[simp] theorem curve_zero (c : ι → ℝ) (a : ℝ) (h : ι → ℝ) : curve c a h 0 = c := by
  funext i
  simp [curve]

theorem scalar_contDiff (c : ι → ℝ) (a : ℝ) (h : ι → ℝ) (i : ι) :
    ContDiff ℝ ∞ (fun t => curve c a h t i) := by
  unfold curve
  fun_prop

theorem contDiff [Fintype ι] (c : ι → ℝ) (a : ℝ) (h : ι → ℝ) :
    ContDiff ℝ ∞ (curve c a h) :=
  contDiff_pi.mpr (scalar_contDiff c a h)

theorem scalar_deriv (c : ι → ℝ) (a : ℝ) (h : ι → ℝ) (i : ι) (t : ℝ) :
    deriv (fun s => curve c a h s i) t = -2 * a * t * (h i) ^ 2 := by
  have hd := ((hasDerivAt_const t (c i)).sub
    (((hasDerivAt_id t).pow 2).const_mul a |>.mul_const ((h i)^2))).deriv
  convert hd using 1 <;> simp only [curve, Nat.cast_ofNat, pow_one, mul_one, zero_sub, id_eq] <;> ring

@[simp] theorem scalar_deriv_zero (c : ι → ℝ) (a : ℝ) (h : ι → ℝ) (i : ι) :
    deriv (fun s => curve c a h s i) 0 = 0 := by
  rw [scalar_deriv]
  ring

theorem scalar_second (c : ι → ℝ) (a : ℝ) (h : ι → ℝ) (i : ι) :
    iteratedDeriv 2 (fun s => curve c a h s i) 0 = -2 * a * (h i) ^ 2 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  have he : deriv (fun s => curve c a h s i) = fun t => -2 * a * t * (h i) ^ 2 :=
    funext (scalar_deriv c a h i)
  rw [he]
  simpa only [mul_one] using
    (((hasDerivAt_id (0 : ℝ)).const_mul (-2 * a)).mul_const ((h i)^2)).deriv

section Affine
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem affine_contDiff (H D : E) : ContDiff ℝ ∞ (fun t : ℝ => H + t • D) := by
  fun_prop

theorem affine_deriv (H D : E) (t : ℝ) :
    deriv (fun s : ℝ => H + s • D) t = D := by
  simpa using ((hasDerivAt_const t H).add ((hasDerivAt_id t).smul_const D)).deriv

theorem affine_second (H D : E) :
    iteratedDeriv 2 (fun s : ℝ => H + s • D) 0 = 0 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one,
    show deriv (fun s : ℝ => H + s • D) = fun _ => D from funext (affine_deriv H D)]
  simp

end Affine
end AugmentedHigherRankKS.QuadraticReserveCurve
