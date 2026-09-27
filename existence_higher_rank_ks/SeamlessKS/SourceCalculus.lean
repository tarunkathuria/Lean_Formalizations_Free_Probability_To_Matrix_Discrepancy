import SeamlessKS.Source

/-! Differentiation of the actual smooth source, without a derivative oracle. -/
noncomputable section
namespace SeamlessKS
namespace Source

lemma hasDerivAt_radialRoot {ζ : ℝ} (hζ : 0 < ζ) (x : ℝ) :
    HasDerivAt (fun t : ℝ => Real.sqrt (t ^ 2 + ζ ^ 2))
      (x / Real.sqrt (x ^ 2 + ζ ^ 2)) x := by
  have harg : HasDerivAt (fun t : ℝ => t ^ 2 + ζ ^ 2) (2 * x) x := by
    convert ((hasDerivAt_id x).pow 2).add_const (ζ ^ 2) using 1 <;> simp
  convert harg.sqrt (ne_of_gt (radicand_pos hζ x)) using 1
  field_simp

/-- The closed expression `slope` is the derivative of the source itself. -/
theorem hasDerivAt_weight {ζ : ℝ} (hζ : 0 < ζ) (u x : ℝ) :
    HasDerivAt (weight u ζ) (slope u ζ x) x := by
  have hpow : HasDerivAt (fun t : ℝ => t ^ 2) (2 * x) x := by
    convert (hasDerivAt_id x).pow 2 using 1 <;> simp
  have h := (((hasDerivAt_const x (1 : ℝ)).sub hpow).add_const
    (Real.sqrt (1 + ζ ^ 2))).sub (hasDerivAt_radialRoot hζ x)
  convert h.const_mul u using 1 <;> simp [weight, slope] <;> ring

@[simp] theorem deriv_weight {ζ : ℝ} (hζ : 0 < ζ) (u x : ℝ) :
    deriv (weight u ζ) x = slope u ζ x := (hasDerivAt_weight hζ u x).deriv

/-- The square root smoothing adds strictly negative curvature to the quadratic. -/
theorem hasDerivAt_slope {ζ : ℝ} (hζ : 0 < ζ) (u x : ℝ) :
    HasDerivAt (slope u ζ) (curvature u ζ x) x := by
  have ht : 0 < Real.sqrt (x ^ 2 + ζ ^ 2) := Real.sqrt_pos.mpr (radicand_pos hζ x)
  have ht2 := Real.sq_sqrt (radicand_pos hζ x).le
  have hquot := (hasDerivAt_id x).div (hasDerivAt_radialRoot hζ x) ht.ne'
  have h := (((hasDerivAt_id x).const_mul 2).add hquot).const_mul (-u)
  convert h using 1
  unfold curvature
  dsimp
  field_simp
  rw [ht2]
  ring

@[simp] theorem deriv_slope {ζ : ℝ} (hζ : 0 < ζ) (u x : ℝ) :
    deriv (slope u ζ) x = curvature u ζ x := (hasDerivAt_slope hζ u x).deriv

theorem second_deriv_weight {ζ : ℝ} (hζ : 0 < ζ) (u x : ℝ) :
    deriv (deriv (weight u ζ)) x = curvature u ζ x := by
  have hfun : deriv (weight u ζ) = slope u ζ := funext (deriv_weight hζ u)
  rw [hfun, deriv_slope hζ]

theorem curvature_upper {u ζ : ℝ} (hu : 0 ≤ u) (x : ℝ) :
    curvature u ζ x ≤ -2 * u := by
  unfold curvature
  have : 0 ≤ u * ζ ^ 2 / Real.sqrt (x ^ 2 + ζ ^ 2) ^ 3 := by positivity
  linarith

theorem second_deriv_weight_upper {u ζ : ℝ} (hu : 0 ≤ u) (hζ : 0 < ζ) (x : ℝ) :
    deriv (deriv (weight u ζ)) x ≤ -2 * u := by
  rw [second_deriv_weight hζ]
  exact curvature_upper hu x

end Source
end SeamlessKS
