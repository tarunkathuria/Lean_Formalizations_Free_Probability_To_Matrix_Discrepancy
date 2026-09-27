import MatrixSpencer.KSFullManuscriptHessian
import SeamlessKS.Source

/-!
# Normalizing actual Hessian directions by the smooth source

The smooth-source diagonal satisfies `wᵢ² ≤ 2`, and is strictly positive
on the live face. All identities concern the genuine Hessian of the supplied
smooth function; the geometric theorem must supply its negative curve.
-/

open Matrix Set
open scoped BigOperators Topology
noncomputable section
namespace SeamlessKS.NormalizedHessian

open MatrixSpencer MatrixSpencer.KSNumericalHessian
open MatrixSpencer.KSFullManuscriptHessian (weighted)
open MatrixSpencer.KSRayleighAccuracy

variable {m : ℕ}

def diagonalMap (w : Fin m → ℝ) : Space m →L[ℝ] Space m :=
  Matrix.toEuclideanCLM (𝕜 := ℝ) (Matrix.diagonal w)

theorem diagonalMap_apply (w : Fin m → ℝ) (v : Space m) (i : Fin m) :
    diagonalMap w v i = w i * v i := by
  change (Matrix.diagonal w *ᵥ WithLp.ofLp v) i = _
  simp [Matrix.mulVec_diagonal]

theorem weighted_rayleigh (w : Fin m → ℝ) (A : Matrix (Fin m) (Fin m) ℝ)
    (v : Space m) : realRayleigh (weighted w A) v =
      realRayleigh A (diagonalMap w v) / 2 := by
  simp only [realRayleigh_eq_quadratic, dotProduct, Matrix.mulVec,
    Finset.mul_sum, Finset.sum_div, weighted]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change v i * (w i * A i j * w j / 2 * v j) =
    (diagonalMap w v i * (A i j * diagonalMap w v j)) / 2
  rw [diagonalMap_apply, diagonalMap_apply]
  ring

theorem weighted_hessian_rayleigh (w : Fin m → ℝ) (f : Space m → ℝ)
    (x v : Space m) : realRayleigh (weighted w (hessian f x)) v =
      fderiv ℝ (fderiv ℝ f) x (diagonalMap w v) (diagonalMap w v) / 2 := by
  rw [weighted_rayleigh, hessian_rayleigh]

def inverseDirection (w : Fin m → ℝ) (h : Space m) : Space m :=
  WithLp.toLp 2 (fun i => h i / w i)

theorem diagonalMap_inverse (w : Fin m → ℝ) (hw : ∀ i, w i ≠ 0) (h : Space m) :
    diagonalMap w (inverseDirection w h) = h := by
  ext i
  rw [diagonalMap_apply]
  change w i * (h i / w i) = h i
  field_simp [hw i]

/-- Any actual nonzero negative curve yields negative normalized curvature.
No special relation to a quadratic source is required. -/
theorem leastRayleigh_neg_of_curve (w : Fin m → ℝ) (hw : ∀ i, 0 < w i)
    (f : Space m → ℝ) (x h : Space m) (hf : ContDiffAt ℝ 2 f x)
    (hh : h ≠ 0)
    (hneg : iteratedDeriv 2 (fun t : ℝ => f (x + t • h)) 0 < 0) :
    leastRayleigh (weighted w (hessian f x)) < 0 := by
  let y := inverseDirection w h
  have hrecon : diagonalMap w y = h := diagonalMap_inverse w (fun i => (hw i).ne') h
  have hy : y ≠ 0 := by
    intro hz
    have hh0 : h = 0 := by rw [← hrecon, hz, map_zero]
    exact hh hh0
  have hyn : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hi : 0 < ‖y‖⁻¹ := inv_pos.mpr hyn
  let v : Space m := ‖y‖⁻¹ • y
  have hv : ‖v‖ = 1 := by
    rw [show v = ‖y‖⁻¹ • y from rfl, norm_smul, Real.norm_eq_abs,
      abs_of_pos hi, inv_mul_cancel₀ hyn.ne']
  rw [KSFourthDifference.line_second f x h hf] at hneg
  have hq : realRayleigh (weighted w (hessian f x)) v < 0 := by
    rw [weighted_hessian_rayleigh]
    change fderiv ℝ (fderiv ℝ f) x (diagonalMap w (‖y‖⁻¹ • y))
      (diagonalMap w (‖y‖⁻¹ • y)) / 2 < 0
    rw [map_smul, hrecon]
    simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    exact div_neg_of_neg_of_pos
      (mul_neg_of_pos_of_neg hi (mul_neg_of_pos_of_neg hi hneg)) (by norm_num)
  exact (leastRayleigh_le _ v hv).trans_lt hq

/-- The larger smooth-source weights do not amplify the unweighted entry
error after the required factor of one half. -/
theorem weighted_entry_error (w : Fin m → ℝ) (hw : ∀ i, w i ^ 2 ≤ 2)
    {A B : Matrix (Fin m) (Fin m) ℝ} {e : ℝ} (he : 0 ≤ e)
    (hab : ∀ i j, |A i j - B i j| ≤ e) :
    ∀ i j, |weighted w A i j - weighted w B i j| ≤ e := by
  intro i j
  have hp : |w i| * |w j| ≤ 2 := by
    nlinarith [sq_abs (w i), sq_abs (w j), sq_nonneg (|w i| - |w j|), hw i, hw j]
  have hid : weighted w A i j - weighted w B i j =
      w i * (A i j - B i j) * w j / 2 := by unfold weighted; ring
  rw [hid, abs_div, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hh := mul_le_mul (hab i j) hp (mul_nonneg (abs_nonneg _) (abs_nonneg _)) he
  nlinarith

def sourceWeight (ζ : ℝ) (x : Fin m → ℝ) (i : Fin m) : ℝ :=
  Real.sqrt (Source.weight 64 ζ (x i) / 64)

theorem sourceWeight_pos (ζ : ℝ) (x : Fin m → ℝ)
    (hx : ∀ i, |x i| < 1) (i : Fin m) : 0 < sourceWeight ζ x i :=
  Real.sqrt_pos.mpr (div_pos (Source.weight_pos (by norm_num) (hx i)) (by norm_num))

theorem sourceWeight_sq_le_two {ζ : ℝ} (hζ : 0 ≤ ζ) (x : Fin m → ℝ)
    (hx : ∀ i, |x i| ≤ 1) (i : Fin m) : sourceWeight ζ x i ^ 2 ≤ 2 := by
  rw [sourceWeight, Real.sq_sqrt (div_nonneg (Source.weight_nonneg (by norm_num) (hx i))
    (by norm_num))]
  have hu := Source.weight_upper (by norm_num : (0 : ℝ) ≤ 64) hζ (x i)
  linarith

end SeamlessKS.NormalizedHessian
