import HigherRankKSRuntime.RuntimeLineBounds

/-! The concrete numerical stencil and unit tangent walk inherit the proved
actual potential bounds on their entire query intervals. -/
noncomputable section
open Matrix MatrixSpencer Set
open scoped BigOperators Topology ContDiff MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace HigherRankKSRuntime.RuntimeHessianBounds
open AugmentedHigherRankKS RuntimeParameters RuntimeLineBounds
open KSNumericalHessian (coordinate)
set_option maxHeartbeats 1200000
variable {m : ℕ} {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

lemma coordinate_norm (i : Fin m) : ‖coordinate i‖ = 1 := by
  simp [coordinate]

lemma coordinate_abs_le (i j : Fin m) : |coordinate i j| ≤ 1 := by
  simp only [coordinate,EuclideanSpace.single_apply]
  split_ifs <;> norm_num

lemma coordinate_add_abs_le (i j : Fin m) (hij : i ≠ j) (l : Fin m) :
    |(coordinate i+coordinate j) l| ≤ 1 := by
  change |coordinate i l+coordinate j l| ≤ 1
  simp only [coordinate,EuclideanSpace.single_apply]
  split_ifs <;> simp_all

lemma coordinate_sub_abs_le (i j : Fin m) (hij : i ≠ j) (l : Fin m) :
    |(coordinate i-coordinate j) l| ≤ 1 := by
  change |coordinate i l-coordinate j l| ≤ 1
  simp only [coordinate,EuclideanSpace.single_apply]
  split_ifs <;> simp_all

/-- No assumed Hessian accuracy or regularity enters the actual stencil bound. -/
theorem chart_numeric_line_bounds
    (p : Dimensions) (hp : p ∈ Domain) (hd : (Fintype.card n : ℝ) ≤ p.D)
    (H : Matrix (FourSpin n) (FourSpin n) ℂ) (hH : H.IsHermitian) (hH5 : ‖H‖ ≤ 5)
    (A : Fin m → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef) (hsum : ∑ i, A i ≤ 1)
    {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hN : ∀ i, ‖A i‖ ≤ ε)
    {r : ℕ} (hr : ∀ i, (A i).rank ≤ r) (k : ℕ) (hk : 1 ≤ k)
    (hrβ : (r:ℝ)^((1:ℝ)/2^k) ≤ 2)
    (x c : Fin m → ℝ) (hx : ∀ i, |x i| ≤ 1)
    (hc : ∀ i, 2*zeta p ≤ c i) (hcu : ∀ i, c i ≤ 4*a p) :
    NumericHessian.LineBounds (RuntimeCurvature.chart H A ((1:ℝ)/2^k)
      (theta p) (a p) x c) 0 (stencil p) (M p) := by
  have hradius := (stencil_query_radius p hp).1
  have ht := (stencil_poly.positive p hp).le
  have hM : M p ≤ 8*M p := by linarith [M_poly.positive p hp]
  constructor
  · intro i
    have hh := chart_line_bounds p hp hd H hH hH5 A hA hsum hε hε1 hN hr k hk hrβ
      x c hx hc hcu (coordinate i) (coordinate_abs_le i)
      (t := stencil p) (by rw [coordinate_norm,mul_one]; linarith)
    simpa only [zero_add] using hh
  · intro i j hij
    have hpn : ‖coordinate i+coordinate j‖ ≤ 2 := by
      simpa only [coordinate_norm,one_add_one_eq_two] using norm_add_le (coordinate i) (coordinate j)
    have hmn : ‖coordinate i-coordinate j‖ ≤ 2 := by
      simpa only [coordinate_norm,one_add_one_eq_two] using norm_sub_le (coordinate i) (coordinate j)
    have hp' := chart_line_bounds p hp hd H hH hH5 A hA hsum hε hε1 hN hr k hk hrβ
      x c hx hc hcu (coordinate i+coordinate j) (coordinate_add_abs_le i j hij)
      (t := stencil p) (by nlinarith [mul_le_mul_of_nonneg_left hpn ht])
    have hm' := chart_line_bounds p hp hd H hH hH5 A hA hsum hε hε1 hN hr k hk hrβ
      x c hx hc hcu (coordinate i-coordinate j) (coordinate_sub_abs_le i j hij)
      (t := stencil p) (by nlinarith [mul_le_mul_of_nonneg_left hmn ht])
    simp only [zero_add]
    exact ⟨hp'.1,hm'.1,fun s hs => (hp'.2 s hs).trans hM,fun s hs => (hm'.2 s hs).trans hM⟩

/-- The actual selected unit tangent direction has the same uniform scalar
third-derivative estimate used to choose the better signed step. -/
theorem chart_walk_line_bounds
    (p : Dimensions) (hp : p ∈ Domain) (hd : (Fintype.card n : ℝ) ≤ p.D)
    (H : Matrix (FourSpin n) (FourSpin n) ℂ) (hH : H.IsHermitian) (hH5 : ‖H‖ ≤ 5)
    (A : Fin m → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef) (hsum : ∑ i, A i ≤ 1)
    {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hN : ∀ i, ‖A i‖ ≤ ε)
    {r : ℕ} (hr : ∀ i, (A i).rank ≤ r) (k : ℕ) (hk : 1 ≤ k)
    (hrβ : (r:ℝ)^((1:ℝ)/2^k) ≤ 2)
    (x c : Fin m → ℝ) (hx : ∀ i, |x i| ≤ 1)
    (hc : ∀ i, 2*zeta p ≤ c i) (hcu : ∀ i, c i ≤ 4*a p)
    (g : RuntimeCurvature.Space m) (hg : ‖g‖ = 1) :
    ContDiffOn ℝ 3 (fun s : ℝ => RuntimeCurvature.chart H A ((1:ℝ)/2^k)
      (theta p) (a p) x c (s•g)) (Icc (-(walk p)) (walk p)) ∧
    ∀ s ∈ Icc (-(walk p)) (walk p), |iteratedDeriv 3 (fun w : ℝ => RuntimeCurvature.chart H A ((1:ℝ)/2^k)
      (theta p) (a p) x c (w•g)) s| ≤ M p := by
  apply chart_line_bounds p hp hd H hH hH5 A hA hsum hε hε1 hN hr k hk hrβ x c hx hc hcu g
  · intro i
    simpa only [Real.norm_eq_abs,hg] using PiLp.norm_apply_le g i
  · rw [hg,mul_one]
    exact (walk_query_radius p hp).1

end HigherRankKSRuntime.RuntimeHessianBounds
