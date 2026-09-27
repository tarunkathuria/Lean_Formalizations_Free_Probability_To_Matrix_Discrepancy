import HigherRankKSRuntime.RuntimeStateBounds
import HigherRankKSRuntime.NumericHessian
import AugmentedHigherRankKS.RuntimePotentialDerivatives

/-! Derivative bounds on the actual finite-difference and walk query lines.
The uniform constant is the explicit runtime recipe, derived from the input. -/
noncomputable section
open Matrix MatrixSpencer Set Filter
open scoped BigOperators Topology ContDiff MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace HigherRankKSRuntime.RuntimeLineBounds
open AugmentedHigherRankKS RuntimeParameters
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 300000
variable {m : ℕ} {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
local instance lineCStar {j : Type*} [Fintype j] [DecidableEq j] :
  CStarAlgebra (Matrix j j ℂ) := {}

theorem coefficientForce_hermitian (A : Fin m → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) (x u : Fin m → ℝ) :
    (Frames.coefficientForce A x u).IsHermitian := by
  change (∑ i, u i • forceAtom (x i) (A i))ᴴ = _
  simp only [Matrix.conjTranspose_sum,Matrix.conjTranspose_smul,star_trivial,
    (forceAtom_isHermitian _ (hA _).isHermitian).eq]
  rfl

theorem chart_smooth_at (H : Matrix (FourSpin n) (FourSpin n) ℂ)
    (A : Fin m → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (k : ℕ) (hk : 1 ≤ k) {θ : ℝ} (hθ : 0 < θ) (a : ℝ)
    (x c : Fin m → ℝ) (u : RuntimeCurvature.Space m) (hc : ∀ i, 0 < c i-a*(u i)^2) :
    ContDiffAt ℝ ∞ (RuntimeCurvature.chart H A ((1:ℝ)/2^k) θ a x c) u := by
  apply contDiffAt_potential_of_positive_weights A hA k hk θ hθ
    (fun u : RuntimeCurvature.Space m => H+Frames.coefficientForce A x u)
    (fun u : RuntimeCurvature.Space m => fun i => c i-a*(u i)^2) u
  · unfold Frames.coefficientForce
    fun_prop
  · apply contDiffAt_pi.mpr
    intro i
    fun_prop
  · exact hc

theorem chart_shift_line (H : Matrix (FourSpin n) (FourSpin n) ℂ)
    (A : Fin m → Matrix n n ℂ) (β θ a : ℝ) (x c : Fin m → ℝ)
    (u g : RuntimeCurvature.Space m) :
    (fun t : ℝ => RuntimeCurvature.chart H A β θ a x c (u+t•g)) =
      (fun t : ℝ => potential ((H+Frames.coefficientForce A x u)+t•Frames.coefficientForce A x g)
        A β (quadraticReserve c u g a t) θ) := by
  funext t
  unfold RuntimeCurvature.chart
  have he : Frames.coefficientForce A x (u+t•g) =
      Frames.coefficientForce A x u+t•Frames.coefficientForce A x g := by
    unfold Frames.coefficientForce
    rw [Finset.smul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    change (u i+t*g i) • forceAtom (x i) (A i) = _
    rw [add_smul,MulAction.mul_smul]
  rw [he,←add_assoc]
  rfl

/-- The actual chart has the uniform third-derivative bound at every queried
point and every coefficient direction with coordinates bounded by one. -/
theorem chart_point_third
    (p : Dimensions) (hp : p ∈ Domain) (hd : (Fintype.card n : ℝ) ≤ p.D)
    (H : Matrix (FourSpin n) (FourSpin n) ℂ) (hH : H.IsHermitian) (hH5 : ‖H‖ ≤ 5)
    (A : Fin m → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef) (hsum : ∑ i, A i ≤ 1)
    {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hN : ∀ i, ‖A i‖ ≤ ε)
    {r : ℕ} (hr : ∀ i, (A i).rank ≤ r) (k : ℕ) (hk : 1 ≤ k)
    (hrβ : (r:ℝ)^((1:ℝ)/2^k) ≤ 2)
    (x c : Fin m → ℝ) (hx : ∀ i, |x i| ≤ 1)
    (hc : ∀ i, 2*zeta p ≤ c i) (hcu : ∀ i, c i ≤ 4*a p)
    (u g : RuntimeCurvature.Space m) (hu : ‖u‖ ≤ radius p) (hg : ∀ i, |g i| ≤ 1) :
    |iteratedDeriv 3 (fun t : ℝ => RuntimeCurvature.chart H A ((1:ℝ)/2^k)
      (theta p) (a p) x c (u+t•g)) 0| ≤ M p := by
  obtain ⟨hcenter,hreserve⟩ := runtime_quadratic_query_domain p hp A hA hsum H hH5 x hx c hc hcu u hu
  have huf : ∀ i, |u i| ≤ 1 := by
    intro i
    have hi : |u i| ≤ ‖u‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le u i
    have hb := (hu.trans (min_le_left _ _))
    have hrho := theta_le_one p hp
    change ‖u‖ ≤ rho p/4 at hb
    linarith
  have hforce : ‖Frames.coefficientForce A x g‖ ≤ 2 := by
    simpa only [mul_one] using coefficient_force_norm_le A hA hsum x g hx zero_le_one hg
  have hb := runtime_quadratic_derivative_bounds p hp hd
    (H+Frames.coefficientForce A x u) (Frames.coefficientForce A x g)
    (hH.add (coefficientForce_hermitian A hA x u)) hcenter hforce
    A hA hsum hε hε1 hN hr k hk hrβ c u g huf hg
    (fun i => (hreserve i).1) (fun i => (hreserve i).2)
  rw [chart_shift_line]
  exact hb.2

/-- Smoothness and the third-derivative estimate along a complete scalar
query interval follow from its explicit radius bound. -/
theorem chart_line_bounds
    (p : Dimensions) (hp : p ∈ Domain) (hd : (Fintype.card n : ℝ) ≤ p.D)
    (H : Matrix (FourSpin n) (FourSpin n) ℂ) (hH : H.IsHermitian) (hH5 : ‖H‖ ≤ 5)
    (A : Fin m → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef) (hsum : ∑ i, A i ≤ 1)
    {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hN : ∀ i, ‖A i‖ ≤ ε)
    {r : ℕ} (hr : ∀ i, (A i).rank ≤ r) (k : ℕ) (hk : 1 ≤ k)
    (hrβ : (r:ℝ)^((1:ℝ)/2^k) ≤ 2)
    (x c : Fin m → ℝ) (hx : ∀ i, |x i| ≤ 1)
    (hc : ∀ i, 2*zeta p ≤ c i) (hcu : ∀ i, c i ≤ 4*a p)
    (g : RuntimeCurvature.Space m) (hg : ∀ i, |g i| ≤ 1)
    {t : ℝ} (htradius : t*‖g‖ ≤ radius p) :
    ContDiffOn ℝ 3 (fun s : ℝ => RuntimeCurvature.chart H A ((1:ℝ)/2^k)
      (theta p) (a p) x c (s•g)) (Icc (-t) t) ∧
    ∀ s ∈ Icc (-t) t, |iteratedDeriv 3 (fun w : ℝ => RuntimeCurvature.chart H A ((1:ℝ)/2^k)
      (theta p) (a p) x c (w•g)) s| ≤ M p := by
  have hradius : ∀ s ∈ Icc (-t) t, ‖s•g‖ ≤ radius p := by
    intro s hs
    rw [norm_smul,Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right (abs_le.mpr hs) (norm_nonneg g)).trans htradius
  constructor
  · intro s hs
    obtain ⟨_,hreserve⟩ := runtime_quadratic_query_domain p hp A hA hsum H hH5 x hx c hc hcu (s•g) (hradius s hs)
    have hsm := chart_smooth_at H A hA k hk (theta_poly.positive p hp) (a p) x c (s•g)
      (fun i => lt_of_lt_of_le (theta_poly.positive p hp) (hreserve i).1)
    have hh : ContDiffAt ℝ ∞ (fun w : ℝ => RuntimeCurvature.chart H A ((1:ℝ)/2^k)
        (theta p) (a p) x c (w•g)) s :=
      ContDiffAt.comp (g := RuntimeCurvature.chart H A ((1:ℝ)/2^k) (theta p) (a p) x c)
        (f := fun w : ℝ => w•g) s hsm (contDiffAt_id.smul contDiffAt_const)
    exact (hh.of_le (WithTop.coe_le_coe.mpr (show (3 : ℕ∞) ≤ ⊤ from le_top))).contDiffWithinAt
  · intro s hs
    have hb := chart_point_third p hp hd H hH hH5 A hA hsum hε hε1 hN hr k hk hrβ x c hx hc hcu
      (s•g) g (hradius s hs) hg
    have he : (fun v : ℝ => RuntimeCurvature.chart H A ((1:ℝ)/2^k) (theta p) (a p) x c
        ((v+s)•g)) = (fun v : ℝ => RuntimeCurvature.chart H A ((1:ℝ)/2^k) (theta p) (a p) x c
        (s•g+v•g)) := by funext v; rw [add_smul,add_comm]
    have hdshift := congrFun (iteratedDeriv_comp_add_const 3
      (fun w : ℝ => RuntimeCurvature.chart H A ((1:ℝ)/2^k) (theta p) (a p) x c (w•g)) s) 0
    rw [he] at hdshift
    simpa only [zero_add,hdshift] using hb

end HigherRankKSRuntime.RuntimeLineBounds
