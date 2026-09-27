import AugmentedHigherRankKS.FourBlockQueryRegularity
import AugmentedHigherRankKS.RuntimeQueryFloors

/-! Concrete uniform derivatives of actual optimized reserve queries. All
optimizer, density-floor, and source-fidelity inputs are derived here from the
matrix assumptions and the explicit query domain. -/
noncomputable section
open Matrix MatrixSpencer HigherRankKS Filter
open scoped BigOperators Topology ContDiff MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace AugmentedHigherRankKS
open RuntimeParameters
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 300000
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n] [Nonempty n]
local instance runtimeDerivativeCStar {j : Type*} [Fintype j] [DecidableEq j] :
  CStarAlgebra (Matrix j j ℂ) := {}

theorem runtime_sqrt_m_ge_one (z : Dimensions) (hz : z ∈ Domain) :
    1 ≤ Real.sqrt (m z) := by
  have hd := hz.2.1
  have hm : (1:ℝ)^2 ≤ m z := by dsimp [m]; linarith
  exact (Real.le_sqrt (by norm_num) (by dsimp [m]; positivity)).mpr hm

theorem runtime_sqrt_card_le (z : Dimensions) (hd : (Fintype.card n : ℝ) ≤ z.D) :
    Real.sqrt (Fintype.card (FourSpin n) : ℝ) ≤ Real.sqrt (m z) := by
  apply Real.sqrt_le_sqrt
  have hc : (Fintype.card (FourSpin n) : ℝ) = 4*(Fintype.card n : ℝ) := by
    simp only [FourSpin,Fintype.card_sum,Nat.cast_add]
    ring
  rw [hc]
  dsimp [m]
  linarith

/-- Actual optimized derivatives for a quadratic query at any base point
inside the explicit query domain; no optimizer is supplied by the caller. -/
theorem runtime_quadratic_derivative_bounds
    (z : Dimensions) (hz : z ∈ Domain) (hd : (Fintype.card n : ℝ) ≤ z.D)
    (H K : Matrix (FourSpin n) (FourSpin n) ℂ) (hH : H.IsHermitian)
    (hH8 : ‖H‖ ≤ 8) (hK : ‖K‖ ≤ 2)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef) (hsum : ∑ i, A i ≤ 1)
    {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hN : ∀ i, ‖A i‖ ≤ ε)
    {r : ℕ} (hr : ∀ i, (A i).rank ≤ r) (k : ℕ) (hk : 1 ≤ k)
    (hrβ : (r:ℝ)^((1:ℝ)/2^k) ≤ 2)
    (c u g : ι → ℝ) (hu : ∀ i, |u i| ≤ 1) (hg : ∀ i, |g i| ≤ 1)
    (hc : ∀ i, zeta z ≤ c i-a z*(u i)^2)
    (hccap : ∀ i, c i-a z*(u i)^2 ≤ 8*a z) :
    |iteratedDeriv 2 (fun t => potential (H+t•K) A ((1:ℝ)/2^k)
      (quadraticReserve c u g (a z) t) (theta z)) 0| ≤ M z ∧
    |iteratedDeriv 3 (fun t => potential (H+t•K) A ((1:ℝ)/2^k)
      (quadraticReserve c u g (a z) t) (theta z)) 0| ≤ M z := by
  have hpos : ∀ i, 0 < c i-a z*(u i)^2 := fun i =>
    lt_of_lt_of_le (theta_poly.positive z hz) (hc i)
  obtain ⟨S,hS,ht,hmax,hfloor,hbudget⟩ := exists_runtime_query_optimizer z hz hd H hH hH8
    A hA hsum hε hε1 hN hr k hk hrβ _ hpos hccap
  have hc0 : quadraticReserve c u g (a z) 0 = fun i => c i-a z*(u i)^2 := by
    funext i
    simp [quadraticReserve]
  have hh := query_potential_derivative_bounds A hA k hk H K
    (quadraticReserve c u g (a z)) (contDiff_quadraticReserve c u g (a z)).contDiffAt
    (by simpa only [hc0] using hpos) S hS ⟨hS.posSemidef,ht⟩
    (theta_poly.positive z hz) (s0_poly.positive z hz)
    (div_nonneg (mul_nonneg (by norm_num) (a_poly.positive z hz).le) (theta_poly.positive z hz).le)
    (runtime_sqrt_m_ge_one z hz) (runtime_sqrt_card_le z hd)
    (show 0 ≤ C0 z by unfold C0; positivity) hK hfloor
    (by simpa only [hc0] using hbudget) (by simpa only [hc0] using hmax)
    (quadraticReserve_scaled_jets c u g (by linarith [a_ge z hz])
      (theta_poly.positive z hz) (theta_le_one z hz) hc hu hg)
  simpa only [M,B2,B3,A0,H0,L0,jointAmplitude,jointScale] using hh

/-- Affine preparation has the same proved second- and third-derivative
budget as the centered quadratic queries. -/
theorem runtime_affine_derivative_bounds
    (z : Dimensions) (hz : z ∈ Domain) (hd : (Fintype.card n : ℝ) ≤ z.D)
    (H K : Matrix (FourSpin n) (FourSpin n) ℂ) (hH : H.IsHermitian)
    (hH8 : ‖H‖ ≤ 8) (hK : ‖K‖ ≤ 2)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef) (hsum : ∑ i, A i ≤ 1)
    {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hN : ∀ i, ‖A i‖ ≤ ε)
    {r : ℕ} (hr : ∀ i, (A i).rank ≤ r) (k : ℕ) (hk : 1 ≤ k)
    (hrβ : (r:ℝ)^((1:ℝ)/2^k) ≤ 2)
    (c w : ι → ℝ) (hw : ∀ i, |w i| ≤ 1)
    (hc : ∀ i, zeta z ≤ c i) (hccap : ∀ i, c i ≤ 8*a z) :
    |iteratedDeriv 2 (fun t => potential (H+t•K) A ((1:ℝ)/2^k)
      (affineReserve c w t) (theta z)) 0| ≤ M z ∧
    |iteratedDeriv 3 (fun t => potential (H+t•K) A ((1:ℝ)/2^k)
      (affineReserve c w t) (theta z)) 0| ≤ M z := by
  have hpos : ∀ i, 0 < c i := fun i => lt_of_lt_of_le (theta_poly.positive z hz) (hc i)
  obtain ⟨S,hS,ht,hmax,hfloor,hbudget⟩ := exists_runtime_query_optimizer z hz hd H hH hH8
    A hA hsum hε hε1 hN hr k hk hrβ c hpos hccap
  have hc0 : affineReserve c w 0 = c := by funext i; simp [affineReserve]
  have hh := query_potential_derivative_bounds A hA k hk H K
    (affineReserve c w) (contDiff_affineReserve c w).contDiffAt
    (by simpa only [hc0] using hpos) S hS ⟨hS.posSemidef,ht⟩
    (theta_poly.positive z hz) (s0_poly.positive z hz)
    (div_nonneg (mul_nonneg (by norm_num) (a_poly.positive z hz).le) (theta_poly.positive z hz).le)
    (runtime_sqrt_m_ge_one z hz) (runtime_sqrt_card_le z hd)
    (show 0 ≤ C0 z by unfold C0; positivity) hK hfloor
    (by simpa only [hc0] using hbudget) (by simpa only [hc0] using hmax)
    (affineReserve_scaled_jets c w (by linarith [a_ge z hz])
      (theta_poly.positive z hz) hc hw)
  simpa only [M,B2,B3,A0,H0,L0,jointAmplitude,jointScale] using hh

end AugmentedHigherRankKS
