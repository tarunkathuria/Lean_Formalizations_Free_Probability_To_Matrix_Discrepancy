import HigherRankKSRuntime.RuntimeStateBounds
import AugmentedHigherRankKS.RuntimePotentialDerivatives

/-! The preparation finite-difference bound for the actual potential,
including the full queried interval. -/
noncomputable section
open Matrix MatrixSpencer Set
open scoped BigOperators Topology ContDiff MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace HigherRankKSRuntime.RuntimePreparationBounds
open AugmentedHigherRankKS RuntimeParameters
variable {m : ℕ} {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
local instance prepCStar {j : Type*} [Fintype j] [DecidableEq j] :
  CStarAlgebra (Matrix j j ℂ) := {}

theorem prep_shift (H : Matrix (FourSpin n) (FourSpin n) ℂ)
    (A : Fin m → Matrix n n ℂ) (β θ a : ℝ) (c : Fin m → ℝ) (i : Fin m) (t : ℝ) :
    (fun s => RuntimeCurvature.prepCurve H A β θ a c i (t+s)) =
      (fun s => potential ((H+t • ((1/a) • augmentedCenter 0 (A i)))+
        s • ((1/a) • augmentedCenter 0 (A i))) A β
        (affineReserve (fun j => c j-if j=i then t else 0)
          (fun j => if j=i then -1 else 0) s) θ) := by
  funext s
  unfold RuntimeCurvature.prepCurve
  rw [add_smul,←add_assoc]
  congr 1
  funext j
  unfold affineReserve
  by_cases hj : j=i <;> simp only [hj,ite_true,ite_false] <;> ring

theorem prep_smooth_at (H : Matrix (FourSpin n) (FourSpin n) ℂ)
    (A : Fin m → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (k : ℕ) (hk : 1 ≤ k) {θ : ℝ} (hθ : 0 < θ) (a : ℝ)
    (c : Fin m → ℝ) (i : Fin m) (t : ℝ)
    (hc : ∀ j, 0 < c j-(if j=i then t else 0)) :
    ContDiffAt ℝ ∞ (RuntimeCurvature.prepCurve H A ((1:ℝ)/2^k) θ a c i) t := by
  apply contDiffAt_potential_of_positive_weights A hA k hk θ hθ
    (fun t : ℝ => H+t • ((1/a) • augmentedCenter 0 (A i)))
    (fun t : ℝ => fun j => c j-if j=i then t else 0) t
  · fun_prop
  · apply contDiffAt_pi.mpr
    intro j
    by_cases hj : j=i <;> simp only [hj,ite_true,ite_false] <;> fun_prop
  · exact hc

theorem prep_differentiable_zero (H : Matrix (FourSpin n) (FourSpin n) ℂ)
    (A : Fin m → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (k : ℕ) (hk : 1 ≤ k) {θ : ℝ} (hθ : 0 < θ) (a : ℝ)
    (c : Fin m → ℝ) (hc : ∀ j, 0 < c j) (i : Fin m) :
    DifferentiableAt ℝ (RuntimeCurvature.prepCurve H A ((1:ℝ)/2^k) θ a c i) 0 :=
  (prep_smooth_at H A hA k hk hθ a c i 0 (by simpa using hc)).differentiableAt (by simp)

theorem prep_force_bounds (p : Dimensions) (hp : p ∈ Domain)
    (A : Matrix n n ℂ) (hA : A.PosSemidef) (hN : ‖A‖ ≤ 1) :
    ((1/a p) • augmentedCenter 0 A).IsHermitian ∧
    ‖(1/a p) • augmentedCenter 0 A‖ ≤ 2 := by
  have ha : 0 < a p := a_poly.positive p hp
  have hB := augmentedCenter_isHermitian (show (0 : Matrix n n ℂ).IsHermitian by simp) hA.isHermitian
  constructor
  · change ((1/a p) • augmentedCenter 0 A)ᴴ = _
    simp only [Matrix.conjTranspose_smul,star_trivial,hB.eq]
  · rw [norm_smul,Real.norm_eq_abs,abs_of_pos (one_div_pos.mpr ha)]
    have hb : ‖augmentedCenter 0 A‖ ≤ 1 := augmentedCenter_norm_le (by simp) hA.isHermitian (by simp) hN
    have had : 1/a p ≤ 1 := (div_le_one ha).mpr (by linarith [a_ge p hp])
    have hh := mul_le_mul had hb (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
    simpa only [one_div] using hh.trans (by norm_num : (1:ℝ)*1 ≤ 2)

/-- All analytic assumptions in the scalar preparation secant estimate are
consequences of ordinary input bounds and the clean reserve margin. -/
theorem prep_line_bounds
    (p : Dimensions) (hp : p ∈ Domain) (hd : (Fintype.card n : ℝ) ≤ p.D)
    (H : Matrix (FourSpin n) (FourSpin n) ℂ) (hH : H.IsHermitian) (hH5 : ‖H‖ ≤ 5)
    (A : Fin m → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef) (hsum : ∑ i, A i ≤ 1)
    {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hN : ∀ i, ‖A i‖ ≤ ε)
    {r : ℕ} (hr : ∀ i, (A i).rank ≤ r) (k : ℕ) (hk : 1 ≤ k)
    (hrβ : (r:ℝ)^((1:ℝ)/2^k) ≤ 2)
    (c : Fin m → ℝ) (hc : ∀ i, 2*zeta p ≤ c i) (hcu : ∀ i, c i ≤ 4*a p) (i : Fin m) :
    ContDiffOn ℝ 2 (RuntimeCurvature.prepCurve H A ((1:ℝ)/2^k) (theta p) (a p) c i) (Icc 0 (prep p)) ∧
    ∀ t ∈ Icc 0 (prep p), |iteratedDeriv 2
      (RuntimeCurvature.prepCurve H A ((1:ℝ)/2^k) (theta p) (a p) c i) t| ≤ M p := by
  have hforce := prep_force_bounds p hp (A i) (hA i) ((hN i).trans hε1)
  have hquery (t : ℝ) (ht : t ∈ Icc 0 (prep p)) :
      ‖H+t • ((1/a p) • augmentedCenter 0 (A i))‖ ≤ 8 ∧
      (∀ j, zeta p ≤ c j-if j=i then t else 0) ∧
      (∀ j, c j-(if j=i then t else 0) ≤ 8*a p) := by
    have hb := runtime_preparation_query_domain p hp A hA (fun j => (hN j).trans hε1)
      H hH5 c hc hcu i ht.1 ht.2
    have he : t • ((1/a p) • augmentedCenter 0 (A i)) = augmentedCenter 0 ((t/a p) • A i) := by
      rw [smul_smul,show t*(1/a p)=t/a p by ring,←augmentedCenter_smul]
      simp
    rw [he]
    exact ⟨hb.1,fun j => by simpa only [Pi.single_apply] using (hb.2 j).1,
      fun j => by simpa only [Pi.single_apply] using (hb.2 j).2⟩
  have hsmooth (t : ℝ) (ht : t ∈ Icc 0 (prep p)) :
      ContDiffAt ℝ ∞ (RuntimeCurvature.prepCurve H A ((1:ℝ)/2^k) (theta p) (a p) c i) t := by
    apply contDiffAt_potential_of_positive_weights A hA k hk (theta p) (theta_poly.positive p hp)
      (fun t : ℝ => H+t • ((1/a p) • augmentedCenter 0 (A i)))
      (fun t : ℝ => fun j => c j-if j=i then t else 0) t
    · fun_prop
    · apply contDiffAt_pi.mpr
      intro j
      by_cases hj : j=i <;> simp only [hj,ite_true,ite_false] <;> fun_prop
    · intro j
      exact (theta_poly.positive p hp).trans_le ((hquery t ht).2.1 j)
  constructor
  · intro t ht
    exact ((hsmooth t ht).of_le
      (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))).contDiffWithinAt
  · intro t ht
    have hHt : (H+t • ((1/a p) • augmentedCenter 0 (A i))).IsHermitian := by
      apply hH.add
      change (t • ((1/a p) • augmentedCenter 0 (A i)))ᴴ = _
      simp only [Matrix.conjTranspose_smul,star_trivial,hforce.1.eq]
    have hb := runtime_affine_derivative_bounds p hp hd _ _ hHt (hquery t ht).1 hforce.2
      A hA hsum hε hε1 hN hr k hk hrβ (fun j => c j-if j=i then t else 0)
      (fun j => if j=i then -1 else 0) (by intro j; dsimp only; split_ifs <;> norm_num)
      (hquery t ht).2.1 (hquery t ht).2.2
    have hshift := congrFun (iteratedDeriv_comp_const_add 2
      (RuntimeCurvature.prepCurve H A ((1:ℝ)/2^k) (theta p) (a p) c i) t) 0
    rw [prep_shift] at hshift
    simpa only [add_zero,hshift] using hb.1

end HigherRankKSRuntime.RuntimePreparationBounds
