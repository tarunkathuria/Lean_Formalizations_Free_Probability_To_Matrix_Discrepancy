import AugmentedHigherRankKS.FourBlockQueryFloors
import AugmentedHigherRankKS.QueryCenterBounds

/-! The concrete centered-difference and preparation queries lie in the uniform domain. -/
noncomputable section
open Matrix MatrixSpencer HigherRankKS Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace AugmentedHigherRankKS
variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n] [Nonempty n]
local instance queryDomainCStar {j : Type*} [Fintype j] [DecidableEq j] :
  CStarAlgebra (Matrix j j ℂ) := {}

theorem quadratic_query_reserve {a ζ : ℝ} (ha : 0 < a) (hζ : 0 ≤ ζ)
    (c : ι → ℝ) (hc : ∀ i, 2*ζ ≤ c i) (hcu : ∀ i, c i ≤ 4*a)
    (u : EuclideanSpace ℝ ι) (hu : ‖u‖ ≤ Real.sqrt (ζ/(4*a))) (i : ι) :
    ζ ≤ c i-a*(u i)^2 ∧ c i-a*(u i)^2 ≤ 8*a := by
  have hi : |u i| ≤ ‖u‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le u i
  have hu2 : (u i)^2 ≤ ζ/(4*a) := by
    have h := hi.trans hu
    have hs := Real.sq_sqrt (div_nonneg hζ (by positivity : 0 ≤ 4*a))
    have hh := (sq_le_sq₀ (abs_nonneg (u i)) (Real.sqrt_nonneg (ζ/(4*a)))).mpr h
    simpa only [sq_abs,hs] using hh
  have hcost : a*(u i)^2 ≤ ζ/4 := by
    have h := (le_div_iff₀ (by positivity : 0 < 4*a)).mp hu2
    nlinarith
  constructor
  · linarith [hc i]
  · nlinarith [hcu i,sq_nonneg (u i)]

theorem quadratic_query_bounds (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (hsum : ∑ i, A i ≤ 1) (H : Matrix (FourSpin n) (FourSpin n) ℂ) (hH : ‖H‖ ≤ 5)
    (x : ι → ℝ) (hx : ∀ i, |x i| ≤ 1) {a ζ ρ : ℝ}
    (ha : 0 < a) (hζ : 0 ≤ ζ) (hρ : ρ ≤ 1)
    (c : ι → ℝ) (hc : ∀ i, 2*ζ ≤ c i) (hcu : ∀ i, c i ≤ 4*a)
    (u : EuclideanSpace ℝ ι) (hu : ‖u‖ ≤ min (ρ/4) (Real.sqrt (ζ/(4*a)))) :
    ‖H+∑ i, u i • forceAtom (x i) (A i)‖ ≤ 8 ∧
      (∀ i, ζ ≤ c i-a*(u i)^2 ∧ c i-a*(u i)^2 ≤ 8*a) := by
  refine ⟨coefficient_query_center_norm A hA hsum H hH x u hx ?_,?_⟩
  · intro i
    have hi : |u i| ≤ ‖u‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le u i
    have hh := hu.trans (min_le_left _ _)
    linarith
  · exact quadratic_query_reserve ha hζ c hc hcu u (hu.trans (min_le_right _ _))

theorem preparation_query_bounds (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (hN : ∀ i, ‖A i‖ ≤ 1) (H : Matrix (FourSpin n) (FourSpin n) ℂ) (hH : ‖H‖ ≤ 5)
    {a ζ t : ℝ} (ha : 1 ≤ a) (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1) (ht : 0 ≤ t) (htu : t ≤ ζ)
    (c : ι → ℝ) (hc : ∀ i, 2*ζ ≤ c i) (hcu : ∀ i, c i ≤ 4*a) (i : ι) :
    ‖H+augmentedCenter 0 ((t/a) • A i)‖ ≤ 8 ∧
      (∀ j, ζ ≤ c j-(Pi.single i t : ι → ℝ) j ∧ c j-(Pi.single i t : ι → ℝ) j ≤ 8*a) := by
  have ha0 : 0 < a := by linarith
  have hq : 0 ≤ t/a := div_nonneg ht ha0.le
  have hq1 : t/a ≤ 1 := (div_le_one ha0).mpr (by linarith)
  have hKH : ((t/a) • A i).IsHermitian := by
    change ((t/a) • A i)ᴴ = _
    simp only [Matrix.conjTranspose_smul,star_trivial,(hA i).isHermitian.eq]
  have hpert : ‖augmentedCenter (0 : Matrix n n ℂ) ((t/a) • A i)‖ ≤ 1 := by
    apply augmentedCenter_norm_le (by simp) hKH (by simp)
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hq]
    exact (mul_le_mul hq1 (hN i) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  refine ⟨(norm_add_le _ _).trans (by linarith),?_⟩
  intro j
  by_cases hji : j=i
  · subst j
    simp only [Pi.single_eq_same]
    constructor <;> nlinarith [hc i,hcu i]
  · simp only [Pi.single_eq_of_ne hji,sub_zero]
    constructor <;> nlinarith [hc j,hcu j]

/-- A matrix neighborhood of the actual density optimizer retains half its proved floor. -/
theorem query_density_neighbor_floor {S X : Matrix (FourSpin n) (FourSpin n) ℂ}
    (hX : X.IsHermitian) {s : ℝ}
    (hs : s • (1 : Matrix (FourSpin n) (FourSpin n) ℂ) ≤ S) (hN : ‖X‖ ≤ s/2) :
    (s/2) • (1 : Matrix (FourSpin n) (FourSpin n) ℂ) ≤ S+X := by
  have hx : -(‖X‖ • (1 : Matrix (FourSpin n) (FourSpin n) ℂ)) ≤ X := by
    simpa only [Algebra.algebraMap_eq_smul_one,neg_smul] using
      (show IsSelfAdjoint X from hX).neg_algebraMap_norm_le_self
  have hlo : -(s/2) • (1 : Matrix (FourSpin n) (FourSpin n) ℂ) ≤ X := by
    exact (smul_le_smul_of_nonneg_right (neg_le_neg hN) zero_le_one).trans (by simpa only [neg_smul] using hx)
  have hh := add_le_add hs hlo
  rw [← add_smul] at hh
  convert hh using 1 <;> ring
end AugmentedHigherRankKS
