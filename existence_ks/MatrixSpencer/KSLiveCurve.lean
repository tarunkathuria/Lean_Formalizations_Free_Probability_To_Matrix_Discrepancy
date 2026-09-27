import MatrixSpencer.KSGlobalMinima

/-! Curves on the original live-coordinate face, including exact finite sum restriction. -/

open Matrix Filter Topology Set
open scoped BigOperators
noncomputable section
namespace MatrixSpencer.KSLiveCurve
open KSPotentialModels
variable {N : ℕ}

abbrev Live (a : ℝ) (x : Fin N → ℝ) := {i : Fin N // |x i| < a}

def extend (a : ℝ) (x : Fin N → ℝ) (h : Live a x → ℝ) (i : Fin N) : ℝ :=
  if hi : |x i| < a then h ⟨i, hi⟩ else 0

def path (a : ℝ) (x : Fin N → ℝ) (h : Live a x → ℝ) (t : ℝ) : Fin N → ℝ :=
  fun i => x i + t * extend a x h i

@[simp] theorem extend_live (a : ℝ) (x : Fin N → ℝ) (h : Live a x → ℝ) (i : Live a x) :
    extend a x h i = h i := by simp only [extend, dif_pos i.property]

theorem extend_dead (a : ℝ) (x : Fin N → ℝ) (h : Live a x → ℝ)
    (i : Fin N) (hi : ¬ |x i| < a) : extend a x h i = 0 := by simp only [extend, dif_neg hi]

@[simp] theorem path_zero (a : ℝ) (x : Fin N → ℝ) (h : Live a x → ℝ) : path a x h 0 = x := by
  funext i; simp only [path, zero_mul, add_zero]

@[simp] theorem path_live (a : ℝ) (x : Fin N → ℝ) (h : Live a x → ℝ)
    (t : ℝ) (i : Live a x) : path a x h t i = x i + t * h i := by
  simp only [path, extend_live]

theorem path_dead (a : ℝ) (x : Fin N → ℝ) (h : Live a x → ℝ)
    (t : ℝ) (i : Fin N) (hi : ¬ |x i| < a) : path a x h t i = x i := by
  simp only [path, extend_dead a x h i hi, mul_zero, add_zero]

theorem extend_ne_zero (a : ℝ) (x : Fin N → ℝ) {h : Live a x → ℝ} (hh : h ≠ 0) :
    extend a x h ≠ 0 := by
  intro hz
  apply hh
  funext i
  have hi := congrFun hz i.val
  simpa only [extend_live, Pi.zero_apply] using hi

theorem eventually_live {a : ℝ} (x : Fin N → ℝ) (h : Live a x → ℝ) :
    ∀ᶠ t in 𝓝 (0 : ℝ), ∀ i : Live a x, |path a x h t i| < a := by
  rw [Filter.eventually_all]
  intro i
  have hc : Continuous (fun t : ℝ => |x i + t * h i|) := by fun_prop
  have hi : |x i + (0 : ℝ) * h i| < a := by simpa only [zero_mul, add_zero] using i.property
  simpa only [path_live] using hc.continuousAt.eventually (isOpen_Iio.mem_nhds hi)

theorem eventually_in_cube {a : ℝ} {x : Fin N → ℝ} (hx : x ∈ ksCube a)
    (h : Live a x → ℝ) : ∀ᶠ t in 𝓝 (0 : ℝ), path a x h t ∈ ksCube a := by
  filter_upwards [eventually_live x h] with t ht
  constructor <;> intro i
  · by_cases hi : |x i| < a
    · exact (abs_lt.mp (ht ⟨i, hi⟩)).1.le
    · rw [path_dead a x h t i hi]
      exact hx.1 i
  · by_cases hi : |x i| < a
    · exact (abs_lt.mp (ht ⟨i, hi⟩)).2.le
    · rw [path_dead a x h t i hi]
      exact hx.2 i

theorem eventually_same_live {a : ℝ} (x : Fin N → ℝ) (h : Live a x → ℝ) :
    ∀ᶠ t in 𝓝 (0 : ℝ), live a (path a x h t) = live a x := by
  filter_upwards [eventually_live x h] with t ht
  ext i
  simp only [live, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hi : |x i| < a
  · exact iff_of_true (ht ⟨i, hi⟩) hi
  · rw [path_dead a x h t i hi]

theorem isLocalMin_path {a : ℝ} {x : Fin N → ℝ} (hx : x ∈ ksCube a)
    (f : (Fin N → ℝ) → ℝ) (hmin : ∀ y ∈ ksCube a, f x ≤ f y)
    (h : Live a x → ℝ) : IsLocalMin (fun t => f (path a x h t)) 0 := by
  filter_upwards [eventually_in_cube hx h] with t ht
  simpa only [path_zero] using hmin (path a x h t) ht

theorem sum_restrict_live {E : Type*} [AddCommMonoid E]
    (a : ℝ) (x : Fin N → ℝ) (f : Fin N → E)
    (hzero : ∀ i, ¬ |x i| < a → f i = 0) :
    ∑ i, f i = ∑ i : Live a x, f i := by
  have hs : ∑ i ∈ live a x, f i = ∑ i, f i := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    apply hzero i
    simpa only [live, Finset.mem_filter, Finset.mem_univ, true_and] using hi
  rw [← hs]
  exact Finset.sum_subtype (live a x) (by intro i; simp only [live, Finset.mem_filter, Finset.mem_univ, true_and]) f

theorem sum_extend_smul {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (a : ℝ) (x : Fin N → ℝ) (h : Live a x → ℝ) (A : Fin N → E) :
    ∑ i, extend a x h i • A i = ∑ i : Live a x, h i • A i := by
  rw [sum_restrict_live a x _ (by intro i hi; rw [extend_dead a x h i hi, zero_smul])]
  simp only [extend_live]

theorem center_path {n : Type*} [Fintype n] [DecidableEq n]
    (A : Fin N → Matrix n n ℂ) (a : ℝ) (x : Fin N → ℝ) (h : Live a x → ℝ) (t : ℝ) :
    center A (path a x h t) = center A x + t • (∑ i : Live a x, h i • A i) := by
  simp only [KSPotentialModels.center, path, add_smul, MulAction.mul_smul, Finset.sum_add_distrib, ← Finset.smul_sum]
  rw [sum_extend_smul]

theorem naturalOwner_dead {x : Fin N → ℝ} (hx : x ∈ ksCube 1) (u : ℝ)
    (i : Fin N) (hi : ¬ |x i| < 1) : naturalOwners u x i = 0 := by
  have habs : |x i| = 1 := le_antisymm (abs_le.mpr ⟨hx.1 i, hx.2 i⟩) (not_lt.mp hi)
  have hsq : x i ^ 2 = 1 := by nlinarith [sq_abs (x i)]
  simp only [naturalOwners, hsq, sub_self, mul_zero]

end MatrixSpencer.KSLiveCurve
