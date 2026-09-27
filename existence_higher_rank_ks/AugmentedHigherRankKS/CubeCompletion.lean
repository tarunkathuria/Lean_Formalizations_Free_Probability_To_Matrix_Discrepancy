import AugmentedHigherRankKS.BudgetOrder
import AugmentedHigherRankKS.EpochIteration
import MatrixSpencer.SignedLift

/-! Concrete cube geometry and deterministic terminal rounding for the epoch
argument. The active set consists of original owners, never rank-one pieces. -/

open Matrix MatrixSpencer Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace AugmentedHigherRankKS

variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
local instance cubeCStar : CStarAlgebra (Matrix n n ℂ) := {}

abbrev CubePoint (ι : Type*) := {x : ι → ℝ // ∀ i, |x i| ≤ 1}

def cubeLive (x : CubePoint ι) : Finset ι := by
  classical
  exact Finset.univ.filter fun i => |x.val i| < 1

def cubeMass (A : ι → Matrix n n ℂ) (x : CubePoint ι) : Matrix n n ℂ :=
  ∑ i ∈ cubeLive x, A i

def cubeCenter (A : ι → Matrix n n ℂ) (x : CubePoint ι) : Matrix n n ℂ :=
  ∑ i, x.val i • A i

def cubeTerminal (x : CubePoint ι) : Prop := ∀ i, x.val i = 1 ∨ x.val i = -1

@[simp] theorem mem_cubeLive (x : CubePoint ι) (i : ι) :
    i ∈ cubeLive x ↔ |x.val i| < 1 := by simp [cubeLive]

theorem cube_not_live_abs_eq {x : CubePoint ι} {i : ι} (hi : i ∉ cubeLive x) :
    |x.val i| = 1 :=
  le_antisymm (x.property i) (le_of_not_gt (by simpa only [mem_cubeLive] using hi))

theorem cubeMass_nonneg (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) (x : CubePoint ι) : 0 ≤ cubeMass A x := by
  exact Finset.sum_nonneg fun i _ => (hA i).nonneg

/-- Any cube move preserving the frozen faces changes the matrix by at most
 twice the live PSD mass, independent of its dimension and the owner count. -/
theorem cube_increment_norm_le [Nonempty n] (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) (x y : CubePoint ι)
    (hfrozen : ∀ i, i ∉ cubeLive x → y.val i = x.val i) :
    ‖cubeCenter A y - cubeCenter A x‖ ≤ 2 * ‖cubeMass A x‖ := by
  have heq : cubeCenter A y - cubeCenter A x =
      ∑ i ∈ cubeLive x, (y.val i - x.val i) • A i := by
    unfold cubeCenter
    rw [← Finset.sum_sub_distrib]
    simp only [← sub_smul]
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i hi hn
    simp [hfrozen i hn]
  rw [heq]
  have hu : (∑ i ∈ cubeLive x, (y.val i - x.val i) • A i) ≤
      (2 : ℝ) • cubeMass A x := by
    rw [cubeMass, Finset.smul_sum]
    apply Finset.sum_le_sum
    intro i hi
    apply smul_le_smul_of_nonneg_right _ (hA i).nonneg
    have hx := abs_le.mp (x.property i)
    have hy := abs_le.mp (y.property i)
    linarith
  have hl : -((2 : ℝ) • cubeMass A x) ≤
      ∑ i ∈ cubeLive x, (y.val i - x.val i) • A i := by
    rw [cubeMass, Finset.smul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro i hi
    rw [← neg_smul]
    apply smul_le_smul_of_nonneg_right _ (hA i).nonneg
    have hx := abs_le.mp (x.property i)
    have hy := abs_le.mp (y.property i)
    linarith
  have hB := IsSelfAdjoint.le_algebraMap_norm_self (cubeMass_nonneg A hA x).posSemidef.isHermitian
  rw [Algebra.algebraMap_eq_smul_one] at hB
  have h2 := smul_le_smul_of_nonneg_left hB (show (0 : ℝ) ≤ 2 by norm_num)
  rw [smul_smul] at h2
  apply hermitian_norm_le_of_order _ ((neg_le_neg h2).trans hl) (hu.trans h2)
  change (∑ i ∈ cubeLive x, (y.val i - x.val i) • A i)ᴴ = _
  simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul,
    star_trivial, (hA _).isHermitian.eq]

/-- Deterministic outward rounding, preserving every coordinate already fixed. -/
def roundCube (x : CubePoint ι) : CubePoint ι := by
  classical
  refine ⟨fun i => if 0 ≤ x.val i then 1 else -1, ?_⟩
  intro i
  dsimp
  split_ifs <;> norm_num

theorem roundCube_terminal (x : CubePoint ι) : cubeTerminal (roundCube x) := by
  classical
  intro i
  simp only [roundCube]
  split_ifs <;> simp

theorem roundCube_frozen (x : CubePoint ι) (i : ι) (hi : i ∉ cubeLive x) :
    (roundCube x).val i = x.val i := by
  classical
  have hx := cube_not_live_abs_eq hi
  rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp hx with hx | hx
  · simp [roundCube, hx]
  · simp [roundCube, hx]

theorem roundCube_norm_le [Nonempty n] (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) (x : CubePoint ι) :
    ‖cubeCenter A (roundCube x) - cubeCenter A x‖ ≤ 2 * ‖cubeMass A x‖ :=
  cube_increment_norm_le A hA x (roundCube x) (roundCube_frozen x)

/-- Strict live-mass contraction fixes at least one previously live owner. -/
theorem cubeLive_card_lt_of_mass_lt (A : ι → Matrix n n ℂ) (x y : CubePoint ι)
    (hfrozen : ∀ i, i ∉ cubeLive x → y.val i = x.val i)
    (hmass : ‖cubeMass A y‖ < ‖cubeMass A x‖) :
    (cubeLive y).card < (cubeLive x).card := by
  have hsub : cubeLive y ⊆ cubeLive x := by
    intro i hi
    by_contra hn
    have hx := cube_not_live_abs_eq hn
    have hy := (mem_cubeLive y i).mp hi
    rw [hfrozen i hn, hx] at hy
    exact (lt_irrefl (1 : ℝ)) hy
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨hsub, ?_⟩
  intro heq
  apply (lt_irrefl ‖cubeMass A x‖)
  simpa only [cubeMass, heq] using hmass

/-- Global cube completion once the concrete epoch theorem is supplied.
This internal assembly theorem will be invoked with the proved reserve epoch. -/
theorem cube_completion_of_contracting_epochs [Nonempty n]
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hepoch : ∀ x : CubePoint ι, δ ^ 2 < ‖cubeMass A x‖ →
      ∃ y : CubePoint ι,
        (∀ i, i ∉ cubeLive x → y.val i = x.val i) ∧
        ‖cubeMass A y‖ ≤ ‖cubeMass A x‖ / 2 ∧
        ‖cubeCenter A y - cubeCenter A x‖ ≤ δ * Real.sqrt ‖cubeMass A x‖) :
    ∀ x : CubePoint ι, ∃ z : CubePoint ι, cubeTerminal z ∧
      ‖cubeCenter A z - cubeCenter A x‖ ≤ 4 * δ * Real.sqrt ‖cubeMass A x‖ := by
  apply finite_epoch_completion (cubeCenter A) (fun x => ‖cubeMass A x‖)
    (fun x => (cubeLive x).card) cubeTerminal hδ (fun x => norm_nonneg _)
  · intro x hx
    exact ⟨roundCube x, roundCube_terminal x, roundCube_norm_le A hA x⟩
  · intro x hx
    obtain ⟨y, hf, hm, hi⟩ := hepoch x hx
    refine ⟨y, cubeLive_card_lt_of_mass_lt A x y hf ?_, hm, hi⟩
    have hpos : 0 < ‖cubeMass A x‖ := lt_of_le_of_lt (sq_nonneg δ) hx
    linarith

end AugmentedHigherRankKS
