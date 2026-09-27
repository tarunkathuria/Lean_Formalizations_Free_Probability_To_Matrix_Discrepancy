import AugmentedHigherRankKS.CubeCompletion
import AugmentedHigherRankKS.EpochBounds

/-! Reassembly of live-owner epochs in the original cube. Each original
matrix keeps a single coefficient throughout all epochs. -/

open Matrix MatrixSpencer Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace AugmentedHigherRankKS

variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]

abbrev LiveOwners (x : CubePoint ι) := {i // i ∈ cubeLive x}

def liftLiveCube (x : CubePoint ι) (y : CubePoint (LiveOwners x)) : CubePoint ι := by
  classical
  refine ⟨fun i => if hi : i ∈ cubeLive x then y.val ⟨i, hi⟩ else x.val i, ?_⟩
  intro i
  dsimp
  split_ifs with hi
  · exact y.property ⟨i, hi⟩
  · exact x.property i

theorem liftLiveCube_frozen (x : CubePoint ι) (y : CubePoint (LiveOwners x))
    (i : ι) (hi : i ∉ cubeLive x) : (liftLiveCube x y).val i = x.val i := by
  classical
  simp only [liftLiveCube, dif_neg hi]

@[simp] theorem liftLiveCube_live (x : CubePoint ι) (y : CubePoint (LiveOwners x))
    (i : LiveOwners x) : (liftLiveCube x y).val i = y.val i := by
  classical
  simp only [liftLiveCube, dif_pos i.property]

theorem sum_eq_live_of_zero {E : Type*} [AddCommMonoid E]
    (x : CubePoint ι) (f : ι → E) (hf : ∀ i, i ∉ cubeLive x → f i = 0) :
    ∑ i, f i = ∑ i : LiveOwners x, f i := by
  rw [Finset.sum_coe_sort]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i hi hn
  exact hf i hn

theorem cubeMass_eq_live_sum (A : ι → Matrix n n ℂ) (x : CubePoint ι) :
    cubeMass A x = ∑ i : LiveOwners x, A i := by
  exact (Finset.sum_coe_sort (cubeLive x) A).symm

theorem cubeMass_eq_ite (A : ι → Matrix n n ℂ) (x : CubePoint ι) :
    cubeMass A x = ∑ i, if |x.val i| < 1 then A i else 0 := by
  classical
  simp [cubeMass, cubeLive, Finset.sum_filter]

def stateCube {a R : ℝ} (z : EpochState ι) (hz : z ∈ epochDomain a R) : CubePoint ι :=
  ⟨position z, fun i => abs_le.mpr ⟨(hz i).1, (hz i).2.1⟩⟩

theorem lifted_discrepancy_eq (A : ι → Matrix n n ℂ) (x : CubePoint ι)
    {a R : ℝ} (z : EpochState (LiveOwners x)) (hz : z ∈ epochDomain a R) :
    cubeCenter A (liftLiveCube x (stateCube z hz)) - cubeCenter A x =
      discrepancy (fun i : LiveOwners x => A i) (fun i => x.val i) z := by
  unfold cubeCenter
  rw [← Finset.sum_sub_distrib]
  simp only [← sub_smul]
  rw [sum_eq_live_of_zero x _ (by
    intro i hi
    rw [liftLiveCube_frozen x (stateCube z hz) i hi]
    simp)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [liftLiveCube_live]
  rfl

theorem lifted_unfinishedMass_eq (A : ι → Matrix n n ℂ) (x : CubePoint ι)
    {a R : ℝ} (z : EpochState (LiveOwners x)) (hz : z ∈ epochDomain a R) :
    cubeMass A (liftLiveCube x (stateCube z hz)) =
      unfinishedMass (fun i : LiveOwners x => A i) z := by
  classical
  rw [cubeMass_eq_ite]
  rw [sum_eq_live_of_zero x _ (by
    intro i hi
    rw [liftLiveCube_frozen x (stateCube z hz) i hi, cube_not_live_abs_eq hi]
    simp)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [liftLiveCube_live]
  rfl

/-- A concrete zero-reserve epoch on live owners gives a cube transition,
with all former faces preserved and both norm budgets retained. -/
theorem lift_exhausted_epoch (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) (x : CubePoint ι)
    {a R D : ℝ} (ha : a ≠ 0) (hR : 0 < R)
    (z : EpochState (LiveOwners x)) (hz : z ∈ epochDomain a R)
    (hc : ∀ i, reserve z i = 0)
    (hD : epochCenterSize (fun i : LiveOwners x => A i) (fun i => x.val i) z ≤ D) :
    ∃ y : CubePoint ι,
      (∀ i, i ∉ cubeLive x → y.val i = x.val i) ∧
      ‖cubeMass A y‖ ≤ (‖cubeMass A x‖ + D) / R ∧
      ‖cubeCenter A y - cubeCenter A x‖ ≤ D := by
  let y := liftLiveCube x (stateCube z hz)
  refine ⟨y, liftLiveCube_frozen x (stateCube z hz), ?_, ?_⟩
  · dsimp only [y]
    rw [lifted_unfinishedMass_eq]
    rw [cubeMass_eq_live_sum]
    exact (exhausted_epoch_bounds (fun i : LiveOwners x => A i) (fun i => hA i)
      (fun i => x.val i) ha hR hz hc hD).2
  · dsimp only [y]
    rw [lifted_discrepancy_eq]
    exact (le_max_left _ _).trans hD

/-- The matrix reserve epoch composes on the original cube. The family below
is an internal theorem argument, discharged by the compact analytic epoch. -/
theorem cube_completion_of_exhausted_epochs [Nonempty n]
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    {a δ : ℝ} (ha : a ≠ 0) (hδ : 0 ≤ δ)
    (hepoch : ∀ x : CubePoint ι, δ ^ 2 < ‖cubeMass A x‖ →
      ∃ z : EpochState (LiveOwners x), z ∈ epochDomain a 4 ∧
        (∀ i, reserve z i = 0) ∧
        epochCenterSize (fun i : LiveOwners x => A i) (fun i => x.val i) z ≤
          δ * Real.sqrt ‖cubeMass A x‖) :
    ∀ x : CubePoint ι, ∃ y : CubePoint ι, cubeTerminal y ∧
      ‖cubeCenter A y - cubeCenter A x‖ ≤ 4 * δ * Real.sqrt ‖cubeMass A x‖ := by
  apply cube_completion_of_contracting_epochs A hA hδ
  intro x hx
  obtain ⟨z, hz, hc, hD⟩ := hepoch x hx
  obtain ⟨y, hf, hm, hi⟩ := lift_exhausted_epoch A hA x ha (by norm_num) z hz hc hD
  refine ⟨y, hf, hm.trans ?_, hi⟩
  have hs := Real.sqrt_nonneg ‖cubeMass A x‖
  have hsq := Real.sq_sqrt (norm_nonneg (cubeMass A x))
  have hsδ : δ ≤ Real.sqrt ‖cubeMass A x‖ := by nlinarith
  have hmul := mul_le_mul_of_nonneg_right hsδ hs
  nlinarith

def originCube : CubePoint ι := ⟨fun _ => 0, fun _ => by norm_num⟩

@[simp] theorem cubeCenter_origin (A : ι → Matrix n n ℂ) :
    cubeCenter A originCube = 0 := by simp [cubeCenter, originCube]

@[simp] theorem cubeMass_origin (A : ι → Matrix n n ℂ) :
    cubeMass A originCube = ∑ i, A i := by simp [cubeMass, cubeLive, originCube]

/-- One real sign per original atom, obtained from the reserve epochs. -/
theorem signing_of_exhausted_epochs [Nonempty n]
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    {a δ : ℝ} (ha : a ≠ 0) (hδ : 0 ≤ δ)
    (hepoch : ∀ x : CubePoint ι, δ ^ 2 < ‖cubeMass A x‖ →
      ∃ z : EpochState (LiveOwners x), z ∈ epochDomain a 4 ∧
        (∀ i, reserve z i = 0) ∧
        epochCenterSize (fun i : LiveOwners x => A i) (fun i => x.val i) z ≤
          δ * Real.sqrt ‖cubeMass A x‖) :
    ∃ σ : ι → ℝ, (∀ i, σ i = 1 ∨ σ i = -1) ∧
      ‖∑ i, σ i • A i‖ ≤ 4 * δ * Real.sqrt ‖∑ i, A i‖ := by
  obtain ⟨y, hy, hnorm⟩ := cube_completion_of_exhausted_epochs A hA ha hδ hepoch originCube
  refine ⟨y.val, hy, ?_⟩
  simpa [cubeCenter, cubeMass, cubeLive, originCube] using hnorm

end AugmentedHigherRankKS
