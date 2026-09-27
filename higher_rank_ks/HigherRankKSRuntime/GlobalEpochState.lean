import HigherRankKSRuntime.GlobalEpochs

/-! Reset only unfinished original owners. The deterministic budget is
compared with their live PSD mass, retaining all fractional coordinates. -/
open Matrix MatrixSpencer Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace HigherRankKSRuntime.GlobalEpochs
open AugmentedHigherRankKS
variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
local instance globalCStar : CStarAlgebra (Matrix n n ℂ) := {}

def resetState (a R : ℝ) (x : CubePoint ι) : EpochState ι :=
  (x.val,fun _ => 0,fun i => if |x.val i| < 1 then a*R else 0)

theorem resetState_mem {a R : ℝ} (ha : 0 ≤ a) (hR : 0 ≤ R)
    (x : CubePoint ι) : resetState a R x ∈ epochDomain a R := by
  intro i
  have hx := abs_le.mp (x.property i)
  have har := mul_nonneg ha hR
  by_cases hi : |x.val i| < 1
  · simp only [resetState,position,spent,reserve,if_pos hi]
    exact ⟨hx.1,hx.2,le_rfl,hR,har,le_rfl,by simp,by simp⟩
  · have he : |x.val i| = 1 := le_antisymm (x.property i) (le_of_not_gt hi)
    have hs : (x.val i)^2 = 1 := by nlinarith [sq_abs (x.val i)]
    simp only [resetState,position,spent,reserve,if_neg hi]
    exact ⟨hx.1,hx.2,le_rfl,hR,le_rfl,har,by simpa using har,by simp [hs]⟩

@[simp] theorem resetState_position (a R : ℝ) (x : CubePoint ι) :
    position (resetState a R x) = x.val := rfl

@[simp] theorem resetState_spent (a R : ℝ) (x : CubePoint ι) :
    spent (resetState a R x) = 0 := rfl

@[simp] theorem resetState_discrepancy (A : ι → Matrix n n ℂ)
    (a R : ℝ) (x : CubePoint ι) : discrepancy A x.val (resetState a R x) = 0 := by
  simp [discrepancy]

@[simp] theorem resetState_budgetCenter (A : ι → Matrix n n ℂ)
    (a R : ℝ) (x : CubePoint ι) : budgetCenter A x.val (resetState a R x) = 0 := by
  simp [budgetCenter]

theorem initialRemaining_le_cubeMass (A : ι → Matrix n n ℂ)
    (hA : ∀ i,(A i).PosSemidef) (x : CubePoint ι) :
    initialRemaining A x.val ≤ cubeMass A x := by
  rw [cubeMass_eq_ite]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : |x.val i| < 1
  · simp only [if_pos hi]
    simpa only [one_smul] using smul_le_smul_of_nonneg_right
      (show 1-(x.val i)^2 ≤ 1 by nlinarith [sq_nonneg (x.val i)]) (hA i).nonneg
  · have he : |x.val i| = 1 := le_antisymm (x.property i) (le_of_not_gt hi)
    have hs : (x.val i)^2 = 1 := by nlinarith [sq_abs (x.val i)]
    simp [hi,hs]

theorem stateCube_mass {a R : ℝ} (A : ι → Matrix n n ℂ)
    (z : EpochState ι) (hz : z ∈ epochDomain a R) :
    cubeMass A (stateCube z hz) = unfinishedMass A z := by
  rw [cubeMass_eq_ite]
  rfl

theorem stateCube_center {a R : ℝ} (A : ι → Matrix n n ℂ)
    (x : CubePoint ι) (z : EpochState ι) (hz : z ∈ epochDomain a R) :
    cubeCenter A (stateCube z hz) - cubeCenter A x = discrepancy A x.val z := by
  simp only [cubeCenter,← Finset.sum_sub_distrib,← sub_smul]
  rfl

/-- The full-owner representation retains the smaller live-mass budget. -/
theorem terminal_live_mass_bound (A : ι → Matrix n n ℂ)
    (hA : ∀ i,(A i).PosSemidef) (x : CubePoint ι)
    {a R : ℝ} (ha : a ≠ 0) (hR : 0 < R)
    {z : EpochState ι} (hz : z ∈ epochDomain a R)
    (hc : ControllerLoop.Terminal z) :
    ‖cubeMass A (stateCube z hz)‖ ≤
      (‖cubeMass A x‖ + ‖budgetCenter A x.val z‖)/R := by
  rw [stateCube_mass]
  have ho := terminal_mass_le_budget A hA ha hz hc
  rw [budget_decomposition A x.val z] at ho
  have ho' := ho.trans (add_le_add_right (initialRemaining_le_cubeMass A hA x) _)
  have hn := (CStarAlgebra.norm_le_norm_of_nonneg_of_le
    (smul_nonneg hR.le (unfinishedMass_nonneg A hA z)) ho').trans
    (norm_add_le (cubeMass A x) (budgetCenter A x.val z))
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos hR] at hn
  exact (le_div_iff₀ hR).2 (by simpa only [mul_comm] using hn)

theorem terminal_cube_contract (A : ι → Matrix n n ℂ)
    (hA : ∀ i,(A i).PosSemidef) (x : CubePoint ι)
    {a δ : ℝ} (ha : a ≠ 0) (hδ : 0 ≤ δ)
    (hlarge : δ^2 < ‖cubeMass A x‖)
    {z : EpochState ι} (hz : z ∈ epochDomain a 4)
    (hc : ControllerLoop.Terminal z)
    (hsize : epochCenterSize A x.val z ≤ δ*Real.sqrt ‖cubeMass A x‖) :
    ‖cubeMass A (stateCube z hz)‖ ≤ ‖cubeMass A x‖/2 ∧
    ‖cubeCenter A (stateCube z hz)-cubeCenter A x‖ ≤ δ*Real.sqrt ‖cubeMass A x‖ := by
  have hK := (le_max_right _ _).trans hsize
  have hm := terminal_live_mass_bound A hA x ha (by norm_num : (0:ℝ)<4) hz hc
  have hs := Real.sqrt_nonneg ‖cubeMass A x‖
  have hsq := Real.sq_sqrt (norm_nonneg (cubeMass A x))
  have hd : δ ≤ Real.sqrt ‖cubeMass A x‖ := by nlinarith
  have hmul := mul_le_mul_of_nonneg_right hd hs
  refine ⟨by nlinarith,?_⟩
  rw [stateCube_center]
  exact (le_max_left _ _).trans hsize

theorem resetState_source (A : ι → Matrix n n ℂ) (β a R : ℝ)
    (x : CubePoint ι) (S : Matrix (FourSpin n) (FourSpin n) ℂ) :
    source A β (reserve (resetState a R x)) S =
      source (fun i : LiveOwners x => A i) β (fun _ => a*R) S := by
  unfold source
  rw [sum_eq_live_of_zero x _ (by
    intro i hi
    have hn : ¬ |x.val i| < 1 := by simpa [cubeLive] using hi
    simp [resetState,reserve,hn])]
  apply Finset.sum_congr rfl
  intro i _
  have hi : |x.val i| < 1 := by simpa only [cubeLive,Finset.mem_filter,Finset.mem_univ,true_and] using i.property
  simp [resetState,reserve,hi]

/-- Resetting reserves costs the square root of the current live mass,
not the mass of the full original family. -/
theorem resetState_potential_le [Nonempty n]
    (A : ι → Matrix n n ℂ) (hA : ∀ i,(A i).PosSemidef)
    (x : CubePoint ι) {ε : ℝ} (hε : 0 ≤ ε) (hN : ∀ i,‖A i‖ ≤ ε)
    {r : ℕ} (hr : ∀ i,(A i).rank ≤ r)
    {β : ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    {a R θ : ℝ} (haR : 0 ≤ a*R) (hθ : 0 ≤ θ) :
    epochPotential A β θ x.val (resetState a R x) ≤
      2*Real.sqrt (4*(a*R)*ε*(r:ℝ)^β*‖cubeMass A x‖) +
      2*θ*Real.sqrt (Fintype.card (FourSpin n):ℝ) := by
  have hc : ∀ i,0 ≤ reserve (resetState a R x) i := by
    intro i
    dsimp [resetState,reserve]
    split_ifs <;> positivity
  have hsum : ∑ i : LiveOwners x,A i ≤
      ‖cubeMass A x‖ • (1 : Matrix n n ℂ) := by
    rw [← cubeMass_eq_live_sum]
    simpa only [Algebra.algebraMap_eq_smul_one] using
      IsSelfAdjoint.le_algebraMap_norm_self (cubeMass_nonneg A hA x).posSemidef.isHermitian
  have hbudget : ∀ S ∈ densitySet,
      realTrace (source A β (reserve (resetState a R x)) S) ≤
        4*(a*R)*ε*(r:ℝ)^β*‖cubeMass A x‖ := by
    intro S hS
    rw [resetState_source]
    exact source_trace_le_mass (fun i : LiveOwners x => A i) (fun i => hA i)
      hsum hε (fun i => hN i) (fun i => hr i) hβ hβ1 haR (fun _ => le_rfl) hS
  unfold epochPotential
  rw [resetState_discrepancy,resetState_budgetCenter]
  have hz : augmentedCenter (0 : Matrix n n ℂ) 0 = 0 := by
    simp [augmentedCenter,signedLift]
  rw [hz]
  exact potential_zero_le_source_budget A hβ.le hβ1.le hc hθ hbudget

end HigherRankKSRuntime.GlobalEpochs
