import HigherRankKSRuntime.RuntimeInputFactors
import HigherRankKSRuntime.GlobalEpochState
import SeamlessKS.RuntimeDirection
import MatrixSpencer.RealRAMKSInputSetup

/-! Exact whole-atom norms and their maximum are computed using realification,
permitted real EVD, and a finite scalar maximum. Small atoms are fixed at +1
in the original owner array, without modifying any input matrix. -/
noncomputable section
open Matrix MatrixSpencer Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace HigherRankKSRuntime.RuntimeInputNormalization
open AugmentedHigherRankKS RealRAM
open RealRAM.JacobiIteration (Counted)
variable {N d : ℕ}
local instance normalizationCStar : CStarAlgebra (SDPValue.Mat d) := {}

def atomNorm (A : SDPValue.Mat d) : Counted ℝ := SeamlessKS.RuntimeDirection.norm A

theorem atomNorm_value (A : SDPValue.Mat d) (hA : A.IsHermitian) : (atomNorm A).value=‖A‖ := by
  rw [atomNorm,SeamlessKS.RuntimeDirection.norm_value,
    SeamlessKS.ExactEVD.normReport_exact _ (KSComplexNorm.realificationFin_symmetric A hA),
    KSComplexNorm.realificationFin_norm]

theorem atomNorm_cost (A : SDPValue.Mat d) : (atomNorm A).cost≤5600*(d+1)^3 := by
  have h := SeamlessKS.RuntimeDirection.norm_cost A
  have hp : (d+d+1)^3 ≤ (2*(d+1))^3 := Nat.pow_le_pow_left (by omega) 3
  rw [mul_pow] at hp
  norm_num at hp
  exact h.trans (by nlinarith)

def norms (A : Fin N → SDPValue.Mat d) : Counted (Fin N → ℝ) :=
  ⟨fun i => (atomNorm (A i)).value, (∑ i, (atomNorm (A i)).cost)+N+1⟩

theorem norms_value (A : Fin N → SDPValue.Mat d) (hA : ∀ i,(A i).IsHermitian) :
    (norms A).value=fun i => ‖A i‖ := funext fun i => atomNorm_value (A i) (hA i)

theorem norms_cost (A : Fin N → SDPValue.Mat d) :
    (norms A).cost ≤ 5600*N*(d+1)^3+N+1 := by
  have hh := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => atomNorm_cost (A i))
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hh
  dsimp only [norms]
  nlinarith

def epsilon (A : Fin N → SDPValue.Mat d) : Counted ℝ :=
  let ns := norms A
  let mx := KSInputSetup.maximum ((List.finRange N).map ns.value)
  ⟨mx.value,ns.cost+mx.cost+3*N+1⟩

theorem epsilon_value (A : Fin N → SDPValue.Mat d) (hA : ∀ i,(A i).IsHermitian) :
    (epsilon A).value = KSEighthManuscriptPreprocess.maximum ((List.finRange N).map (fun i => ‖A i‖)) := by
  simp only [epsilon,KSInputSetup.maximum_value,norms_value A hA]

theorem epsilon_cost (A : Fin N → SDPValue.Mat d) :
    (epsilon A).cost ≤ 5610*(N+1)*(d+1)^3 := by
  have hn := norms_cost A
  have hm := KSInputSetup.maximum_cost ((List.finRange N).map (norms A).value)
  simp only [List.length_map,List.length_finRange] at hm
  have hpow : 1 ≤ (d+1)^3 := Nat.one_le_pow 3 (d+1) (by omega)
  have hN := Nat.mul_le_mul_left N hpow
  dsimp only [epsilon]
  nlinarith

theorem epsilon_nonneg (A : Fin N → SDPValue.Mat d) (hA : ∀ i,(A i).IsHermitian) :
    0 ≤ (epsilon A).value := by
  rw [epsilon_value A hA]
  exact KSEighthManuscriptPreprocess.maximum_nonneg _

theorem norm_le_epsilon (A : Fin N → SDPValue.Mat d) (hA : ∀ i,(A i).IsHermitian) (i : Fin N) :
    ‖A i‖ ≤ (epsilon A).value := by
  rw [epsilon_value A hA]
  exact KSEighthManuscriptPreprocess.le_maximum (List.mem_map.mpr ⟨i,List.mem_finRange i,rfl⟩)

theorem epsilon_le (A : Fin N → SDPValue.Mat d) (hA : ∀ i,(A i).IsHermitian)
    {ε : ℝ} (hε : 0 ≤ ε) (hN : ∀ i,‖A i‖≤ε) : (epsilon A).value≤ε := by
  rw [epsilon_value A hA]
  apply KSEighthManuscriptPreprocess.maximum_le hε
  intro v hv
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hv
  exact hN i

theorem atom_norm_le_one [Nonempty (Fin d)] (A : Fin N → SDPValue.Mat d)
    (hA : ∀ i,(A i).PosSemidef) (hs : ∑ i,A i ≤ 1) (i : Fin N) : ‖A i‖≤1 := by
  have hi : A i ≤ ∑ j,A j := Finset.single_le_sum (fun j _ => (hA j).nonneg) (Finset.mem_univ i)
  simpa only [norm_one] using CStarAlgebra.norm_le_norm_of_nonneg_of_le (hA i).nonneg (hi.trans hs)

theorem epsilon_le_one [Nonempty (Fin d)] (A : Fin N → SDPValue.Mat d)
    (hA : ∀ i,(A i).PosSemidef) (hs : ∑ i,A i ≤ 1) : (epsilon A).value≤1 :=
  epsilon_le A (fun i => (hA i).isHermitian) zero_le_one (atom_norm_le_one A hA hs)

theorem epsilon_lower [Nonempty (Fin d)] (A : Fin N → SDPValue.Mat d)
    (hA : ∀ i,(A i).PosSemidef) (hs : ∑ i,A i=1) (hN : 0 < N) :
    1/(N:ℝ) ≤ (epsilon A).value := by
  have hb : 1 ≤ (N:ℝ)*(epsilon A).value := by
    calc
      (1:ℝ) = ‖∑ i,A i‖ := by rw [hs,norm_one]
      _ ≤ ∑ i, ‖A i‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin N,(epsilon A).value :=
        Finset.sum_le_sum fun i _ => norm_le_epsilon A (fun j => (hA j).isHermitian) i
      _ = (N:ℝ)*(epsilon A).value := by simp
  exact (div_le_iff₀ (by exact_mod_cast hN)).mpr (by simpa only [mul_comm] using hb)

/-- Comparisons use the stored exact norm vector; entries are either 0 or 1. -/
def discard (A : Fin N → SDPValue.Mat d) (η : ℝ) : Counted (Fin N → ℝ) :=
  let ns := norms A
  ⟨fun i => if ns.value i≤η then 1 else 0,ns.cost+5*N+1⟩

theorem discard_value (A : Fin N → SDPValue.Mat d) (hA : ∀ i,(A i).IsHermitian)
    (η : ℝ) (i : Fin N) : (discard A η).value i = if ‖A i‖≤η then 1 else 0 := by
  simp only [discard,norms_value A hA]

theorem discard_cube (A : Fin N → SDPValue.Mat d) (η : ℝ) :
    ∀ i, |(discard A η).value i|≤1 := by
  intro i
  dsimp only [discard]
  split_ifs <;> norm_num

def discardCube (A : Fin N → SDPValue.Mat d) (η : ℝ) : CubePoint (Fin N) :=
  ⟨(discard A η).value,discard_cube A η⟩

theorem discard_cost (A : Fin N → SDPValue.Mat d) (η : ℝ) :
    (discard A η).cost≤5610*(N+1)*(d+1)^3 := by
  have hn := norms_cost A
  have hpow : 1 ≤ (d+1)^3 := Nat.one_le_pow 3 (d+1) (by omega)
  have hN := Nat.mul_le_mul_left N hpow
  dsimp only [discard]
  nlinarith

theorem discard_center_bound (A : Fin N → SDPValue.Mat d)
    (hA : ∀ i,(A i).IsHermitian) {η : ℝ} (hη : 0≤η) :
    ‖cubeCenter A (discardCube A η)‖≤(N:ℝ)*η := by
  calc
    _ ≤ ∑ i, ‖(discard A η).value i • A i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin N,η := by
      apply Finset.sum_le_sum
      intro i _
      rw [discard_value A hA]
      split_ifs with hi
      · simpa using hi
      · simpa using hη
    _ = _ := by simp

theorem discard_mass_le (A : Fin N → SDPValue.Mat d) (hA : ∀ i,(A i).PosSemidef) (η : ℝ) :
    cubeMass A (discardCube A η) ≤ ∑ i,A i := by
  rw [cubeMass_eq_ite]
  apply Finset.sum_le_sum
  intro i _
  split_ifs
  · exact le_rfl
  · exact (hA i).nonneg

theorem discard_live_large (A : Fin N → SDPValue.Mat d)
    (hA : ∀ i,(A i).IsHermitian) (η : ℝ) (i : Fin N)
    (hi : |(discardCube A η).val i|<1) : η < ‖A i‖ := by
  change |(discard A η).value i|<1 at hi
  rw [discard_value A hA] at hi
  by_contra hn
  have hs : ‖A i‖≤η := le_of_not_gt hn
  simp [hs] at hi

theorem discard_reset_large (A : Fin N → SDPValue.Mat d)
    (hA : ∀ i,(A i).IsHermitian) (η a R : ℝ) (i : Fin N)
    (hi : 0 < reserve (GlobalEpochs.resetState a R (discardCube A η)) i) : η≤‖A i‖ := by
  have hl : |(discardCube A η).val i|<1 := by
    by_contra hn
    simp [GlobalEpochs.resetState,reserve,hn] at hi
  exact (discard_live_large A hA η i hl).le

/-- A supplied rank bound is safely clamped to the physical dimension. -/
def rankBound (r d : ℕ) := max 1 (min r d)

theorem rankBound_one (r d : ℕ) : 1≤rankBound r d := le_max_left _ _
theorem rankBound_le {r d : ℕ} (hd : 1≤d) : rankBound r d≤d :=
  max_le hd (min_le_right _ _)
theorem rankBound_le_supplied {r d : ℕ} (hr : 1≤r) : rankBound r d≤r :=
  max_le hr (min_le_left _ _)
theorem atom_rank_le_rankBound (A : Fin N → SDPValue.Mat d) {r : ℕ}
    (hr : ∀ i,(A i).rank≤r) (i : Fin N) : (A i).rank≤rankBound r d :=
  (le_min (hr i) (A i).rank_le_width).trans (le_max_right _ _)

end HigherRankKSRuntime.RuntimeInputNormalization
