import HigherRankKSRuntime.RuntimeInputFactors
import AugmentedHigherRankKS.EpochPotential
import MatrixSpencer.RealRAMComplexArithmetic

/-! An actual state value report assembles every center entry by scalar
circuits and reuses the input factors. Complex entries are pairs of real
registers. No matrix sum or optimized potential is a machine primitive. -/
noncomputable section
open Matrix MatrixSpencer
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace HigherRankKSRuntime.RuntimeStateReport
open AugmentedHigherRankKS RealRAM
open RealRAM.JacobiIteration (Counted)
variable {N d : ℕ}

abbrev Input (N d : ℕ) := (Fin N × Fin 4) ⊕ (Fin N × Fin d × Fin d × Bool)

def input (A : Fin N → SDPValue.Mat d) (x₀ : Fin N → ℝ)
    (z : EpochState (Fin N)) : Input N d → ℝ
  | .inl (i,j) => if j=0 then x₀ i else if j=1 then position z i
      else if j=2 then spent z i else reserve z i
  | .inr (i,j,k,b) => if b then (A i j k).im else (A i j k).re

def hCoeff (i : Fin N) : Expr (Input N d) :=
  .sub (.input (.inl (i,1))) (.input (.inl (i,0)))
def kCoeff (i : Fin N) : Expr (Input N d) :=
  .add (.sub (.mul (.input (.inl (i,0))) (.input (.inl (i,0))))
      (.mul (.input (.inl (i,1))) (.input (.inl (i,1))))) (.input (.inl (i,2)))
def atomEntry (i : Fin N) (j k : Fin d) : ComplexExpr (Input N d) :=
  ⟨.input (.inr (i,j,k,false)),.input (.inr (i,j,k,true))⟩
def hEntry (j k : Fin d) : ComplexExpr (Input N d) :=
  ComplexExpr.sum (fun i => .smul (hCoeff i) (atomEntry i j k))
def kEntry (j k : Fin d) : ComplexExpr (Input N d) :=
  ComplexExpr.sum (fun i => .smul (kCoeff i) (atomEntry i j k))

def centerEntry : FourSpin (Fin d) → FourSpin (Fin d) → ComplexExpr (Input N d)
  | .inl (.inl i), .inl (.inl j) => hEntry i j
  | .inl (.inr i), .inl (.inr j) => .smul (.constant (-1)) (hEntry i j)
  | .inr (.inl i), .inr (.inl j) => kEntry i j
  | .inr (.inr i), .inr (.inr j) => .smul (.constant (-1)) (kEntry i j)
  | _,_ => .zero

def reserveEntry (i : Fin N) : Expr (Input N d) := .input (.inl (i,3))

theorem hEntry_eval (A : Fin N → SDPValue.Mat d) (x₀ : Fin N → ℝ)
    (z : EpochState (Fin N)) (j k : Fin d) :
    (hEntry j k).eval (input A x₀ z) = discrepancy A x₀ z j k := by
  simp only [hEntry,ComplexExpr.eval_sum,ComplexExpr.eval_smul]
  simp [hCoeff,atomEntry,ComplexExpr.eval,Expr.eval,input,discrepancy,
    Matrix.sum_apply,Matrix.smul_apply]

theorem kEntry_eval (A : Fin N → SDPValue.Mat d) (x₀ : Fin N → ℝ)
    (z : EpochState (Fin N)) (j k : Fin d) :
    (kEntry j k).eval (input A x₀ z) = budgetCenter A x₀ z j k := by
  simp only [kEntry,ComplexExpr.eval_sum,ComplexExpr.eval_smul]
  simp [kCoeff,atomEntry,ComplexExpr.eval,Expr.eval,input,budgetCenter,
    Matrix.sum_apply,Matrix.smul_apply,pow_two]

theorem centerEntry_eval (A : Fin N → SDPValue.Mat d) (x₀ : Fin N → ℝ)
    (z : EpochState (Fin N)) (i j : FourSpin (Fin d)) :
    (centerEntry i j).eval (input A x₀ z) =
      augmentedCenter (discrepancy A x₀ z) (budgetCenter A x₀ z) i j := by
  rcases i with (i|i) <;> rcases i with (i|i) <;>
    rcases j with (j|j) <;> rcases j with (j|j) <;>
    simp [centerEntry,augmentedCenter,signedLift,hEntry_eval,kEntry_eval,Expr.eval]

theorem centerEntry_valid (v : Input N d → ℝ) (i j : FourSpin (Fin d)) :
    (centerEntry i j).Valid v := by
  have hh (j k : Fin d) : (hEntry (N:=N) j k).Valid v := by
    apply ComplexExpr.valid_sum
    intro i
    exact ComplexExpr.valid_smul ⟨trivial,trivial⟩ ⟨trivial,trivial⟩
  have hk (j k : Fin d) : (kEntry (N:=N) j k).Valid v := by
    apply ComplexExpr.valid_sum
    intro i
    exact ComplexExpr.valid_smul ⟨⟨⟨trivial,trivial⟩,⟨trivial,trivial⟩⟩,trivial⟩ ⟨trivial,trivial⟩
  rcases i with (i|i) <;> rcases i with (i|i) <;>
    rcases j with (j|j) <;> rcases j with (j|j) <;>
    first | exact ComplexExpr.valid_zero v | exact hh _ _ | exact hk _ _ |
      exact ComplexExpr.valid_smul trivial (hh _ _) |
      exact ComplexExpr.valid_smul trivial (hk _ _)

theorem centerEntry_cost (i j : FourSpin (Fin d)) :
    (centerEntry (N:=N) i j).cost ≤ 24*N+6 := by
  have hh (i j : Fin d) : (hEntry (N:=N) i j).cost ≤ 12*N+2 := by
    simpa only [hEntry,Fintype.card_fin,mul_comm,Nat.reduceAdd] using ComplexExpr.cost_sum_le (fun l : Fin N => .smul (hCoeff l) (atomEntry l i j)) 10
      (fun _ => by norm_num [ComplexExpr.cost_smul,hCoeff,atomEntry,ComplexExpr.cost,ComplexExpr.smul,Expr.cost])
  have hk (i j : Fin d) : (kEntry (N:=N) i j).cost ≤ 24*N+2 := by
    simpa only [kEntry,Fintype.card_fin,mul_comm,Nat.reduceAdd] using ComplexExpr.cost_sum_le (fun l : Fin N => .smul (kCoeff l) (atomEntry l i j)) 22
      (fun _ => by norm_num [ComplexExpr.cost_smul,kCoeff,atomEntry,ComplexExpr.cost,ComplexExpr.smul,Expr.cost])
  rcases i with (i|i) <;> rcases i with (i|i) <;>
    rcases j with (j|j) <;> rcases j with (j|j) <;>
    simp only [centerEntry,ComplexExpr.cost_smul,Expr.cost,ComplexExpr.cost_zero] <;>
    first | omega | nlinarith [hh i j,hk i j]

def center (A : Fin N → SDPValue.Mat d) (x₀ : Fin N → ℝ)
    (z : EpochState (Fin N)) : Counted (SDPValue.Full d) :=
  ⟨fun i j => (centerEntry i j).eval (input A x₀ z),
    (∑ i : FourSpin (Fin d), ∑ j : FourSpin (Fin d), ((centerEntry (N:=N) i j).cost+2))+
      4*N+2*N*d^2+1⟩

theorem center_value (A : Fin N → SDPValue.Mat d) (x₀ : Fin N → ℝ)
    (z : EpochState (Fin N)) :
    (center A x₀ z).value = augmentedCenter (discrepancy A x₀ z) (budgetCenter A x₀ z) := by
  ext i j
  exact centerEntry_eval A x₀ z i j

theorem center_entry_execution (A : Fin N → SDPValue.Mat d) (x₀ : Fin N → ℝ)
    (z : EpochState (Fin N)) (i j : FourSpin (Fin d)) :
    Expr.Executes (input A x₀ z) (centerEntry i j).re
      ((center A x₀ z).value i j).re (centerEntry (N:=N) i j).re.cost ∧
    Expr.Executes (input A x₀ z) (centerEntry i j).im
      ((center A x₀ z).value i j).im (centerEntry (N:=N) i j).im.cost :=
  ComplexExpr.executes _ _ (centerEntry_valid _ i j)

theorem center_cost (A : Fin N → SDPValue.Mat d) (x₀ : Fin N → ℝ)
    (z : EpochState (Fin N)) : (center A x₀ z).cost ≤ 1000*(N+1)*(d+1)^2 := by
  have hi (i : FourSpin (Fin d)) :
      (∑ j : FourSpin (Fin d), ((centerEntry (N:=N) i j).cost+2)) ≤ (4*d)*(24*N+8) := by
    have hh := Finset.sum_le_sum (s := Finset.univ)
      (f := fun j : FourSpin (Fin d) => (centerEntry (N:=N) i j).cost+2)
      (g := fun _ => 24*N+8)
      (fun j _ => Nat.add_le_add_right (centerEntry_cost (N:=N) i j) 2)
    convert hh using 1 <;> simp only [Nat.add_assoc,Nat.reduceAdd,Finset.sum_const,Finset.card_univ,
      Fintype.card_sum,Fintype.card_fin,FourSpin,nsmul_eq_mul] <;> norm_cast <;> ring
  have hh : (∑ i : FourSpin (Fin d), ∑ j : FourSpin (Fin d), ((centerEntry (N:=N) i j).cost+2)) ≤
      (4*d)*(4*d)*(24*N+8) := by
    have hs := Finset.sum_le_sum (s := Finset.univ)
      (f := fun i : FourSpin (Fin d) => ∑ j : FourSpin (Fin d), ((centerEntry (N:=N) i j).cost+2))
      (g := fun _ => (4*d)*(24*N+8)) (fun i _ => hi i)
    convert hs using 1 <;> simp [FourSpin] <;> ring
  dsimp only [center]
  nlinarith [Nat.zero_le (N*d),Nat.zero_le N,Nat.zero_le d,Nat.zero_le (d^2),Nat.zero_le (N*d^2)]

def report (O : SDPValue.Solver) (A B : Fin N → SDPValue.Mat d)
    (k : ℕ) (x₀ : Fin N → ℝ) (θ ν : ℝ) (z : EpochState (Fin N)) : Counted ℝ :=
  let H := center A x₀ z
  let c := fun i => (reserveEntry i).eval (input A x₀ z)
  let out := InputFactors.cachedQuery O B k H.value c θ ν
  ⟨out.value,H.cost+2*N+out.cost+1⟩

theorem report_value (O : SDPValue.Solver) (A B : Fin N → SDPValue.Mat d)
    (k : ℕ) (x₀ : Fin N → ℝ) (θ ν : ℝ) (z : EpochState (Fin N)) :
    (report O A B k x₀ θ ν z).value =
      (InputFactors.cachedQuery O B k
        (augmentedCenter (discrepancy A x₀ z) (budgetCenter A x₀ z)) (reserve z) θ ν).value := by
  simp [report,center_value,reserveEntry,Expr.eval,input]

theorem report_accuracy (O : SDPValue.Solver) (A : Fin N → SDPValue.Mat d)
    (hA : ∀ i,(A i).PosSemidef) (k : ℕ) (x₀ : Fin N → ℝ) (hd : 0 < d) (hk : 1 ≤ k)
    {θ ν : ℝ} (hθ : 0 < θ) (hν : 0 < ν)
    (z : EpochState (Fin N)) (hc : ∀ i,0 ≤ reserve z i) :
    |(report O A (InputFactors.factors A).value k x₀ θ ν z).value-
      epochPotential A ((1:ℝ)/2^k) θ x₀ z| ≤ ν := by
  rw [report_value]
  exact InputFactors.cachedQuery_accuracy O A hA k _ hd hk hc hθ hν

theorem report_cost (O : SDPValue.Solver) (A B : Fin N → SDPValue.Mat d)
    (k : ℕ) (x₀ : Fin N → ℝ) (θ : ℝ) {ν : ℝ} (hν : 0 < ν) (z : EpochState (Fin N)) :
    (report O A B k x₀ θ ν z).cost ≤
      O.coefficient*(SDPValue.dataSize N d k+⌈ν⁻¹⌉₊+1)^O.degree +
        1004*(N+1)*(d+1)^2 := by
  have hh := center_cost A x₀ z
  have hq := InputFactors.cachedQuery_cost O B k (center A x₀ z).value
    (fun i => (reserveEntry i).eval (input A x₀ z)) θ hν
  dsimp only [report]
  have hN : N+1 ≤ (N+1)*(d+1)^2 := Nat.le_mul_of_pos_right (N+1) (by positivity)
  nlinarith

end HigherRankKSRuntime.RuntimeStateReport
