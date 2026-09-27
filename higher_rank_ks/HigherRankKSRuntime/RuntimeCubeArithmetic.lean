import HigherRankKSRuntime.RuntimeInputNormalization
import HigherRankKSRuntime.RuntimeStateReport
import MatrixSpencer.RealRAMProgram

/-! The global stopping test and final rounding use counted scalar programs,
entrywise matrix assembly, and the already permitted exact EVD. -/
noncomputable section
open Matrix MatrixSpencer Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace HigherRankKSRuntime.RuntimeCubeArithmetic
open AugmentedHigherRankKS RealRAM
open RealRAM.JacobiIteration (Counted)
variable {N d : ℕ}

def scalarInput (x : ℝ) : Fin 2 → ℝ := ![x,0]
def liveProgram : Program (Fin 2) :=
  .branchLE (.constant 1) (.mul (.input 0) (.input 0))
    (.assign 1 (.constant 0)) (.assign 1 (.constant 1))
def roundProgram : Program (Fin 2) :=
  .branchLE (.constant 0) (.input 0)
    (.assign 1 (.constant 1)) (.assign 1 (.constant (-1)))

theorem liveProgram_safe (v : Fin 2 → ℝ) : liveProgram.Safe v := by
  refine ⟨trivial,⟨trivial,trivial⟩,?_⟩
  split_ifs <;> trivial

theorem roundProgram_safe (v : Fin 2 → ℝ) : roundProgram.Safe v := by
  refine ⟨trivial,trivial,?_⟩
  split_ifs <;> trivial

theorem liveProgram_value (x : ℝ) :
    liveProgram.run (scalarInput x) 1 = if |x|<1 then 1 else 0 := by
  simp only [liveProgram,Program.run,Expr.eval,scalarInput,Matrix.cons_val_zero]
  have he : 1≤x*x ↔ ¬|x|<1 := by
    simpa only [pow_two,not_lt] using not_congr (sq_lt_one_iff_abs_lt_one x)
  by_cases hh : |x|<1
  · simp [he,hh]
  · simp [he,hh]

theorem roundProgram_value (x : ℝ) :
    roundProgram.run (scalarInput x) 1 = if 0≤x then 1 else -1 := by
  simp only [roundProgram,Program.run,Expr.eval,scalarInput,Matrix.cons_val_zero]
  norm_num only at *
  split_ifs <;> simp_all

theorem liveProgram_bound : liveProgram.bound≤12 := by decide
theorem roundProgram_bound : roundProgram.bound≤10 := by decide

def mask (x : CubePoint (Fin N)) : Counted (Fin N → ℝ) :=
  ⟨fun i => liveProgram.run (scalarInput (x.val i)) 1,
    (∑ i,liveProgram.cost (scalarInput (x.val i)))+3*N+1⟩

theorem mask_value (x : CubePoint (Fin N)) (i : Fin N) :
    (mask x).value i = if |x.val i|<1 then 1 else 0 := liveProgram_value _

theorem mask_execution (x : CubePoint (Fin N)) (i : Fin N) :
    ∃ out cost, Program.Executes liveProgram (scalarInput (x.val i)) out cost ∧
      out 1=(mask x).value i ∧ cost≤12 :=
  ⟨_,_,Program.executes_of_safe _ _ (liveProgram_safe _),rfl,
    (Program.cost_le_bound _ _).trans liveProgram_bound⟩

theorem mask_cost (x : CubePoint (Fin N)) : (mask x).cost ≤ 15*N+1 := by
  have hh := Finset.sum_le_sum (s:=Finset.univ) (fun i _ =>
    (Program.cost_le_bound liveProgram (scalarInput (x.val i))).trans liveProgram_bound)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] at hh
  dsimp only [mask]
  omega

abbrev Input (N d : ℕ) := Fin N ⊕ (Fin N × Fin d × Fin d × Bool)
def input (A : Fin N → SDPValue.Mat d) (x : CubePoint (Fin N)) : Input N d → ℝ
  | .inl i => (mask x).value i
  | .inr (i,j,k,b) => if b then (A i j k).im else (A i j k).re

def entry (j k : Fin d) : ComplexExpr (Input N d) :=
  .sum (fun i => .smul (.input (.inl i))
    ⟨.input (.inr (i,j,k,false)),.input (.inr (i,j,k,true))⟩)

theorem entry_eval (A : Fin N → SDPValue.Mat d) (x : CubePoint (Fin N)) (j k : Fin d) :
    (entry j k).eval (input A x) = cubeMass A x j k := by
  rw [cubeMass_eq_ite]
  simp only [entry,ComplexExpr.eval_sum,ComplexExpr.eval_smul,Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp only [ComplexExpr.eval,Expr.eval,input,mask_value,Bool.false_eq_true,ite_false,ite_true]
  split_ifs <;> simp

theorem entry_valid (v : Input N d → ℝ) (j k : Fin d) : (entry j k).Valid v := by
  apply ComplexExpr.valid_sum
  intro i
  exact ComplexExpr.valid_smul trivial ⟨trivial,trivial⟩

theorem entry_cost (j k : Fin d) : (entry (N:=N) j k).cost ≤ 8*N+2 := by
  simpa only [entry,Fintype.card_fin,mul_comm,Nat.reduceAdd] using
    ComplexExpr.cost_sum_le
      (fun i : Fin N => (.smul (.input (.inl i))
        ⟨.input (.inr (i,j,k,false)),.input (.inr (i,j,k,true))⟩ : ComplexExpr (Input N d))) 6
      (fun i => by norm_num [ComplexExpr.smul,ComplexExpr.cost,Expr.cost])

def mass (A : Fin N → SDPValue.Mat d) (x : CubePoint (Fin N)) : Counted (SDPValue.Mat d) :=
  ⟨fun i j => (entry i j).eval (input A x),
    (mask x).cost+(∑ i : Fin d,∑ j : Fin d,((entry (N:=N) i j).cost+2))+2*N*d^2+1⟩

theorem mass_value (A : Fin N → SDPValue.Mat d) (x : CubePoint (Fin N)) :
    (mass A x).value=cubeMass A x := by ext i j; exact entry_eval A x i j

theorem mass_entry_execution (A : Fin N → SDPValue.Mat d) (x : CubePoint (Fin N)) (i j : Fin d) :
    Expr.Executes (input A x) (entry i j).re ((mass A x).value i j).re (entry (N:=N) i j).re.cost ∧
    Expr.Executes (input A x) (entry i j).im ((mass A x).value i j).im (entry (N:=N) i j).im.cost :=
  ComplexExpr.executes _ _ (entry_valid _ _ _)

theorem mass_cost (A : Fin N → SDPValue.Mat d) (x : CubePoint (Fin N)) :
    (mass A x).cost ≤ 100*(N+1)*(d+1)^2 := by
  have hm := mask_cost x
  have hs := Finset.sum_le_sum (s:=Finset.univ) (fun (i : Fin d) _ =>
    Finset.sum_le_sum (s:=Finset.univ) (fun (j : Fin d) _ => Nat.add_le_add_right (entry_cost (N:=N) i j) 2))
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hs
  dsimp only [mass]
  nlinarith [Nat.zero_le (N*d),Nat.zero_le N,Nat.zero_le d,Nat.zero_le (d^2),Nat.zero_le (N*d^2)]

def massNorm (A : Fin N → SDPValue.Mat d) (x : CubePoint (Fin N)) : Counted ℝ :=
  let M := mass A x
  let v := RuntimeInputNormalization.atomNorm M.value
  ⟨v.value,M.cost+v.cost+1⟩

theorem massNorm_value (A : Fin N → SDPValue.Mat d) (hA : ∀ i,(A i).IsHermitian)
    (x : CubePoint (Fin N)) : (massNorm A x).value = ‖cubeMass A x‖ := by
  have hmass : (mass A x).value.IsHermitian := by
    rw [mass_value]
    unfold cubeMass
    change (∑ i ∈ cubeLive x, A i)ᴴ = _
    simp only [Matrix.conjTranspose_sum,(hA _).eq]
  change (RuntimeInputNormalization.atomNorm (mass A x).value).value = _
  rw [RuntimeInputNormalization.atomNorm_value _ hmass,mass_value]

theorem massNorm_cost (A : Fin N → SDPValue.Mat d) (x : CubePoint (Fin N)) :
    (massNorm A x).cost ≤ 5600*(d+1)^3+100*(N+1)*(d+1)^2+1 := by
  have hm := mass_cost A x
  have he := RuntimeInputNormalization.atomNorm_cost (mass A x).value
  dsimp only [massNorm]
  omega

def round (x : CubePoint (Fin N)) : Counted (CubePoint (Fin N)) :=
  let out : Fin N → ℝ := fun i => roundProgram.run (scalarInput (x.val i)) 1
  ⟨⟨out,by intro i; simp only [out,roundProgram_value]; split_ifs <;> norm_num⟩,
    (∑ i,roundProgram.cost (scalarInput (x.val i)))+3*N+1⟩

theorem round_value (x : CubePoint (Fin N)) : (round x).value=roundCube x := by
  apply Subtype.ext
  funext i
  exact roundProgram_value _

theorem round_execution (x : CubePoint (Fin N)) (i : Fin N) :
    ∃ out cost, Program.Executes roundProgram (scalarInput (x.val i)) out cost ∧
      out 1=(round x).value.val i ∧ cost≤10 :=
  ⟨_,_,Program.executes_of_safe _ _ (roundProgram_safe _),rfl,
    (Program.cost_le_bound _ _).trans roundProgram_bound⟩

theorem round_cost (x : CubePoint (Fin N)) : (round x).cost≤13*N+1 := by
  have hh := Finset.sum_le_sum (s:=Finset.univ) (fun i _ =>
    (Program.cost_le_bound roundProgram (scalarInput (x.val i))).trans roundProgram_bound)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] at hh
  dsimp only [round]
  omega

end HigherRankKSRuntime.RuntimeCubeArithmetic
