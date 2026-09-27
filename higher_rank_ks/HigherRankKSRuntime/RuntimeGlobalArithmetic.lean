import HigherRankKSRuntime.RuntimeCubeArithmetic
import HigherRankKSRuntime.GlobalEpochsOn

/-! The global loop materializes its live-mass matrix and obtains the stopping
norm by the permitted EVD. Its output agrees with the mathematical epoch loop,
while its cost records these executed tests and coordinate rounding programs. -/
noncomputable section
open Matrix MatrixSpencer Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace HigherRankKSRuntime.GlobalEpochs
open AugmentedHigherRankKS
open RealRAM.JacobiIteration (Counted)
variable {N d : ℕ}

def massWork (N d : ℕ) : ℕ := 5600*(d+1)^3+100*(N+1)*(d+1)^2+4
def roundingWork (N : ℕ) : ℕ := 13*N+1

def runArithmeticOn (A : Fin N → SDPValue.Mat d) (δ : ℝ) (P : CubePoint (Fin N) → Prop)
    (epoch : (x : CubePoint (Fin N)) → P x → Counted (CubePoint (Fin N)))
    (closed : ∀ x hx,P (epoch x hx).value) :
    ℕ → (x : CubePoint (Fin N)) → P x → Counted (CubePoint (Fin N))
  | 0, x, _ => RuntimeCubeArithmetic.round x
  | fuel+1, x, hx =>
      let m := RuntimeCubeArithmetic.massNorm A x
      if m.value ≤ δ^2 then
        let y := RuntimeCubeArithmetic.round x
        ⟨y.value,m.cost+3+y.cost⟩
      else
        let y := epoch x hx
        let z := runArithmeticOn A δ P epoch closed fuel y.value (closed x hx)
        ⟨z.value,m.cost+3+y.cost+z.cost⟩

theorem runArithmeticOn_value (A : Fin N → SDPValue.Mat d)
    (hA : ∀ i,(A i).IsHermitian) (δ : ℝ) (P : CubePoint (Fin N) → Prop)
    (epoch : (x : CubePoint (Fin N)) → P x → Counted (CubePoint (Fin N)))
    (closed : ∀ x hx,P (epoch x hx).value) (testWork roundWork : ℕ)
    (fuel : ℕ) (x : CubePoint (Fin N)) (hx : P x) :
    (runArithmeticOn A δ P epoch closed fuel x hx).value =
      (runOn A δ P epoch closed testWork roundWork fuel x hx).value := by
  induction fuel generalizing x with
  | zero => exact RuntimeCubeArithmetic.round_value x
  | succ fuel ih =>
    simp only [runArithmeticOn,runOn,RuntimeCubeArithmetic.massNorm_value A hA]
    split_ifs
    · exact RuntimeCubeArithmetic.round_value x
    · exact ih _ _

theorem runArithmeticOn_cost_le_semantic (A : Fin N → SDPValue.Mat d)
    (hA : ∀ i,(A i).IsHermitian) (δ : ℝ) (P : CubePoint (Fin N) → Prop)
    (epoch : (x : CubePoint (Fin N)) → P x → Counted (CubePoint (Fin N)))
    (closed : ∀ x hx,P (epoch x hx).value) (testWork roundWork : ℕ)
    (htest : ∀ x,(RuntimeCubeArithmetic.massNorm A x).cost+3≤testWork)
    (hround : ∀ x : CubePoint (Fin N),(RuntimeCubeArithmetic.round x).cost≤roundWork)
    (fuel : ℕ) (x : CubePoint (Fin N)) (hx : P x) :
    (runArithmeticOn A δ P epoch closed fuel x hx).cost ≤
      (runOn A δ P epoch closed testWork roundWork fuel x hx).cost := by
  induction fuel generalizing x with
  | zero => exact hround x
  | succ fuel ih =>
    simp only [runArithmeticOn,runOn,RuntimeCubeArithmetic.massNorm_value A hA]
    split_ifs
    · exact Nat.add_le_add (htest x) (hround x)
    · exact Nat.add_le_add (Nat.add_le_add_right (htest x) _) (ih _ _)


theorem runArithmeticOn_cost (A : Fin N → SDPValue.Mat d)
    (hA : ∀ i,(A i).IsHermitian) (δ : ℝ) (P : CubePoint (Fin N) → Prop)
    (epoch : (x : CubePoint (Fin N)) → P x → Counted (CubePoint (Fin N)))
    (closed : ∀ x hx,P (epoch x hx).value) (Q : ℕ)
    (hepoch : ∀ x hx,δ^2 < ‖cubeMass A x‖ → (epoch x hx).cost≤Q)
    (fuel : ℕ) (x : CubePoint (Fin N)) (hx : P x) :
    (runArithmeticOn A δ P epoch closed fuel x hx).cost ≤
      fuel*(Q+massWork N d)+roundingWork N := by
  induction fuel generalizing x with
  | zero => simpa only [runArithmeticOn,Nat.zero_mul,Nat.zero_add,roundingWork]
      using RuntimeCubeArithmetic.round_cost x
  | succ fuel ih =>
    have hm := RuntimeCubeArithmetic.massNorm_cost A x
    have hr := RuntimeCubeArithmetic.round_cost x
    simp only [runArithmeticOn,RuntimeCubeArithmetic.massNorm_value A hA]
    by_cases hs : ‖cubeMass A x‖≤δ^2
    · rw [if_pos hs]
      dsimp only [massWork,roundingWork]
      nlinarith
    · rw [if_neg hs]
      have hy := hepoch x hx (lt_of_not_ge hs)
      have hz := ih (epoch x hx).value (closed x hx)
      dsimp only [massWork,roundingWork] at *
      nlinarith

end HigherRankKSRuntime.GlobalEpochs
