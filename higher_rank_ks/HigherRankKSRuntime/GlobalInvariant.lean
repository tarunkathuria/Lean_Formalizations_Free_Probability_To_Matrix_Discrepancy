import HigherRankKSRuntime.RuntimeInvariant
import HigherRankKSRuntime.GlobalEpochsOn
import HigherRankKSRuntime.GlobalNumericBounds
import HigherRankKSRuntime.RuntimeInputNormalization

open Matrix MatrixSpencer Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace HigherRankKSRuntime.GlobalEpochs
open AugmentedHigherRankKS
open MatrixSpencer.RealRAM.JacobiIteration (Counted)
variable {N d : ℕ}

def LargeCube (A : Fin N → SDPValue.Mat d) (η : ℝ) (x : CubePoint (Fin N)) : Prop :=
  ∀ i,i ∈ cubeLive x → η ≤ ‖A i‖

theorem largeCube_discard (A : Fin N → SDPValue.Mat d)
    (hA : ∀ i,(A i).PosSemidef) (η : ℝ) :
    LargeCube A η (RuntimeInputNormalization.discardCube A η) := by
  intro i hi
  exact (RuntimeInputNormalization.discard_live_large A (fun j => (hA j).isHermitian)
    η i ((mem_cubeLive _ _).mp hi)).le

theorem largeCube_reset (A : Fin N → SDPValue.Mat d) (η a R : ℝ)
    (x : CubePoint (Fin N)) (hx : LargeCube A η x) :
    NextEvent.LargeOwners A η (resetState a R x) := by
  intro i hi
  apply hx i
  apply (mem_cubeLive _ _).mpr
  by_contra hn
  simp [resetState,reserve,hn] at hi

theorem largeCube_frozen (A : Fin N → SDPValue.Mat d) (η : ℝ)
    {x y : CubePoint (Fin N)} (hx : LargeCube A η x)
    (hf : ∀ i,i ∉ cubeLive x → y.val i = x.val i) : LargeCube A η y := by
  intro i hi
  apply hx i
  by_contra hn
  have hx1 := cube_not_live_abs_eq hn
  have hy1 := (mem_cubeLive y i).mp hi
  rw [hf i hn,hx1] at hy1
  exact lt_irrefl _ hy1

theorem executedEpochOn_frozen (a step h : ℝ) (ha : 0 < a)
    (P : EpochState (Fin N) → Prop)
    (next : EpochState (Fin N) → Counted (ControllerLoop.Event (Fin N)))
    (sound : ∀ z ∈ epochDomain a 4,P z → (next z).value.Valid a 4 step h z)
    (closed : ∀ z ∈ epochDomain a 4,P z → P ((next z).value.apply a step h z))
    (hf : ∀ z ∈ epochDomain a 4,
      ControllerLoop.PreservesFrozen z ((next z).value.apply a step h z))
    (fuel : ℕ) (x : CubePoint (Fin N)) (hx : P (resetState a 4 x)) :
    ∀ i,i ∉ cubeLive x →
      (executedEpochOn a step h ha P next sound closed fuel x hx).value.val i = x.val i := by
  have hh := ControllerLoop.run_preservesFrozen_on ha P next sound closed hf fuel
    (resetState_mem ha.le (by norm_num : (0:ℝ)≤4) x) hx
  intro i hi
  exact hh i (cube_not_live_abs_eq hi)

end HigherRankKSRuntime.GlobalEpochs
