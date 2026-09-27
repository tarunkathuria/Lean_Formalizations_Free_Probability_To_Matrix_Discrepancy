import HigherRankKSRuntime.GlobalEpochState
import HigherRankKSRuntime.InvariantControllerLoop

/-! Conversion of the counted controller output to the cube transition
used by the global loop. Every analytic interface here is internal; the
source-specific controller discharges it at the endpoint. -/
open Matrix MatrixSpencer Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace HigherRankKSRuntime.GlobalEpochs
open AugmentedHigherRankKS
open MatrixSpencer.RealRAM.JacobiIteration (Counted)
variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]

def executedEpoch (a step h : ℝ) (ha : 0 < a)
    (next : EpochState ι → Counted (ControllerLoop.Event ι))
    (sound : ∀ z ∈ epochDomain a 4,(next z).value.Valid a 4 step h z)
    (fuel : ℕ) (x : CubePoint ι) : Counted (CubePoint ι) :=
  let z := resetState a 4 x
  let r := ControllerLoop.run a step h next fuel z
  let hf := (ControllerLoop.run_spec ha next sound fuel (resetState_mem ha.le (by norm_num) x)).1
  ⟨stateCube r.state hf,r.work+10*Fintype.card ι+1⟩

theorem epoch_error_absorption {α b err : ℝ} (hα : 0 ≤ α)
    (hlarge : (5*Real.sqrt α)^2 < b) (herr : err ≤ α) :
    4*Real.sqrt (α*b)+err ≤ 5*Real.sqrt α*Real.sqrt b := by
  have hb : 0 ≤ b := le_trans (sq_nonneg _) hlarge.le
  rw [Real.sqrt_mul hα]
  have hsa := Real.sqrt_nonneg α
  have hsb := Real.sqrt_nonneg b
  have ha2 := Real.sq_sqrt hα
  have hb2 := Real.sq_sqrt hb
  have hs : Real.sqrt α ≤ Real.sqrt b := by nlinarith
  have hh := mul_le_mul_of_nonneg_left hs hsa
  nlinarith

theorem executedEpoch_spec [Nonempty n]
    (A : ι → Matrix n n ℂ) (hA : ∀ i,(A i).PosSemidef)
    (a step h : ℝ) (ha : 0 < a) (hstep : 0 < step) (hh : h ≠ 0)
    (next : EpochState ι → Counted (ControllerLoop.Event ι))
    (sound : ∀ z ∈ epochDomain a 4,(next z).value.Valid a 4 step h z)
    (fuel : ℕ) (hfuel : (Fintype.card ι:ℝ)/h^2+
      (Fintype.card ι:ℝ)*(a*4)/step+Fintype.card ι < fuel)
    (x : CubePoint ι) {β θ δ κ : ℝ}
    (hβ : 0 ≤ β) (hβ1 : β ≤ 1) (hθ : 0 ≤ θ) (hδ : 0 ≤ δ) (hκ : 0 ≤ κ)
    (hlarge : δ^2 < ‖cubeMass A x‖)
    (hsafe : ∀ z ∈ epochDomain a 4,
      epochPotential A β θ x.val ((next z).value.apply a step h z) ≤
      epochPotential A β θ x.val z+((next z).value.cleanups:ℝ)*κ)
    (hinit : epochPotential A β θ x.val (resetState a 4 x)+Fintype.card ι*κ ≤
      δ*Real.sqrt ‖cubeMass A x‖)
    (hfrozen : ∀ i,i ∉ cubeLive x →
      position (ControllerLoop.run a step h next fuel (resetState a 4 x)).state i = x.val i)
    {Q : ℕ} (hwork : ∀ z ∈ epochDomain a 4,(next z).cost ≤ Q) :
    let out := executedEpoch a step h ha next sound fuel x
    (∀ i,i ∉ cubeLive x → out.value.val i = x.val i) ∧
      ‖cubeMass A out.value‖ ≤ ‖cubeMass A x‖/2 ∧
      ‖cubeCenter A out.value-cubeCenter A x‖ ≤ δ*Real.sqrt ‖cubeMass A x‖ ∧
      out.cost ≤ fuel*Q+10*Fintype.card ι+1 := by
  have hz := resetState_mem ha.le (by norm_num : (0:ℝ)≤4) x
  have hspec := ControllerLoop.run_spec ha next sound fuel hz
  have ht := ControllerLoop.run_terminal ha hstep hh next sound fuel hfuel hz
  have hp := ControllerLoop.run_potential_card_bound ha hstep.le next sound
    (epochPotential A β θ x.val) hκ hsafe fuel hz
  have hsize := (epochCenterSize_le_potential A hA hβ hβ1 hθ x.val hspec.1).trans
    (hp.trans hinit)
  have hc := terminal_cube_contract A hA x ha.ne' hδ hlarge hspec.1 ht hsize
  have hw := ControllerLoop.run_work_le ha next sound hwork fuel hz
  exact ⟨hfrozen,hc.1,hc.2,Nat.add_le_add_right (Nat.add_le_add_right hw _) _⟩

def executedEpochOn (a step h : ℝ) (ha : 0 < a)
    (P : EpochState ι → Prop)
    (next : EpochState ι → Counted (ControllerLoop.Event ι))
    (sound : ∀ z ∈ epochDomain a 4,P z → (next z).value.Valid a 4 step h z)
    (closed : ∀ z ∈ epochDomain a 4,P z → P ((next z).value.apply a step h z))
    (fuel : ℕ) (x : CubePoint ι) (hx : P (resetState a 4 x)) : Counted (CubePoint ι) :=
  let z := resetState a 4 x
  let r := ControllerLoop.run a step h next fuel z
  let hf := (ControllerLoop.run_spec_on ha P next sound closed fuel
    (resetState_mem ha.le (by norm_num) x) hx).2.1
  ⟨stateCube r.state hf,r.work+10*Fintype.card ι+1⟩


theorem executedEpochOn_spec [Nonempty n]
    (A : ι → Matrix n n ℂ) (hA : ∀ i,(A i).PosSemidef)
    (a step h : ℝ) (ha : 0 < a) (hstep : 0 < step) (hh : h ≠ 0)
    (P : EpochState ι → Prop)
    (next : EpochState ι → Counted (ControllerLoop.Event ι))
    (sound : ∀ z ∈ epochDomain a 4,P z → (next z).value.Valid a 4 step h z)
    (closed : ∀ z ∈ epochDomain a 4,P z → P ((next z).value.apply a step h z))
    (fuel : ℕ) (hfuel : (Fintype.card ι:ℝ)/h^2+
      (Fintype.card ι:ℝ)*(a*4)/step+Fintype.card ι < fuel)
    (x : CubePoint ι) (hx : P (resetState a 4 x)) {β θ δ κ : ℝ}
    (hβ : 0 ≤ β) (hβ1 : β ≤ 1) (hθ : 0 ≤ θ) (hδ : 0 ≤ δ) (hκ : 0 ≤ κ)
    (hlarge : δ^2 < ‖cubeMass A x‖)
    (hsafe : ∀ z ∈ epochDomain a 4,P z →
      epochPotential A β θ x.val ((next z).value.apply a step h z) ≤
      epochPotential A β θ x.val z+((next z).value.cleanups:ℝ)*κ)
    (hinit : epochPotential A β θ x.val (resetState a 4 x)+Fintype.card ι*κ ≤
      δ*Real.sqrt ‖cubeMass A x‖)
    (hfrozen : ∀ i,i ∉ cubeLive x →
      position (ControllerLoop.run a step h next fuel (resetState a 4 x)).state i = x.val i)
    {Q : ℕ} (hwork : ∀ z ∈ epochDomain a 4,P z → (next z).cost ≤ Q) :
    let out := executedEpochOn a step h ha P next sound closed fuel x hx
    (∀ i,i ∉ cubeLive x → out.value.val i = x.val i) ∧
      ‖cubeMass A out.value‖ ≤ ‖cubeMass A x‖/2 ∧
      ‖cubeCenter A out.value-cubeCenter A x‖ ≤ δ*Real.sqrt ‖cubeMass A x‖ ∧
      out.cost ≤ fuel*Q+10*Fintype.card ι+1 := by
  have hz := resetState_mem ha.le (by norm_num : (0:ℝ)≤4) x
  have hspec := ControllerLoop.run_spec_on ha P next sound closed fuel hz hx
  have ht := ControllerLoop.run_terminal_on ha hstep hh P next sound closed fuel hfuel hz hx
  have hp := ControllerLoop.run_potential_card_bound_on ha hstep.le P next sound closed
    (epochPotential A β θ x.val) hκ hsafe fuel hz hx
  have hsize := (epochCenterSize_le_potential A hA hβ hβ1 hθ x.val hspec.2.1).trans
    (hp.trans hinit)
  have hc := terminal_cube_contract A hA x ha.ne' hδ hlarge hspec.2.1 ht hsize
  have hw := ControllerLoop.run_work_le_on ha P next sound closed hwork fuel hz hx
  exact ⟨hfrozen,hc.1,hc.2,Nat.add_le_add_right (Nat.add_le_add_right hw _) _⟩

end HigherRankKSRuntime.GlobalEpochs
