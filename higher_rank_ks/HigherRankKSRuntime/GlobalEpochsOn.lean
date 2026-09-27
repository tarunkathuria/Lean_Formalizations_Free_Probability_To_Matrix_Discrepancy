import HigherRankKSRuntime.GlobalEpochs

/-! Finite composition of executed reserve epochs on the original owner cube.
The local callback contracts below are internal interfaces: the public runtime
endpoint instantiates them with the finite controller, not a compact minimizer. -/

open Matrix MatrixSpencer Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 800000
namespace HigherRankKSRuntime.GlobalEpochs
open AugmentedHigherRankKS
open MatrixSpencer.RealRAM.JacobiIteration (Counted)

variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]

/-- The finite global loop tests the live PSD mass, invokes the counted epoch,
and rounds the remaining original coefficients when their mass is small.
At zero fuel it rounds; the theorem below proves this cannot be premature. -/
def runOn (A : ι → Matrix n n ℂ) (δ : ℝ) (P : CubePoint ι → Prop)
    (epoch : (x : CubePoint ι) → P x → Counted (CubePoint ι))
    (closed : ∀ x hx,P (epoch x hx).value) (testWork roundWork : ℕ) :
    ℕ → (x : CubePoint ι) → P x → Counted (CubePoint ι)
  | 0, x, _ => ⟨roundCube x, roundWork⟩
  | fuel + 1, x, hx =>
      if ‖cubeMass A x‖ ≤ δ ^ 2 then ⟨roundCube x, testWork + roundWork⟩
      else
        let y := epoch x hx
        let z := runOn A δ P epoch closed testWork roundWork fuel y.value (closed x hx)
        ⟨z.value, testWork + y.cost + z.cost⟩

/-- Every branch of the explicit global loop has the desired discrepancy
budget; its number of epoch calls is at most the original owner count. -/
theorem runOn_spec [Nonempty n] (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) {δ : ℝ} (hδ : 0 ≤ δ)
    (P : CubePoint ι → Prop)
    (epoch : (x : CubePoint ι) → P x → Counted (CubePoint ι))
    (closed : ∀ x hx,P (epoch x hx).value) (testWork roundWork Q : ℕ)
    (hepoch : ∀ (x : CubePoint ι) (hx : P x), δ ^ 2 < ‖cubeMass A x‖ →
      (∀ i, i ∉ cubeLive x → (epoch x hx).value.val i = x.val i) ∧
      ‖cubeMass A (epoch x hx).value‖ ≤ ‖cubeMass A x‖ / 2 ∧
      ‖cubeCenter A (epoch x hx).value - cubeCenter A x‖ ≤
        δ * Real.sqrt ‖cubeMass A x‖ ∧ (epoch x hx).cost ≤ Q)
    (fuel : ℕ) (x : CubePoint ι) (hx : P x) (hfuel : (cubeLive x).card ≤ fuel) :
    cubeTerminal (runOn A δ P epoch closed testWork roundWork fuel x hx).value ∧
      ‖cubeCenter A (runOn A δ P epoch closed testWork roundWork fuel x hx).value - cubeCenter A x‖ ≤
        4 * δ * Real.sqrt ‖cubeMass A x‖ ∧
      (runOn A δ P epoch closed testWork roundWork fuel x hx).cost ≤
        fuel * (Q + testWork) + roundWork := by
  induction fuel generalizing x with
  | zero =>
      have hm : cubeMass A x = 0 := cubeMass_eq_zero_of_card_zero A x (by omega)
      refine ⟨roundCube_terminal x, ?_, by simp [runOn]⟩
      simpa [runOn, hm] using roundCube_norm_le A hA x
  | succ fuel ih =>
      by_cases hs : ‖cubeMass A x‖ ≤ δ ^ 2
      · simp only [runOn, if_pos hs]
        refine ⟨roundCube_terminal x, ?_, by nlinarith⟩
        exact (roundCube_norm_le A hA x).trans
          (terminal_rounding_budget hδ (norm_nonneg _) hs)
      · have hlarge := lt_of_not_ge hs
        obtain ⟨hfrozen, hmass, hinc, hcost⟩ := hepoch x hx hlarge
        have hmasspos : 0 < ‖cubeMass A x‖ := lt_of_le_of_lt (sq_nonneg δ) hlarge
        have hcard := cubeLive_card_lt_of_mass_lt A x (epoch x hx).value hfrozen
          (show ‖cubeMass A (epoch x hx).value‖ < ‖cubeMass A x‖ by linarith)
        have hnext : (cubeLive (epoch x hx).value).card ≤ fuel := by omega
        obtain ⟨hterm, hbound, hwork⟩ := ih (epoch x hx).value (closed x hx) hnext
        simp only [runOn, if_neg hs]
        refine ⟨hterm, ?_, ?_⟩
        · have hhalf := sqrt_half_budget (norm_nonneg (cubeMass A x))
            (norm_nonneg (cubeMass A (epoch x hx).value)) hmass
          have hmul := mul_le_mul_of_nonneg_left hhalf hδ
          calc
            ‖cubeCenter A (runOn A δ P epoch closed testWork roundWork fuel (epoch x hx).value (closed x hx)).value -
                cubeCenter A x‖ ≤
              ‖cubeCenter A (runOn A δ P epoch closed testWork roundWork fuel (epoch x hx).value (closed x hx)).value -
                cubeCenter A (epoch x hx).value‖ +
              ‖cubeCenter A (epoch x hx).value - cubeCenter A x‖ := by
                simpa only [sub_add_sub_cancel] using norm_add_le
                  (cubeCenter A (runOn A δ P epoch closed testWork roundWork fuel (epoch x hx).value (closed x hx)).value -
                    cubeCenter A (epoch x hx).value)
                  (cubeCenter A (epoch x hx).value - cubeCenter A x)
            _ ≤ 4 * δ * Real.sqrt ‖cubeMass A (epoch x hx).value‖ +
                δ * Real.sqrt ‖cubeMass A x‖ := add_le_add hbound hinc
            _ ≤ 4 * δ * Real.sqrt ‖cubeMass A x‖ := by nlinarith
        · nlinarith


end HigherRankKSRuntime.GlobalEpochs
