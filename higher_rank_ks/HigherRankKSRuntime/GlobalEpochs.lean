import AugmentedHigherRankKS.FaceAssembly
import HigherRankKSRuntime.ControllerLoop

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
def run (A : ι → Matrix n n ℂ) (δ : ℝ)
    (epoch : CubePoint ι → Counted (CubePoint ι)) (testWork roundWork : ℕ) :
    ℕ → CubePoint ι → Counted (CubePoint ι)
  | 0, x => ⟨roundCube x, roundWork⟩
  | fuel + 1, x =>
      if ‖cubeMass A x‖ ≤ δ ^ 2 then ⟨roundCube x, testWork + roundWork⟩
      else
        let y := epoch x
        let z := run A δ epoch testWork roundWork fuel y.value
        ⟨z.value, testWork + y.cost + z.cost⟩

/-- A rank-zero cube has no remaining PSD mass. -/
theorem cubeMass_eq_zero_of_card_zero (A : ι → Matrix n n ℂ) (x : CubePoint ι)
    (hx : (cubeLive x).card = 0) : cubeMass A x = 0 := by
  have he : cubeLive x = ∅ := Finset.card_eq_zero.mp hx
  simp [cubeMass, he]

/-- Every branch of the explicit global loop has the desired discrepancy
budget; its number of epoch calls is at most the original owner count. -/
theorem run_spec [Nonempty n] (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) {δ : ℝ} (hδ : 0 ≤ δ)
    (epoch : CubePoint ι → Counted (CubePoint ι)) (testWork roundWork Q : ℕ)
    (hepoch : ∀ x : CubePoint ι, δ ^ 2 < ‖cubeMass A x‖ →
      (∀ i, i ∉ cubeLive x → (epoch x).value.val i = x.val i) ∧
      ‖cubeMass A (epoch x).value‖ ≤ ‖cubeMass A x‖ / 2 ∧
      ‖cubeCenter A (epoch x).value - cubeCenter A x‖ ≤
        δ * Real.sqrt ‖cubeMass A x‖ ∧ (epoch x).cost ≤ Q)
    (fuel : ℕ) (x : CubePoint ι) (hfuel : (cubeLive x).card ≤ fuel) :
    cubeTerminal (run A δ epoch testWork roundWork fuel x).value ∧
      ‖cubeCenter A (run A δ epoch testWork roundWork fuel x).value - cubeCenter A x‖ ≤
        4 * δ * Real.sqrt ‖cubeMass A x‖ ∧
      (run A δ epoch testWork roundWork fuel x).cost ≤
        fuel * (Q + testWork) + roundWork := by
  induction fuel generalizing x with
  | zero =>
      have hm : cubeMass A x = 0 := cubeMass_eq_zero_of_card_zero A x (by omega)
      refine ⟨roundCube_terminal x, ?_, by simp [run]⟩
      simpa [run, hm] using roundCube_norm_le A hA x
  | succ fuel ih =>
      by_cases hs : ‖cubeMass A x‖ ≤ δ ^ 2
      · simp only [run, if_pos hs]
        refine ⟨roundCube_terminal x, ?_, by nlinarith⟩
        exact (roundCube_norm_le A hA x).trans
          (terminal_rounding_budget hδ (norm_nonneg _) hs)
      · have hlarge := lt_of_not_ge hs
        obtain ⟨hfrozen, hmass, hinc, hcost⟩ := hepoch x hlarge
        have hmasspos : 0 < ‖cubeMass A x‖ := lt_of_le_of_lt (sq_nonneg δ) hlarge
        have hcard := cubeLive_card_lt_of_mass_lt A x (epoch x).value hfrozen
          (show ‖cubeMass A (epoch x).value‖ < ‖cubeMass A x‖ by linarith)
        have hnext : (cubeLive (epoch x).value).card ≤ fuel := by omega
        obtain ⟨hterm, hbound, hwork⟩ := ih (epoch x).value hnext
        simp only [run, if_neg hs]
        refine ⟨hterm, ?_, ?_⟩
        · have hhalf := sqrt_half_budget (norm_nonneg (cubeMass A x))
            (norm_nonneg (cubeMass A (epoch x).value)) hmass
          have hmul := mul_le_mul_of_nonneg_left hhalf hδ
          calc
            ‖cubeCenter A (run A δ epoch testWork roundWork fuel (epoch x).value).value -
                cubeCenter A x‖ ≤
              ‖cubeCenter A (run A δ epoch testWork roundWork fuel (epoch x).value).value -
                cubeCenter A (epoch x).value‖ +
              ‖cubeCenter A (epoch x).value - cubeCenter A x‖ := by
                simpa only [sub_add_sub_cancel] using norm_add_le
                  (cubeCenter A (run A δ epoch testWork roundWork fuel (epoch x).value).value -
                    cubeCenter A (epoch x).value)
                  (cubeCenter A (epoch x).value - cubeCenter A x)
            _ ≤ 4 * δ * Real.sqrt ‖cubeMass A (epoch x).value‖ +
                δ * Real.sqrt ‖cubeMass A x‖ := add_le_add hbound hinc
            _ ≤ 4 * δ * Real.sqrt ‖cubeMass A x‖ := by nlinarith
        · nlinarith

/-- Starting at zero gives one sign for each original atom, with an explicit
linear number of calls to the counted epoch callback. -/
theorem run_origin_spec [Nonempty n] (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) {δ : ℝ} (hδ : 0 ≤ δ)
    (epoch : CubePoint ι → Counted (CubePoint ι)) (testWork roundWork Q : ℕ)
    (hepoch : ∀ x : CubePoint ι, δ ^ 2 < ‖cubeMass A x‖ →
      (∀ i, i ∉ cubeLive x → (epoch x).value.val i = x.val i) ∧
      ‖cubeMass A (epoch x).value‖ ≤ ‖cubeMass A x‖ / 2 ∧
      ‖cubeCenter A (epoch x).value - cubeCenter A x‖ ≤
        δ * Real.sqrt ‖cubeMass A x‖ ∧ (epoch x).cost ≤ Q) :
    let out := run A δ epoch testWork roundWork (Fintype.card ι) originCube
    (∀ i, out.value.val i = 1 ∨ out.value.val i = -1) ∧
      ‖∑ i, out.value.val i • A i‖ ≤ 4 * δ * Real.sqrt ‖∑ i, A i‖ ∧
      out.cost ≤ Fintype.card ι * (Q + testWork) + roundWork := by
  have hh := run_spec A hA hδ epoch testWork roundWork Q hepoch (Fintype.card ι)
    originCube (Finset.card_le_card (Finset.subset_univ _))
  rw [cubeCenter_origin,sub_zero,cubeMass_origin] at hh
  exact hh

end HigherRankKSRuntime.GlobalEpochs
