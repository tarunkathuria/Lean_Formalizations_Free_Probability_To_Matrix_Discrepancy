import MatrixSpencer.RectangularRidgeRetryParameters
import MatrixSpencer.RectangularRidgeResponseScalars
import MatrixSpencer.RealRAMJacobiRayleigh

/-! Primitive setup of the actual aspect-ratio-sensitive phase count.
The real ceiling is computed by a bounded comparison/addition loop; the
supplied cap is the proved dimension polynomial, never the unknown ceiling.
The conservative confidence retry count uses a fixed field-operation circuit. -/
noncomputable section
namespace MatrixSpencer.RectangularRidgePhaseSetup
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
open RealRAM RectangularRidgePhaseProgress RectangularRidgeRetryParameters
open RectangularRidgeRateArithmetic RectangularRidgeTuning
open RealRAM.JacobiIteration (Counted)

def argumentExpr (m : ℕ) : Expr (Fin 3) :=
  .add (.mul (.constant 64) (rateExpr m)) (.constant 129)

theorem argumentExpr_eval {N D : ℕ} (hN : 1 ≤ N) :
    (argumentExpr (depth N D hN)).eval (registers N D hN) =
      64 * (RectangularRidgeUniformResponse.coefficient N D hN + 1) + 129 := by
  simp only [argumentExpr, Expr.eval, rateExpr_eval, Rat.cast_ofNat]

theorem argumentExpr_cost (m : ℕ) : (argumentExpr m).cost = 2 * m + 20 := by
  simp only [argumentExpr, Expr.cost, rateExpr_cost]
  omega

theorem argumentExpr_valid {N D : ℕ} (hN : 1 ≤ N) (hND : N ≤ D) :
    (argumentExpr (depth N D hN)).Valid (registers N D hN) :=
  ⟨⟨trivial, rateExpr_valid hN hND⟩, trivial⟩

theorem argumentExpr_executes {N D : ℕ} (hN : 1 ≤ N) (hND : N ≤ D) :
    Expr.Executes (registers N D hN) (argumentExpr (depth N D hN))
      (64 * (RectangularRidgeUniformResponse.coefficient N D hN + 1) + 129)
        (2 * depth N D hN + 20) := by
  have hh := Expr.executes_of_valid _ _ (argumentExpr_valid hN hND)
  simpa only [argumentExpr_eval, argumentExpr_cost] using hh

theorem argument_ceil {N D : ℕ} (hN : 1 ≤ N) :
    ⌈64 * (RectangularRidgeUniformResponse.coefficient N D hN + 1) + 129⌉₊ = epochCalls N D hN := by
  unfold epochCalls RectangularEpochParameters.count
  congr 1
  ring

theorem argument_le_cap {N D : ℕ} (hN : 1 ≤ N) (hND : N ≤ D) :
    64 * (RectangularRidgeUniformResponse.coefficient N D hN + 1) + 129 ≤
      (selected N D : ℝ) := by
  have hc : epochCalls N D hN ≤ selected N D :=
    (Nat.le_mul_of_pos_left _ (Nat.succ_pos N)).trans (total_calls_le hN hND)
  have hh := Nat.le_ceil (64 * (RectangularRidgeUniformResponse.coefficient N D hN + 1) + 129)
  rw [argument_ceil] at hh
  exact hh.trans (Nat.cast_le.mpr hc)

/-- The final natural count is the output of a literal safe real-register
program using only bounded comparisons and increments. -/
theorem ceiling_executes {N D : ℕ} (hN : 1 ≤ N) (hND : N ≤ D) :
    let input : Ceiling.Register → ℝ := fun r => match r with
      | .argument => 64 * (RectangularRidgeUniformResponse.coefficient N D hN + 1) + 129
      | .counter => 0
    ∃ w k, Program.Executes (Ceiling.program (selected N D)) input w k ∧
      w .counter = (epochCalls N D hN : ℝ) ∧ k ≤ 8 * selected N D + 3 := by
  dsimp only
  obtain ⟨w, k, he, hc, _, hk⟩ := Ceiling.execution (selected N D)
    (fun r => match r with
      | .argument => 64 * (RectangularRidgeUniformResponse.coefficient N D hN + 1) + 129
      | .counter => 0) (argument_le_cap hN hND)
  rw [argument_ceil] at hc
  exact ⟨w, k, he, hc, hk⟩

def sizeExpr : Expr (Fin 3) := .add (.add (.input 0) (.input 1)) (.constant 2)
def capExpr : Expr (Fin 3) :=
  .mul (.constant ((2 : ℚ) ^ 22)) (RectangularRidgeNumericalSetup.power sizeExpr 4)
def retryExpr : Expr (Fin 3) := .add (.add capExpr (.input 2)) (.constant 1)

theorem capExpr_eval (N D k : ℕ) : capExpr.eval ![D, N, k] = (selected N D : ℝ) := by
  simp only [capExpr, Expr.eval, RectangularRidgeNumericalSetup.power_eval, sizeExpr,
    Rat.cast_pow, Rat.cast_ofNat, Matrix.cons_val_zero, Matrix.cons_val_one,
    selected, Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat]

theorem retryExpr_eval (N D k : ℕ) : retryExpr.eval ![D, N, k] = (retries N D k : ℝ) := by
  simp only [retryExpr, Expr.eval, capExpr_eval, Rat.cast_one, retries, Nat.cast_add, Nat.cast_one]
  rfl

theorem capExpr_valid (v : Fin 3 → ℝ) : capExpr.Valid v :=
  ⟨trivial, RectangularRidgeNumericalSetup.power_valid sizeExpr v ⟨⟨trivial, trivial⟩, trivial⟩ 4⟩

theorem retryExpr_valid (v : Fin 3 → ℝ) : retryExpr.Valid v :=
  ⟨⟨capExpr_valid v, trivial⟩, trivial⟩

theorem capExpr_cost : capExpr.cost ≤ 100 := by
  norm_num [capExpr, Expr.cost, RectangularRidgeNumericalSetup.power_cost, sizeExpr]

theorem retryExpr_cost : retryExpr.cost ≤ 104 := by
  simp only [retryExpr, Expr.cost]
  have hh := capExpr_cost
  omega

theorem retryExpr_executes (N D k : ℕ) :
    Expr.Executes ![(D : ℝ), N, k] retryExpr (retries N D k : ℝ) retryExpr.cost := by
  rw [← retryExpr_eval]
  exact Expr.executes_of_valid _ _ (retryExpr_valid _)

def setupWithCap (N D cap : ℕ) : Counted ℕ :=
  let t := RectangularRidgeResponseScalars.selected N D
  let theta := (RectangularRidgeWeightWork.expression t.level).eval ![N, D, t.power]
  let arg := (argumentExpr t.level).eval ![N, t.power, theta]
  let ceiling := JacobiRayleigh.ceilLoop arg cap
  ⟨ceiling.value,
    scanCost N D (D + 1) initial + (RectangularRidgeWeightWork.expression t.level).cost +
      (argumentExpr t.level).cost + capExpr.cost + ceiling.cost + 20⟩

theorem setupWithCap_value {N D : ℕ} (hN : 1 ≤ N) (hND : N ≤ D)
    (cap : ℕ) (hcap : 64 * (RectangularRidgeUniformResponse.coefficient N D hN + 1) + 129 ≤ (cap : ℝ)) :
    (setupWithCap N D cap).value = epochCalls N D hN := by
  have hw : (RectangularRidgeWeightWork.expression (depth N D hN)).eval
      ![N, D, order N D hN] = RectangularRidgePrimitiveParameters.weight N D hN :=
    RectangularRidgeWeightWork.expression_eval hN hND
  simp only [setupWithCap, RectangularRidgeResponseScalars.selected_level hN,
    RectangularRidgeResponseScalars.selected_power hN, hw]
  change (JacobiRayleigh.ceilLoop ((argumentExpr (depth N D hN)).eval (registers N D hN))
    cap).value = _
  rw [argumentExpr_eval, JacobiRayleigh.ceilLoop_exact _ _ hcap, argument_ceil]

theorem setupWithCap_cost {N D : ℕ} (hN : 1 ≤ N) (cap : ℕ) :
    (setupWithCap N D cap).cost ≤ 8 * cap + 10 * D + 200 := by
  have hs := scanCost_le N D (D + 1) initial
  have hw := RectangularRidgeWeightWork.operation_budget (D := D) hN
  have hd := depth_le N D hN
  have hc := capExpr_cost
  simp only [setupWithCap, RectangularRidgeResponseScalars.selected_level hN,
    JacobiRayleigh.ceilLoop_cost, argumentExpr_cost]
  omega

def setup (N D : ℕ) : Counted ℕ := setupWithCap N D (selected N D)

theorem setup_value {N D : ℕ} (hN : 1 ≤ N) (hND : N ≤ D) :
    (setup N D).value = epochCalls N D hN :=
  setupWithCap_value hN hND (selected N D) (argument_le_cap hN hND)

theorem setup_cost {N D : ℕ} (hN : 1 ≤ N) :
    (setup N D).cost ≤ 8 * selected N D + 10 * D + 200 :=
  setupWithCap_cost hN (selected N D)

end MatrixSpencer.RectangularRidgePhaseSetup
