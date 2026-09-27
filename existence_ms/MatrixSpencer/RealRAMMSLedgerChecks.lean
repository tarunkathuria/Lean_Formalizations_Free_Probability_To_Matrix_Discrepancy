import MatrixSpencer.MSCountedStateOperations

/-! Primitive scalar witnesses for the fixed ledger arithmetic and stopping
branches. Dimension and frozen-count registers are the results of the already
counted address/label scans. -/
noncomputable section
namespace MatrixSpencer.RealRAM.MSLedgerChecks
attribute [local instance] Classical.propDecidable
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- Registers: N, time, frozen count, paid, dust, h, output bit. -/
def stoppedProgram : Program (Fin 7) :=
  let yes:=Program.assign 6 (.constant 1)
  let no:=Program.assign 6 (.constant 0)
  let threshold:=Expr.div (.input 0) (.constant 64)
  let total:=Expr.add (.input 3) (.input 4)
  let nextTime:=Expr.add (.input 1) (.mul (.input 5) (.input 5))
  .branchLE (.constant (1/1539)) (.input 1) yes
    (.branchLE threshold (.input 2) yes
      (.branchLE total threshold
        (.branchLE nextTime (.constant (1/1539)) no yes) yes))

theorem stopped_safe (v : Fin 7→ℝ) : stoppedProgram.Safe v := by
  simp only [stoppedProgram,Program.Safe,Expr.Valid,Expr.eval]
  norm_num

theorem stopped_result (v : Fin 7→ℝ) :
    stoppedProgram.run v 6=
      if (1:ℝ)/1539 ≤ v 1 ∨ v 0/64 ≤ v 2 ∨ v 0/64<v 3+v 4 ∨
        (1:ℝ)/1539<v 1+(v 5)^2 then 1 else 0 := by
  simp only [stoppedProgram,Program.run,Expr.eval,ite_apply,Function.update_self]
  norm_num only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat]
  split_ifs <;> simp_all [not_le,not_lt,pow_two] <;> (aesop <;> linarith)

theorem stopped_execution (v : Fin 7→ℝ) :
    ∃k ≤ 40,Program.Executes stoppedProgram v (stoppedProgram.run v) k := by
  obtain ⟨k,hk,he⟩:=Program.safe_execution_bounded stoppedProgram v (stopped_safe v)
  refine ⟨k,hk.trans ?_,he⟩
  norm_num [stoppedProgram,Program.bound,Expr.cost]

/-- Registers: paid,dust,alpha,counter,oldTrace,newTrace. -/
def preparePaid : Expr (Fin 6) := .add (.input 0) (.mul (.input 2) (.input 3))
def prepareDust : Expr (Fin 6) :=
  .add (.input 1) (.sub (.sub (.input 4) (.input 5)) (.mul (.input 2) (.input 3)))

theorem prepare_paid_execution (v : Fin 6→ℝ) :
    Expr.Executes v preparePaid (v 0+v 2*v 3) 5 := by
  have hv : preparePaid.Valid v := by simp [preparePaid,Expr.Valid]
  simpa [preparePaid,Expr.eval,Expr.cost] using Expr.executes_of_valid v preparePaid hv

theorem prepare_dust_execution (v : Fin 6→ℝ) :
    Expr.Executes v prepareDust (v 1+(v 4-v 5-v 2*v 3)) 9 := by
  have hv : prepareDust.Valid v := by simp [prepareDust,Expr.Valid]
  simpa [prepareDust,Expr.eval,Expr.cost] using Expr.executes_of_valid v prepareDust hv

/-- Registers: time,variance,rounding,h,traceQ,roundingLoss. -/
def moveTime : Expr (Fin 6) := .add (.input 0) (.mul (.input 3) (.input 3))
def moveVariance : Expr (Fin 6) :=
  .add (.input 1) (.mul (.mul (.input 3) (.input 3)) (.input 4))
def moveRounding : Expr (Fin 6) := .add (.input 2) (.input 5)

theorem move_time_execution (v : Fin 6→ℝ) :
    Expr.Executes v moveTime (v 0+(v 3)^2) 5 := by
  have hv : moveTime.Valid v := by simp [moveTime,Expr.Valid]
  simpa [moveTime,Expr.eval,Expr.cost,pow_two] using Expr.executes_of_valid v moveTime hv

theorem move_variance_execution (v : Fin 6→ℝ) :
    Expr.Executes v moveVariance (v 1+(v 3)^2*v 4) 7 := by
  have hv : moveVariance.Valid v := by simp [moveVariance,Expr.Valid]
  simpa [moveVariance,Expr.eval,Expr.cost,pow_two] using Expr.executes_of_valid v moveVariance hv

theorem move_rounding_execution (v : Fin 6→ℝ) :
    Expr.Executes v moveRounding (v 2+v 5) 3 := by
  have hv : moveRounding.Valid v := by simp [moveRounding,Expr.Valid]
  simpa [moveRounding,Expr.eval,Expr.cost] using Expr.executes_of_valid v moveRounding hv

end MatrixSpencer.RealRAM.MSLedgerChecks
