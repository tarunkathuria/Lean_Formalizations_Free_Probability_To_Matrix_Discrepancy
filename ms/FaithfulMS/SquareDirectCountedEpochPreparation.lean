import FaithfulMS.SquareDirectCountedBounds
import MatrixSpencer.MSCountedStateOperations
import FaithfulMS.SquareDirectEpochRun

/-! The concrete stored-owner preparation followed by its exact trace ledger
update and proof-certificate attachment. Parameter setup is a separate counted
stage; no proof field is inspected by the numerical execution. -/
open Matrix
noncomputable section
open MatrixSpencer
namespace FaithfulMS.SquareDirectCountedEpochPreparation
open RealRAM.JacobiIteration (Counted)
open MSManuscriptNumericalEpochRun (Config Certified params params_valid)
open MSManuscriptNumericalEpochLedger (State)
variable [SquareDirectOracle.Oracle]
variable {N d : ℕ}
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

def data (c : Config N d) (s : Certified c)
    (E : SquareDirectCountedPreparation.Evaluator (params c s.val)) (C J : ℕ) : Counted (State N) :=
  let r:=SquareDirectCountedPreparation.output (params c s.val) E C J s.val.owner
  match r.value with
  | none=>⟨s.val,r.cost+2⟩
  | some y=>
    let b:=MSCountedStateOperations.afterPrepare (params c s.val) s.val y
    ⟨b.value,r.cost+b.cost+3⟩

theorem data_value (c : Config N d) (s : Certified c)
    (E : SquareDirectCountedPreparation.Evaluator (params c s.val)) (C J R : ℕ)
    (hB : SquareDirectCountedPreparation.Bounds (params c s.val) E C J R) :
    (data c s E C J).value=(SquareDirectEpochRun.prepare c s).val := by
  have hr:=(SquareDirectCountedPreparation.output_correct (params c s.val) (params_valid c s)
    E C J R hB s.val.owner
    ⟨s.property.1.owner_valid,s.property.1.owner_le_one,s.property.1.dim_le⟩).1
  have hs:=SquareDirectEpochRun.preparationResult_eq c s
  simp only [data,hr,hs]
  rw [MSCountedStateOperations.afterPrepare_value]
  rfl

theorem data_cost (c : Config N d) (s : Certified c)
    (E : SquareDirectCountedPreparation.Evaluator (params c s.val)) (C J R : ℕ)
    (hB : SquareDirectCountedPreparation.Bounds (params c s.val) E C J R) :
    (data c s E C J).cost ≤
      MSManuscriptSupportedPreparation.budget (params c s.val)*
        SquareDirectCountedPreparation.roundBudget N C J R+14000*(N+1)^3 := by
  have hr:=SquareDirectCountedPreparation.output_correct (params c s.val) (params_valid c s)
    E C J R hB s.val.owner
    ⟨s.property.1.owner_valid,s.property.1.owner_le_one,s.property.1.dim_le⟩
  have hs:=SquareDirectEpochRun.preparationResult_eq c s
  have hc:=MSCountedStateOperations.afterPrepare_cost (params c s.val) s.val
    (SquareDirectEpochRun.preparationResult c s)
  have hn:=(SquareDirectEpochRun.prepare c s).property.1.dim_le
  change (SquareDirectEpochRun.preparationResult c s).1.dim ≤ N at hn
  have hb : N+s.val.owner.dim+(SquareDirectEpochRun.preparationResult c s).1.dim+1 ≤
      3*(N+1) := by have hh:=s.property.1.dim_le;omega
  have hc' : (MSCountedStateOperations.afterPrepare (params c s.val) s.val
      (SquareDirectEpochRun.preparationResult c s)).cost ≤ 13500*(N+1)^3 := by
    calc _ ≤ 500*(3*(N+1))^3 := hc.trans (by gcongr)
         _=_ := by ring
  simp only [data,hr.1,hs]
  have h1 : 1 ≤ (N+1)^3 := Nat.one_le_pow _ _ (by omega)
  omega

def compute (c : Config N d) (s : Certified c)
    (E : SquareDirectCountedPreparation.Evaluator (params c s.val)) (C J R : ℕ)
    (hB : SquareDirectCountedPreparation.Bounds (params c s.val) E C J R) : Counted (Certified c) :=
  let b:=data c s E C J
  ⟨⟨b.value,by rw [data_value c s E C J R hB];exact (SquareDirectEpochRun.prepare c s).property⟩,
    b.cost+2⟩

theorem compute_value (c : Config N d) (s : Certified c)
    (E : SquareDirectCountedPreparation.Evaluator (params c s.val)) (C J R : ℕ)
    (hB : SquareDirectCountedPreparation.Bounds (params c s.val) E C J R) :
    (compute c s E C J R hB).value=SquareDirectEpochRun.prepare c s :=
  Subtype.ext (data_value c s E C J R hB)

theorem compute_cost (c : Config N d) (s : Certified c)
    (E : SquareDirectCountedPreparation.Evaluator (params c s.val)) (C J R : ℕ)
    (hB : SquareDirectCountedPreparation.Bounds (params c s.val) E C J R) :
    (compute c s E C J R hB).cost ≤
      MSManuscriptSupportedPreparation.budget (params c s.val)*
        SquareDirectCountedPreparation.roundBudget N C J R+14000*(N+1)^3+2 :=
  Nat.add_le_add_right (data_cost c s E C J R hB) 2

end FaithfulMS.SquareDirectCountedEpochPreparation
