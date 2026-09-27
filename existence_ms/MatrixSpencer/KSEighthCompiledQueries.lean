import MatrixSpencer.KSEighthOwnerInputExecution
import MatrixSpencer.KSEighthConvexRuntime
import MatrixSpencer.RealRAMOwnerSDPSetup

/-! Concrete counted state and retained-face reports. Every call materializes
the original-input owner pencil before invoking the permitted polynomial
solver. The actual-input cost bounds discharge the intermediate query fields
of the eighth online evaluator. -/
open Set Matrix
open scoped BigOperators
noncomputable section
namespace MatrixSpencer.KSEighthCompiledQueries
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
open RealRAM RealRAM.JacobiIteration KSEighthOwnerInputSetup
open KSEighthCountedPreparation KSEighthManuscriptPreprocess
variable {N d : ℕ}
attribute [local instance] Classical.propDecidable

def ownerReport (P : KSPolynomialConvexSolver.PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (θ : ℝ) (hd : 0<d) (c : Fin N → ℝ) (ν : ℝ) (x : Fin N → ℝ) : Counted ℝ :=
  let h := H v x
  let a := A v x
  let w := C c
  let r := OwnerSDPSetup.ownerReport P ⟨0,by omega⟩ h.value a.value (A_isHermitian v x)
    w.value (C_posSemidef c) (by omega) θ ν
  ⟨r.value,h.cost+a.cost+w.cost+r.cost+4⟩

theorem ownerReport_value (P : KSPolynomialConvexSolver.PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (θ : ℝ) (hd : 0<d) (c : Fin N → ℝ) (ν : ℝ) (x : Fin N → ℝ) :
    (ownerReport P v θ hd c ν x).value=KSEighthConvexValue.ownerReport P.solver v θ hd c ν x := by
  simp only [ownerReport,OwnerSDPSetup.ownerReport_value,H_value,A_value,C_value,
    KSEighthConvexValue.ownerReport,KSConvexValueOracle.reindexedOwnerReport]

def queryCost (P : KSPolynomialConvexSolver.PolynomialSolver) (N d : ℕ) : ℕ :=
  KSEighthOwnerInputSetup.costBudget N d+OwnerSDPSetup.setupCost (2*N) (d+d)+
    KSConvexQueryBudgets.solverWork P N d+200*(N+1)^2+10

theorem ownerReport_cost (P : KSPolynomialConvexSolver.PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (θ : ℝ) (hd : 0<d) (c : Fin N → ℝ) (ν : ℝ) (x : Fin N → ℝ)
    (hν : 0<ν) (hV : ν⁻¹≤(KSConvexQueryBudgets.valuePrecision N d:ℝ)) :
    (ownerReport P v θ hd c ν x).cost≤KSEighthOwnerInputSetup.costBudget N d+
      OwnerSDPSetup.setupCost (2*N) (d+d)+KSConvexQueryBudgets.solverWork P N d+4 := by
  have hh := H_cost v x
  have ha := A_cost v x
  have hc := C_cost c
  have hr := OwnerSDPSetup.ownerReport_cost_le P ⟨0,by omega⟩ (H v x).value (A v x).value
    (A_isHermitian v x) (C c).value (C_posSemidef c) (by omega) θ ν hν
    (KSConvexQueryBudgets.dataSize_le _) hV
  simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool] at hr
  rw [Nat.mul_comm N 2] at hr
  dsimp only [ownerReport,KSEighthOwnerInputSetup.costBudget,KSConvexQueryBudgets.solverWork] at *
  omega

/-- Building either mask permits a full finite membership scan per coordinate,
and charges scalar owner arithmetic, copies and list control. -/
def stateReport (P : KSPolynomialConvexSolver.PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (θ : ℝ) (hd : 0<d) (ν : ℝ) (x : Fin N → ℝ) : Counted ℝ :=
  let m := KSEighthOwnerInputExecution.mask (KSPotentialModels.live (1/8) x) x
  let r := ownerReport P v θ hd m.value ν x
  ⟨r.value,r.cost+m.cost+20*N+6⟩
def retainedReport (P : KSPolynomialConvexSolver.PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (θ : ℝ) (hd : 0<d) (L : Finset (Fin N)) (ν : ℝ) (x : Fin N → ℝ) : Counted ℝ :=
  let m := KSEighthOwnerInputExecution.mask L x
  let r := ownerReport P v θ hd m.value ν x
  ⟨r.value,r.cost+m.cost+6⟩
theorem stateReport_value (P : KSPolynomialConvexSolver.PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (θ : ℝ) (hd : 0<d) (ν : ℝ) (x : Fin N → ℝ) :
    (stateReport P v θ hd ν x).value=KSEighthConvexValue.stateReport P.solver v θ hd ν x := by
  simp only [stateReport,ownerReport_value,KSEighthOwnerInputExecution.mask_value,
    KSEighthConvexValue.stateReport,KSPotentialModels.truncatedOwners]
theorem retainedReport_value (P : KSPolynomialConvexSolver.PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (θ : ℝ) (hd : 0<d) (L : Finset (Fin N)) (ν : ℝ) (x : Fin N → ℝ) :
    (retainedReport P v θ hd L ν x).value=KSEighthConvexValue.retainedReport P.solver v θ hd L ν x := by
  simp only [retainedReport,ownerReport_value,KSEighthOwnerInputExecution.mask_value,
    KSEighthConvexValue.retainedReport]
def queries (P : KSPolynomialConvexSolver.PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (θ : ℝ) (hd : 0<d) : Queries P.solver v θ hd where
  state := stateReport P v θ hd
  state_value := stateReport_value P v θ hd
  retained := retainedReport P v θ hd
  retained_value := retainedReport_value P v θ hd

theorem state_cost (P : KSPolynomialConvexSolver.PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (θ : ℝ) (hd : 0<d) (ν : ℝ) (x : Fin N → ℝ)
    (hν : 0<ν) (hV : ν⁻¹≤(KSConvexQueryBudgets.valuePrecision N d:ℝ)) :
    ((queries P v θ hd).state ν x).cost≤queryCost P N d := by
  have h := ownerReport_cost P v θ hd (KSEighthOwnerInputExecution.mask (KSPotentialModels.live (1/8) x) x).value ν x hν hV
  have hm := KSEighthOwnerInputExecution.mask_cost (KSPotentialModels.live (1/8) x) x
  dsimp only [queries,stateReport,queryCost]
  nlinarith
theorem retained_cost (P : KSPolynomialConvexSolver.PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (θ : ℝ) (hd : 0<d) (L : Finset (Fin N)) (ν : ℝ) (x : Fin N → ℝ)
    (hν : 0<ν) (hV : ν⁻¹≤(KSConvexQueryBudgets.valuePrecision N d:ℝ)) :
    ((queries P v θ hd).retained L ν x).cost≤queryCost P N d := by
  have h := ownerReport_cost P v θ hd (KSEighthOwnerInputExecution.mask L x).value ν x hν hV
  have hm := KSEighthOwnerInputExecution.mask_cost L x
  dsimp only [queries,retainedReport,queryCost]
  omega

theorem actual_state_cost (P : KSPolynomialConvexSolver.PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (hd : 0<d) (hp : (∑i,KSRankOne.atom (v i))=1) (x : Fin N → ℝ) :
    ((queries P v (ksRegularizerScale (epsilon v) (Fin d)) hd).state
      (KSEighthManuscriptParameters.rho N (Real.sqrt (epsilon v))/8) x).cost≤queryCost P N d :=
  state_cost P v _ hd _ x (div_pos (KSEighthManuscriptParameters.rho_pos
    (KSManuscriptInputPolynomialParameters.labels_pos v hd hp) (Real.sqrt_pos.mpr (epsilon_pos v hd hp))) (by norm_num))
    (KSConvexQueryBudgets.eighth_state_inverse v hd hp)

theorem actual_face_cost (P : KSPolynomialConvexSolver.PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (hd : 0<d) (hp : (∑i,KSRankOne.atom (v i))=1) (x : Fin N → ℝ)
    (hk : 0<KSEighthLiveEnumeration.count x) (y : Fin N → ℝ) :
    ((queries P v (ksRegularizerScale (epsilon v) (Fin d)) hd).retained (KSPotentialModels.live (1/8) x)
      (KSEighthHessianQueries.queryTolerance v (ksRegularizerScale (epsilon v) (Fin d))
        (KSEighthManuscriptParameters.precision N (Real.sqrt (epsilon v))) x) y).cost≤queryCost P N d := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  have hN := KSManuscriptInputPolynomialParameters.labels_pos v hd hp
  have hδ := Real.sqrt_pos.mpr (epsilon_pos v hd hp)
  exact retained_cost P v _ hd _ _ y
    (KSEighthHessianQueries.queryTolerance_pos v (ksRegularizerScale_pos (epsilon_pos v hd hp))
      (KSEighthManuscriptParameters.precision_pos hN hδ) hd x hk)
    (KSConvexQueryBudgets.eighth_query_inverse v hd hp x hk)

theorem actual_acceptance_cost (P : KSPolynomialConvexSolver.PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (hd : 0<d) (hp : (∑i,KSRankOne.atom (v i))=1) (x : Fin N → ℝ) :
    ((queries P v (ksRegularizerScale (epsilon v) (Fin d)) hd).state (Real.sqrt (epsilon v)/4) x).cost≤queryCost P N d :=
  state_cost P v _ hd _ x (div_pos (Real.sqrt_pos.mpr (epsilon_pos v hd hp)) (by norm_num))
    (KSConvexQueryBudgets.acceptance_inverse v hd hp)

end MatrixSpencer.KSEighthCompiledQueries
