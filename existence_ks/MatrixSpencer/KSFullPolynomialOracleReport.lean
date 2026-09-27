import MatrixSpencer.KSFullConvexRuntime
import MatrixSpencer.RealRAMKSFullStateData
import MatrixSpencer.RealRAMOwnerSDPSetup
import MatrixSpencer.KSConvexQueryBudgets

/-! Actual full-cube state reports with complete construction accounting.
The only external cost contract is the explicitly permitted polynomial solver
on an already materialized affine PSD program. The current state's center,
source family, coefficient covariance, program arrays, and objective are all
constructed by the preceding primitive evaluators. -/
open Matrix Set
open scoped BigOperators
noncomputable section
namespace MatrixSpencer.KSFullPolynomialOracleReport
open RealRAM.JacobiIteration (Counted)
open RealRAM.KSFullStateData
open KSPolynomialConvexSolver KSConvexQueryBudgets
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
variable {N d : ℕ}

theorem source_isHermitian (v : Fin N → Fin d → ℂ) (x : Fin N → ℝ) (δ η : ℝ)
    (i : Fin N × Fin 4) : ((compute v x δ η).value.A i).IsHermitian := by
  rw [compute_A]
  exact (KSSpinSource.family_isHermitian _ (fun j => KSRankOne.atom_isHermitian (v j)) i).submatrix _

theorem covariance_posSemidef (v : Fin N → Fin d → ℂ) (x : Fin N → ℝ) (δ η : ℝ) :
    (compute v x δ η).value.C.PosSemidef := by
  rw [compute_C]
  exact KSSpinSource.coefficientCovariance_posSemidef (fun _ => le_max_left _ _)

def report (P : PolynomialSolver) (v : Fin N → Fin d → ℂ) (δ η θ : ℝ) (hd : 0<d)
    (ν : ℝ) (x : Fin N → ℝ) : Counted ℝ :=
  let a := compute v x δ η
  let r := RealRAM.OwnerSDPSetup.ownerReport P ⟨0,by omega⟩ a.value.H a.value.A
    (source_isHermitian v x δ η) a.value.C (covariance_posSemidef v x δ η) (by omega) θ ν
  ⟨r.value,a.cost+r.cost+4⟩

theorem report_value (P : PolynomialSolver) (v : Fin N → Fin d → ℂ) (δ η θ : ℝ) (hd : 0<d)
    (ν : ℝ) (x : Fin N → ℝ) :
    (report P v δ η θ hd ν x).value=KSFullConvexOracleValue.stateReport P.solver v δ η θ hd ν x := by
  simp only [report,RealRAM.OwnerSDPSetup.ownerReport_value,compute_H,compute_A,compute_C]
  rfl

/-- Fixed polynomial work for all actual full-cube state and stencil queries. -/
def queryCost (P : PolynomialSolver) (N d : ℕ) : ℕ :=
  10000*(N+1)^2*(d+1)^2+RealRAM.OwnerSDPSetup.setupCost (N*4) (d+d)+solverWork P N d+4

theorem report_cost (P : PolynomialSolver) (v : Fin N → Fin d → ℂ) (δ η θ : ℝ) (hd : 0<d)
    (ν : ℝ) (hν : 0<ν) (hV : ν⁻¹≤(valuePrecision N d:ℝ)) (x : Fin N → ℝ) :
    (report P v δ η θ hd ν x).cost≤queryCost P N d := by
  have h1 := compute_cost v x δ η
  have h2 := RealRAM.OwnerSDPSetup.ownerReport_cost_le P (⟨0,by omega⟩ : Fin (d+d))
    (compute v x δ η).value.H (compute v x δ η).value.A (source_isHermitian v x δ η)
    (compute v x δ η).value.C (covariance_posSemidef v x δ η) (by omega) θ ν hν
    (dataSize_le _) hV
  simp only [Fintype.card_prod,Fintype.card_fin] at h2
  dsimp only [report,queryCost,solverWork]
  omega

def evaluator (P : PolynomialSolver) (v : Fin N → Fin d → ℂ) (δ η θ : ℝ) (hd : 0<d) :
    KSFullConvexRuntime.ValueEvaluator P.solver v δ η θ hd where
  report := report P v δ η θ hd
  correct := report_value P v δ η θ hd

theorem state_cost (P : PolynomialSolver) (v : Fin N → Fin d → ℂ) (hd : 0<d)
    (hp : (∑i,KSRankOne.atom (v i))=1) (x : Fin N → ℝ) :
    ((evaluator P v (Real.sqrt (KSEighthManuscriptPreprocess.epsilon v))
      (Real.sqrt (KSEighthManuscriptPreprocess.epsilon v)/(N:ℝ))
      (ksRegularizerScale (KSEighthManuscriptPreprocess.epsilon v) (Fin d)) hd).report
      (Real.sqrt (KSEighthManuscriptPreprocess.epsilon v)/(N:ℝ)/8) x).cost≤queryCost P N d := by
  have hN := KSManuscriptInputPolynomialParameters.labels_pos v hd hp
  have hδ := Real.sqrt_pos.mpr (KSEighthManuscriptPreprocess.epsilon_pos v hd hp)
  apply report_cost P v _ _ _ hd
  · positivity
  · exact full_state_inverse v hd hp

variable [Nonempty (Fin d)]

theorem hessian_cost (P : PolynomialSolver) (v : Fin N → Fin d → ℂ) (hd : 0<d)
    (hp : (∑i,KSRankOne.atom (v i))=1) (x : Fin N → ℝ) :
    ((evaluator P v (Real.sqrt (KSEighthManuscriptPreprocess.epsilon v))
      (Real.sqrt (KSEighthManuscriptPreprocess.epsilon v)/(N:ℝ))
      (ksRegularizerScale (KSEighthManuscriptPreprocess.epsilon v) (Fin d)) hd).report
      (KSFullManuscriptParameters.valueTolerance N (Real.sqrt (KSEighthManuscriptPreprocess.epsilon v))
        (KSFullConvexOracleAlgorithm.taylorBudget v (KSEighthManuscriptPreprocess.epsilon v))) x).cost≤queryCost P N d := by
  have hN := KSManuscriptInputPolynomialParameters.labels_pos v hd hp
  have hδ := Real.sqrt_pos.mpr (KSEighthManuscriptPreprocess.epsilon_pos v hd hp)
  apply report_cost P v _ _ _ hd
  · exact KSFullManuscriptParameters.valueTolerance_pos hN hδ
      (KSFullConvexOracleAlgorithm.taylorBudget_pos v hN (KSEighthManuscriptPreprocess.epsilon_pos v hd hp))
  · exact full_query_inverse v hd hp

end MatrixSpencer.KSFullPolynomialOracleReport
