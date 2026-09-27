import MatrixSpencer.RealRAMMSValueAcceptance
import MatrixSpencer.RealRAMMSRawOwnerReport

/-! The counted six-query acceptance evaluator instantiated with the actual
raw SDP compiler and the permitted polynomial convex solver. Query sizes and
inverse precisions are the only scalar bounds supplied to this intermediate
cost lemma; no validity tests or primal optimization routines are hidden. -/
open Matrix
open scoped BigOperators
noncomputable section
namespace MatrixSpencer.RealRAM.MSConvexAcceptance
open JacobiIteration (Counted)
open MSManuscriptNumericalAcceptance MSConvexAnchorTangent
variable {N d : ℕ}
set_option maxHeartbeats 1200000
set_option maxRecDepth 4000

def queryBudget (P : KSPolynomialConvexSolver.PolynomialSolver) (N d S V : ℕ) : ℕ :=
  MSRawOwnerReport.setupCost N d+MSRawOwnerReport.setupCost 0 d+
    P.coefficient*(S+V+1)^P.degree

def ownerQuery (P : KSPolynomialConvexSolver.PolynomialSolver) (cfg : Config N d)
    (H : Matrix (Fin d) (Fin d) ℂ) (C : Matrix (Fin N) (Fin N) ℝ) (ν : ℝ) : Counted ℝ :=
  MSRawOwnerReport.report P H cfg.family C cfg.theta cfg.dimension_pos ν

def baseQuery (P : KSPolynomialConvexSolver.PolynomialSolver) (cfg : Config N d)
    (H : Matrix (Fin d) (Fin d) ℂ) (ν : ℝ) : Counted ℝ :=
  MSRawOwnerReport.report P H MSManuscriptAnchorDensity.emptyFamily 0 cfg.theta cfg.dimension_pos ν

def acceptance (P : KSPolynomialConvexSolver.PolynomialSolver) (cfg : Config N d)
    (e : Endpoint N d) : Counted Bool :=
  MSValueAcceptance.acceptance (ownerQuery P cfg) (baseQuery P cfg) cfg e

theorem acceptance_value (P : KSPolynomialConvexSolver.PolynomialSolver) (cfg : Config N d)
    (e : Endpoint N d) :
    (acceptance P cfg e).value=
      @MSConvexValueAcceptance.accepts (MSRawOwnerReport.oracle P) N d cfg e := by
  letI := MSRawOwnerReport.oracle P
  exact MSValueAcceptance.acceptance_value (ownerQuery P cfg) (baseQuery P cfg) cfg e
    (fun _ _ _=>rfl) (fun _ _=>rfl)

theorem ownerQuery_cost (P : KSPolynomialConvexSolver.PolynomialSolver) (cfg : Config N d)
    (H : Matrix (Fin d) (Fin d) ℂ) (C : Matrix (Fin N) (Fin N) ℝ) (ν : ℝ) (hν : 0<ν)
    {S V : ℕ}
    (hS : KSPolynomialConvexSolver.dataSize
      (KSFullManuscriptAffineData.dimension (⟨0,cfg.dimension_pos⟩:Fin d))
      (KSFullManuscriptAffineData.matrixSize (Fin d))≤S) (hV : ν⁻¹≤(V:ℝ)) :
    (ownerQuery P cfg H C ν).cost≤queryBudget P N d S V := by
  have h := MSRawOwnerReport.report_cost P H cfg.family C cfg.theta cfg.dimension_pos ν hν hS hV
  simp only [Fintype.card_fin] at h
  exact h.trans (by unfold queryBudget; omega)

theorem baseQuery_cost (P : KSPolynomialConvexSolver.PolynomialSolver) (cfg : Config N d)
    (H : Matrix (Fin d) (Fin d) ℂ) (ν : ℝ) (hν : 0<ν) {S V : ℕ}
    (hS : KSPolynomialConvexSolver.dataSize
      (KSFullManuscriptAffineData.dimension (⟨0,cfg.dimension_pos⟩:Fin d))
      (KSFullManuscriptAffineData.matrixSize (Fin d))≤S) (hV : ν⁻¹≤(V:ℝ)) :
    (baseQuery P cfg H ν).cost≤queryBudget P N d S V := by
  have h := MSRawOwnerReport.report_cost P H MSManuscriptAnchorDensity.emptyFamily 0 cfg.theta cfg.dimension_pos ν hν hS hV
  simp only [Fintype.card_empty] at h
  exact h.trans (by unfold queryBudget; omega)

theorem acceptance_cost (P : KSPolynomialConvexSolver.PolynomialSolver) (cfg : Config N d)
    (e : Endpoint N d) {S V : ℕ}
    (hS : KSPolynomialConvexSolver.dataSize
      (KSFullManuscriptAffineData.dimension (⟨0,cfg.dimension_pos⟩:Fin d))
      (KSFullManuscriptAffineData.matrixSize (Fin d))≤S)
    (hV : (tolerance cfg/3)⁻¹≤(V:ℝ))
    (hT : (precision cfg.theta cfg.radius (tolerance cfg))⁻¹≤(V:ℝ)) :
    (acceptance P cfg e).cost≤6*queryBudget P N d S V+80*d*d+200 := by
  letI := MSRawOwnerReport.oracle P
  exact MSValueAcceptance.acceptance_cost (ownerQuery P cfg) (baseQuery P cfg) cfg e
    (ownerQuery_cost P cfg e.center e.covariance _ (by have := tolerance_pos cfg; positivity) hS hV)
    (baseQuery_cost P cfg cfg.savedCenter _ (by have := tolerance_pos cfg; positivity) hS hV)
    (fun H=>baseQuery_cost P cfg H _ (precision_pos cfg.theta_pos (tolerance_pos cfg)) hS hT)

end MatrixSpencer.RealRAM.MSConvexAcceptance
