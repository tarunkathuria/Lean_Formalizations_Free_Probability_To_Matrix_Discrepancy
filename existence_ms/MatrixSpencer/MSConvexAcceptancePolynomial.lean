import MatrixSpencer.RealRAMMSAcceptanceData
import MatrixSpencer.MSConvexPolynomialTangentParameters


open Matrix
noncomputable section
namespace MatrixSpencer.MSConvexAcceptancePolynomial
open RealRAM
variable {m N d : ℕ}
set_option maxRecDepth 4000
set_option maxHeartbeats 1200000

def programSize (d : ℕ) : ℕ := 400*d^4+4*d^2+2
def precisionCap (N d : ℕ) : ℕ := 300+MSConvexPolynomialTangentParameters.precisionInv N d

def acceptanceCost (P : KSPolynomialConvexSolver.PolynomialSolver) (N d : ℕ) : ℕ :=
  MSAcceptanceData.epochCost P N d (programSize d) (precisionCap N d)

theorem dataSize_le (a : Fin d) :
    KSPolynomialConvexSolver.dataSize (KSFullManuscriptAffineData.dimension a)
      (KSFullManuscriptAffineData.matrixSize (Fin d))≤programSize d := by
  have hdim : KSFullManuscriptAffineData.dimension a≤4*d^2 := by
    rw [KSConvexValueOracle.variableCount]
    omega
  unfold KSPolynomialConvexSolver.dataSize programSize
  rw [KSConvexValueOracle.pencilEntries a]
  omega

theorem setupCost_mono (hm : m≤N) : MSRawOwnerReport.setupCost m d≤MSRawOwnerReport.setupCost N d := by
  unfold MSRawOwnerReport.setupCost OwnerSDPSetup.blockBound OwnerSDPBlocks.sourceBound OwnerSDPBlocks.productBound
  gcongr

theorem epochCost_mono (P : KSPolynomialConvexSolver.PolynomialSolver) (S V : ℕ) (hm : m≤N) :
    MSAcceptanceData.epochCost P m d S V≤MSAcceptanceData.epochCost P N d S V := by
  have hs := setupCost_mono (d:=d) hm
  unfold MSAcceptanceData.epochCost MSConvexAcceptance.queryBudget
  gcongr

variable [Nonempty (Fin d)]

theorem accepts_cost (P : KSPolynomialConvexSolver.PolynomialSolver)
    (cfg : EpochConfig (Fin m) (Fin d)) (hd : 0<d) (hm : m≤N)
    (s : MSManuscriptNumericalEpochRun.Certified (MSManuscriptNumericalConfig.ofEpochConfig cfg hd)) :
    (MSAcceptanceData.accepts P cfg hd s).cost≤acceptanceCost P N d := by
  have hv:=MSManuscriptPolynomialQueryAcceptance.valueTolerance_inverse_le cfg hd
  have ht:=(MSConvexPolynomialTangentParameters.actual_inverse_bounds cfg hd hm).2
  have hV : (300:ℝ)≤(precisionCap N d:ℝ) := by
    exact_mod_cast (show 300≤precisionCap N d by unfold precisionCap; omega)
  have hT : (MSConvexPolynomialTangentParameters.precisionInv N d:ℝ)≤(precisionCap N d:ℝ) := by
    exact_mod_cast (show MSConvexPolynomialTangentParameters.precisionInv N d≤precisionCap N d by unfold precisionCap; omega)
  exact (MSAcceptanceData.accepts_cost P cfg hd s (dataSize_le ⟨0,hd⟩)
    (hv.trans hV) (ht.trans hT)).trans (epochCost_mono P _ _ hm)

end MatrixSpencer.MSConvexAcceptancePolynomial
