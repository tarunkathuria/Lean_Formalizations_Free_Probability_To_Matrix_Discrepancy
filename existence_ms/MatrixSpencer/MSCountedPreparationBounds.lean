import MatrixSpencer.MSCountedResponse
import MatrixSpencer.MSManuscriptPolynomialQueryResponse

/-! Polynomial bounds for every executed cleanup and finite-difference response
of the compiled convex-solver preparation. Inputs are original phase bounds;
the only remaining numerical lookup premise is discharged by scalar setup. -/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.MSCountedPreparationBounds
open RealRAM
open MSManuscriptSupportedGamma MSManuscriptSupportedOwner
open MSManuscriptPolynomialQueryCurvature MSManuscriptPolynomialQueryParameters
open MSManuscriptPolynomialQueryMagnitude
open MSManuscriptPolynomialQueryResponse
variable {m N d : ℕ}
local instance : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
attribute [local irreducible] ownerPotential

def programSize (d : ℕ) : ℕ := 400*d^4+4*d^2+2

theorem dataSize_le (a : Fin d) :
    KSPolynomialConvexSolver.dataSize (KSFullManuscriptAffineData.dimension a)
      (KSFullManuscriptAffineData.matrixSize (Fin d)) ≤ programSize d := by
  have hdim : KSFullManuscriptAffineData.dimension a ≤ 4*d^2 := by
    rw [KSConvexValueOracle.variableCount]
    omega
  unfold KSPolynomialConvexSolver.dataSize programSize
  rw [KSConvexValueOracle.pencilEntries a]
  omega

theorem setupCost_mono {k N d : ℕ} (hk : k ≤ N) :
    MSRawOwnerReport.setupCost k d ≤ MSRawOwnerReport.setupCost N d := by
  unfold MSRawOwnerReport.setupCost OwnerSDPSetup.blockBound OwnerSDPBlocks.sourceBound
  gcongr

def responseBudget (S : KSPolynomialConvexSolver.PolynomialSolver) (N d B : ℕ) : ℕ :=
  B+6*N^2*MSCountedResponse.queryBudget S N d (programSize d) (valueInv N d)+
    1000*(2*N+d+1)^4

section GenericOracle
variable [MSConvexOwnerValue.Oracle]

theorem entries (P : Parameters m d) (hP : P.Valid) (hm : m ≤ N)
    (hθ : P.regularizer=1) (hδ : P.floor=1/8192)
    (ht : P.threshold=4096/Real.sqrt (m:ℝ)) (hR : P.centerCap ≤ center N d)
    (O : Owner m) (hO : O.Valid P.floor) (hO1 : O.physical ≤ 1)
    (hOm : O.dim ≤ m) (hk : 0<O.dim) :
    ∀i j,|MSConvexSupportedGamma.response P O i j| ≤ responseEntry N d := by
  letI : Nonempty (Fin d):=Fin.pos_iff_nonempty.mp P.physicalDimension_pos
  have hr : ∀C,C.PosSemidef→
      |MSConvexOwnerValue.report P.center (family P O) C P.regularizer
        P.physicalDimension_pos (tolerance P O)-
        ownerPotential P.center (family P O) C P.regularizer| ≤ tolerance P O := by
    intro C hC
    exact MSConvexOwnerValue.report_accuracy _ P.center.property _
      (family_isHermitian P hP O) hC hP.2.2.1 (tolerance_pos P hP O hk)
      P.physicalDimension_pos
  have he:=reported_entries P hP hm hθ hδ ht hR O hO hO1 hOm hk _ hr
  change ∀i j,|MSManuscriptGammaMatrix.reconstruct
    (MSConvexGammaDifference.probe P.center (family P O) O.matrix P.regularizer
      P.physicalDimension_pos (spacing P O) (tolerance P O)) i j| ≤ _
  have hp : MSConvexGammaDifference.probe P.center (family P O) O.matrix P.regularizer
      P.physicalDimension_pos (spacing P O) (tolerance P O)=
      (fun u=>(MSConvexOwnerValue.report P.center (family P O) O.matrix P.regularizer
        P.physicalDimension_pos (tolerance P O)-
        MSConvexOwnerValue.report P.center (family P O)
          (O.matrix-spacing P O • realRankOne (WithLp.ofLp u)) P.regularizer
          P.physicalDimension_pos (tolerance P O))/spacing P O) := by
    funext u
    simp only [MSConvexGammaDifference.probe,MSConvexGammaDifference.valueCurve,
      MSManuscriptGammaDifference.negativeSlope,zero_smul,sub_zero]
  rw [hp]
  exact he

end GenericOracle

theorem tolerance_inverse (P : Parameters m d) (hP : P.Valid) (hm : m ≤ N)
    (hθ : P.regularizer=1) (hδ : P.floor=1/8192)
    (ht : P.threshold=4096/Real.sqrt (m:ℝ)) (hR : P.centerCap ≤ center N d)
    (O : Owner m) (hOm : O.dim ≤ m) (hk : 0<O.dim) :
    (MSCountedResponse.tuning P O.dim).2⁻¹ ≤ (valueInv N d:ℝ) := by
  have hL:=MSManuscriptPolynomialQueryCurvature.secondCap_le (hOm.trans hm) hm
    P.physicalDimension_pos ((norm_nonneg _).trans hP.2.2.2.2.2.2) hR
  have hti : P.threshold⁻¹ ≤ thresholdInv N := by rw [ht];exact threshold_inverse_le hm
  have hi:=topPrecision_inverse_le (hOm.trans hm) hP.2.2.2.2.2.1 hti
  change (MSManuscriptGammaDifference.valueTolerance P.floor (curvatureCap P O)
    (precision P O))⁻¹ ≤ _
  rw [hδ]
  apply valueTolerance_inverse_le (curvature_nonneg P hP O)
    (MSManuscriptGammaMatrix.topPrecision_pos hk hP.2.2.2.2.2.1) ?_ hi
  simpa only [curvatureCap,hθ,hδ] using hL

theorem bounds (S : KSPolynomialConvexSolver.PolynomialSolver)
    (P : Parameters m d) (hP : P.Valid) (hm : m ≤ N)
    (hθ : P.regularizer=1) (hδ : P.floor=1/8192)
    (ht : P.threshold=4096/Real.sqrt (m:ℝ)) (hR : P.centerCap ≤ center N d)
    (T : MSCountedResponse.Scalars P) (B : ℕ)
    (hB : ∀k,k ≤ m→(T.compute k).cost ≤ B) :
    @MSCountedPreparation.Bounds (MSRawOwnerReport.oracle S) m d P
      (MSCountedResponse.evaluator S P T)
      (MSManuscriptPolynomialQueryCleanup.cleanupJacobi N)
      (responseJacobi N d) (responseBudget S N d B) := by
  letI:=MSRawOwnerReport.oracle S
  constructor
  · intro O hO
    rw [hδ]
    apply MSManuscriptPolynomialQueryCleanup.ceiling_input_le O (hO.2.2.trans hm)
      (by simpa only [hδ] using hO.1) hO.2.1
  · intro O hO
    change KSJacobiIteration.denominator O.dim*KSJacobiStep.offDiagonalEnergy
      (-(MSCountedResponse.response S P T O).value)/(P.threshold/64)^2 ≤ _
    by_cases hk : 0<O.dim
    · rw [MSCountedResponse.response_value]
      apply response_ceiling_input_le _ (hO.2.2.trans hm)
        (entries P hP hm hθ hδ ht hR O hO.1 hO.2.1 hO.2.2 hk) hP.2.2.2.2.2.1
      rw [ht]
      exact threshold_inverse_le hm
    · simp only [MSCountedResponse.response,dif_neg hk,neg_zero]
      simp [KSJacobiStep.offDiagonalEnergy]
  · intro O hO
    change (MSCountedResponse.response S P T O).cost ≤ _
    have hn:=hO.2.2.trans hm
    have hc:=MSCountedResponse.response_cost S P T O (programSize d) (valueInv N d) B
      (hB O.dim hO.2.2) (fun hk=>tolerance_pos P hP O hk)
      (dataSize_le ⟨0,P.physicalDimension_pos⟩)
      (fun hk=>tolerance_inverse P hP hm hθ hδ ht hR O hO.2.2 hk)
    apply hc.trans
    unfold responseBudget MSCountedResponse.queryBudget
    have hs:=setupCost_mono (d:=d) hn
    gcongr <;> omega

end MatrixSpencer.MSCountedPreparationBounds
