import MatrixSpencer.RealRAMMSRawOwnerReport
import MatrixSpencer.MSCountedPreparation

/-! Actual covariance-gradient reconstruction using the total compiled SDP
oracle. The separate scalar setup supplies exact finite-difference tunings;
their counted lookup/evaluation cost is included in every response call. -/
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.MSCountedResponse
open RealRAM
open RealRAM.JacobiIteration (Counted Mat)
open MSManuscriptSupportedGamma (Parameters)
open MSManuscriptSupportedOwner (Owner)
open MSManuscriptGammaDifference (stepSize valueTolerance)
variable {N d : ℕ}
attribute [local instance] Classical.propDecidable
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

def tuning (P : Parameters N d) (k : ℕ) : ℝ×ℝ :=
  let L:=MSManuscriptGammaInputBoundScaled.secondCap k d P.centerCap P.regularizer P.floor N
  let η:=MSManuscriptGammaMatrix.topPrecision k P.threshold
  (stepSize P.floor L η,valueTolerance P.floor L η)

structure Scalars (P : Parameters N d) where
  compute : (k : ℕ) → Counted (ℝ×ℝ)
  compute_value : ∀k,(compute k).value=tuning P k

def response (S : KSPolynomialConvexSolver.PolynomialSolver)
    (P : Parameters N d) (T : Scalars P) (O : Owner N) : Counted (Mat O.dim) :=
  if hk : 0<O.dim then
    let a:=MSOwnerReport.family P.atoms O.frame
    let t:=T.compute O.dim
    let q:=fun C=>MSRawOwnerReport.report S P.center a.value C P.regularizer
      P.physicalDimension_pos t.value.2
    let r:=MSResponse.reconstruct (MSResponse.probe q O.matrix t.value.1)
    ⟨r.value,a.cost+t.cost+r.cost+5⟩
  else ⟨0,2⟩

theorem response_value (S : KSPolynomialConvexSolver.PolynomialSolver)
    (P : Parameters N d) (T : Scalars P) (O : Owner N) :
    (response S P T O).value=
      @MSConvexSupportedGamma.response (MSRawOwnerReport.oracle S) N d P O := by
  unfold response
  split_ifs with hk
  · simp only [MSResponse.reconstruct_value,MSResponse.probe_value,
      T.compute_value,MSOwnerReport.family_value]
    rfl
  · ext i j
    exact (hk (Nat.zero_lt_of_lt i.isLt)).elim

def evaluator (S : KSPolynomialConvexSolver.PolynomialSolver)
    (P : Parameters N d) (T : Scalars P) :
    @MSCountedPreparation.Evaluator (MSRawOwnerReport.oracle S) N d P := by
  letI:=MSRawOwnerReport.oracle S
  exact ⟨response S P T,fun O _=>response_value S P T O⟩

def queryBudget (S : KSPolynomialConvexSolver.PolynomialSolver) (k d A V : ℕ) : ℕ :=
  MSRawOwnerReport.setupCost k d+S.coefficient*(A+V+1)^S.degree

theorem response_cost (S : KSPolynomialConvexSolver.PolynomialSolver)
    (P : Parameters N d) (T : Scalars P) (O : Owner N) (A V B : ℕ)
    (hB : (T.compute O.dim).cost≤B)
    (hν : 0<O.dim→0<(tuning P O.dim).2)
    (hA : KSPolynomialConvexSolver.dataSize
      (KSFullManuscriptAffineData.dimension (⟨0,P.physicalDimension_pos⟩:Fin d))
      (KSFullManuscriptAffineData.matrixSize (Fin d))≤A)
    (hV : 0<O.dim→(tuning P O.dim).2⁻¹≤(V:ℝ)) :
    (response S P T O).cost≤B+6*O.dim^2*queryBudget S O.dim d A V+
      1000*(N+O.dim+d+1)^4 := by
  unfold response
  split_ifs with hk
  · let a:=MSOwnerReport.family P.atoms O.frame
    let t:=T.compute O.dim
    let q:=fun C=>MSRawOwnerReport.report S P.center a.value C P.regularizer
      P.physicalDimension_pos t.value.2
    have hν' : 0<t.value.2 := by change 0<(T.compute O.dim).value.2;rw [T.compute_value];exact hν hk
    have hV' : t.value.2⁻¹≤(V:ℝ) := by change (T.compute O.dim).value.2⁻¹≤_;rw [T.compute_value];exact hV hk
    have hq : ∀C,(q C).cost≤queryBudget S O.dim d A V := by
      intro C
      simpa only [queryBudget,Fintype.card_fin] using
        MSRawOwnerReport.report_cost S P.center a.value C P.regularizer
          P.physicalDimension_pos t.value.2 hν' hA hV'
    have hp : ∀u,‖u‖=1→(MSResponse.probe q O.matrix t.value.1 u).cost≤
        2*queryBudget S O.dim d A V+46*(O.dim+1)^2 := by
      intro u _
      exact MSResponse.probe_cost _ _ _ _ _ (hq _) (hq _)
    have hr:=MSResponse.reconstruct_cost (MSResponse.probe q O.matrix t.value.1) _ hp
    have ha:=MSOwnerReport.family_cost P.atoms O.frame
    change a.cost+t.cost+(MSResponse.reconstruct (MSResponse.probe q O.matrix t.value.1)).cost+5≤_
    have hfa : a.cost≤20*(N+O.dim+d+1)^4 := by
      calc _=O.dim*d*d*(8*N+4)+1 := ha
           _≤(N+O.dim+d+1)*(N+O.dim+d+1)*(N+O.dim+d+1)*
              (12*(N+O.dim+d+1))+1 := by gcongr <;> omega
           _≤20*(N+O.dim+d+1)^4 := by nlinarith [Nat.one_le_pow 4 (N+O.dim+d+1) (by omega)]
    have hp2 : O.dim^2*(O.dim+1)^2≤(N+O.dim+d+1)^4 := by
      calc _≤(N+O.dim+d+1)^2*(N+O.dim+d+1)^2 := by gcongr <;> omega
           _=_ := by ring
    have hp3 : (O.dim+1)^3≤(N+O.dim+d+1)^4 :=
      (Nat.pow_le_pow_left (by omega) 3).trans (Nat.pow_le_pow_right (by omega) (by omega))
    have h1 : 1≤(N+O.dim+d+1)^4 := Nat.one_le_pow _ _ (by omega)
    dsimp only [t] at *
    nlinarith
  · simp only
    have h1 : 1≤(N+O.dim+d+1)^4 := Nat.one_le_pow _ _ (by omega)
    omega

end MatrixSpencer.MSCountedResponse
