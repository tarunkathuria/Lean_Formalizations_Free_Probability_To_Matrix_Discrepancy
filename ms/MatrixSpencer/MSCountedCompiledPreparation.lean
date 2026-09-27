import MatrixSpencer.MSCountedEpochStep
import MatrixSpencer.RealRAMMSResponseScalarSetup
import MatrixSpencer.RealRAMMSParameterTables

/-! Concrete convex-solver preparation, including the changing signed center,
entry-arithmetic center bound, and exact scalar response setup. The epoch's
point-independent paid size and loop counters are computed once by the epoch
setup module and used as stored parameters here. -/
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.MSCountedCompiledPreparation
open RealRAM
open RealRAM.JacobiIteration (Counted)
open MSManuscriptNumericalEpochRun (Config Certified params params_valid)
open MSManuscriptPolynomialQueryCurvature MSManuscriptPolynomialQueryParameters
open MSManuscriptPolynomialQueryMagnitude MSManuscriptPolynomialQueryCleanup
variable {m N d : ℕ}
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

def parameters (c : Config m d) (s : Certified c) :
    Counted (MSManuscriptSupportedGamma.Parameters m d) := by
  letI : Nonempty (Fin d):=Fin.pos_iff_nonempty.mp c.dimension_pos
  let H:=MSOwnerReport.center c.offset c.atoms (WithLp.ofLp s.val.point)
  let R:=MSParameterTables.center (c.offset:Matrix (Fin d) (Fin d) ℂ) m
  have hH : H.value.IsHermitian := by
    rw [MSOwnerReport.center_epoch c.offset c.atoms c.hermitian s.val.point]
    exact (epochCenter c.offset c.atoms c.hermitian s.val.point).property
  exact ⟨{params c s.val with center:=⟨H.value,hH⟩,centerCap:=R.value},
    H.cost+R.cost+20*(m+d+1)^2+20⟩

theorem parameters_value (c : Config m d) (s : Certified c) :
    (parameters c s).value=params c s.val := by
  letI : Nonempty (Fin d):=Fin.pos_iff_nonempty.mp c.dimension_pos
  unfold parameters
  simp only [MSParameterTables.center_value]
  simp only [params,MSManuscriptEpochInput.params,
    MSManuscriptSupportedGamma.Parameters.mk.injEq]
  refine ⟨Subtype.ext (MSOwnerReport.center_epoch c.offset c.atoms c.hermitian s.val.point),?_⟩
  simp [MSManuscriptEpochInput.centerCap]

theorem parameters_cost (c : Config m d) (s : Certified c) :
    (parameters c s).cost ≤ 100*(m+d+1)^3 := by
  have hc:=MSOwnerReport.center_cost (c.offset:Matrix (Fin d) (Fin d) ℂ) c.atoms (WithLp.ofLp s.val.point)
  have hr:=MSParameterTables.center_cost d
  change (MSOwnerReport.center c.offset c.atoms (WithLp.ofLp s.val.point)).cost+
    (MSParameterTables.center (c.offset:Matrix (Fin d) (Fin d) ℂ) m).cost+20*(m+d+1)^2+20 ≤ _
  rw [hc]
  change d*d*(8*m+8)+1+((MSParameterTables.centerExpr d).cost+1)+20*(m+d+1)^2+20 ≤ _
  have hd : d*d*(8*m+8) ≤ 8*(m+d+1)^3 := by
    calc _ ≤ (m+d+1)*(m+d+1)*(8*(m+d+1)) := by gcongr <;> omega
         _=_ := by ring
  have hp : (d+1)^2 ≤ (m+d+1)^3 :=
    (Nat.pow_le_pow_left (by omega) 2).trans (Nat.pow_le_pow_right (by omega) (by omega))
  have hp' : (m+d+1)^2 ≤ (m+d+1)^3 := Nat.pow_le_pow_right (by omega) (by omega)
  have h1 : 1 ≤ (m+d+1)^3 := Nat.one_le_pow _ _ (by omega)
  omega

def responseBudget (S : KSPolynomialConvexSolver.PolynomialSolver) (N d : ℕ) :=
  MSCountedPreparationBounds.responseBudget S N d 2100020

def work (S : KSPolynomialConvexSolver.PolynomialSolver) (N d : ℕ) : ℕ :=
  preparation N d*MSCountedPreparation.roundBudget N (cleanupJacobi N)
    (responseJacobi N d) (responseBudget S N d)+100000*(N+d+1)^3

variable (S : KSPolynomialConvexSolver.PolynomialSolver)
  (c : Config m d) (hm : m ≤ N) (hθ : c.regularizer=1) (hδ : c.floor=1/8192)
  (ht : c.threshold=4096/Real.sqrt (m:ℝ))
  (hR : MSManuscriptEpochInput.centerCap c.offset (N:=m) ≤ center N d)

include hm hθ hδ ht hR

def evaluator (s : Certified c) :
    @MSCountedPreparation.Evaluator (MSRawOwnerReport.oracle S) m d (params c s.val) :=
  MSCountedResponse.evaluator S (params c s.val)
    (MSResponseScalarSetup.scalars (params c s.val) hθ hδ ht)

theorem bounds (s : Certified c) :
    @MSCountedPreparation.Bounds (MSRawOwnerReport.oracle S) m d (params c s.val)
      (evaluator S c hθ hδ ht s) (cleanupJacobi N) (responseJacobi N d) (responseBudget S N d) :=
  MSCountedPreparationBounds.bounds S _ (params_valid c s) hm hθ hδ ht hR _ 2100020
    (fun k _=>MSResponseScalarSetup.scalars_cost _ hθ hδ ht k)

def compute (s : Certified c) : Counted (Certified c) := by
  letI:=MSRawOwnerReport.oracle S
  let p:=parameters c s
  let r:=MSCountedEpochPreparation.compute c s (evaluator S c hθ hδ ht s)
    (cleanupJacobi N) (responseJacobi N d) (responseBudget S N d)
    (bounds S c hm hθ hδ ht hR s)
  exact ⟨r.value,p.cost+r.cost+2⟩

theorem compute_value (s : Certified c) :
    (compute S c hm hθ hδ ht hR s).value=
      @MSConvexNumericalEpochRun.prepare (MSRawOwnerReport.oracle S) m d c s := by
  letI:=MSRawOwnerReport.oracle S
  exact MSCountedEpochPreparation.compute_value c s (evaluator S c hθ hδ ht s)
    (cleanupJacobi N) (responseJacobi N d) (responseBudget S N d)
    (bounds S c hm hθ hδ ht hR s)

theorem preparation_le (s : Certified c) :
    MSManuscriptSupportedPreparation.budget (params c s.val) ≤ preparation N d := by
  have hP:=params_valid c s
  have hcur:=curvatureBudget_le (params c s.val) hm hθ hδ
    ((norm_nonneg _).trans hP.2.2.2.2.2.2) hR
  have hti : (params c s.val).threshold⁻¹ ≤ thresholdInv N := by
    change c.threshold⁻¹ ≤ _
    rw [ht]
    exact threshold_inverse_le hm
  exact preparation_budget_le _ hP hm (paidSize_inverse_le _ hP hδ hcur hti)

theorem compute_cost (s : Certified c) :
    (compute S c hm hθ hδ ht hR s).cost ≤ work S N d := by
  letI:=MSRawOwnerReport.oracle S
  have hp:=parameters_cost c s
  have hr:=MSCountedEpochPreparation.compute_cost c s (evaluator S c hθ hδ ht s)
    (cleanupJacobi N) (responseJacobi N d) (responseBudget S N d)
    (bounds S c hm hθ hδ ht hR s)
  have hb:=preparation_le c hm hθ hδ ht hR s
  have hw : MSCountedPreparation.roundBudget m (cleanupJacobi N) (responseJacobi N d)
      (responseBudget S N d) ≤ MSCountedPreparation.roundBudget N (cleanupJacobi N)
        (responseJacobi N d) (responseBudget S N d) := by
    unfold MSCountedPreparation.roundBudget
    gcongr
  have hprod:=Nat.mul_le_mul hb hw
  have hsmall : (m+1)^3 ≤ (N+d+1)^3 := Nat.pow_le_pow_left (by omega) _
  have hlarge : (m+d+1)^3 ≤ (N+d+1)^3 := Nat.pow_le_pow_left (by omega) _
  have h1 : 1 ≤ (N+d+1)^3 := Nat.one_le_pow _ _ (by omega)
  dsimp only [compute]
  unfold work
  omega

end MatrixSpencer.MSCountedCompiledPreparation
