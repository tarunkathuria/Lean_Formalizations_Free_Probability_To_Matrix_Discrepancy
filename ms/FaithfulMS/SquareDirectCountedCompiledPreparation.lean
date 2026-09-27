import FaithfulMS.SquareDirectCountedEpochStep
import MatrixSpencer.MSCountedCompiledPreparation

/-! Counted direct-density preparation at the actual epoch center. The scalar
parameter and cleanup budgets are computed as before; the density response
implementation is supplied by the separately verified direct SDP compiler. -/
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace FaithfulMS.SquareDirectCountedCompiledPreparation
open MatrixSpencer RealRAM
open MatrixSpencer.RealRAM.JacobiIteration (Counted)
open MSManuscriptNumericalEpochRun (Config Certified params params_valid)
open MSManuscriptPolynomialQueryCurvature MSManuscriptPolynomialQueryParameters
open MSManuscriptPolynomialQueryMagnitude MSManuscriptPolynomialQueryCleanup
variable [SquareDirectOracle.Oracle] {m N d : ℕ}
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

abbrev parameters := @MSCountedCompiledPreparation.parameters
abbrev parameters_value := @MSCountedCompiledPreparation.parameters_value
abbrev parameters_cost := @MSCountedCompiledPreparation.parameters_cost
abbrev preparation_le := @MSCountedCompiledPreparation.preparation_le

def work (R N d : ℕ) : ℕ :=
  preparation N d*SquareDirectCountedPreparation.roundBudget N (cleanupJacobi N) 0 R+
    100000*(N+d+1)^3

variable (c : Config m d) (hm : m ≤ N) (hθ : c.regularizer=1) (hδ : c.floor=1/8192)
  (ht : c.threshold=4096/Real.sqrt (m:ℝ))
  (hR : MSManuscriptEpochInput.centerCap c.offset (N:=m) ≤ center N d)
  (R : ℕ) (E : ∀ s : Certified c, SquareDirectCountedPreparation.Evaluator (params c s.val))
  (hE : ∀ s O, MSManuscriptSupportedPreparation.State (params c s.val) O →
    ((E s).response O).cost ≤ R)

include hm hδ hE in
theorem bounds (s : Certified c) :
    SquareDirectCountedPreparation.Bounds (params c s.val) (E s) (cleanupJacobi N) 0 R :=
  SquareDirectCountedBounds.bounds _ (params_valid c s) hm hδ (E s) R (hE s)

def compute (s : Certified c) : Counted (Certified c) :=
  let p := parameters c s
  let r := SquareDirectCountedEpochPreparation.compute c s (E s)
    (cleanupJacobi N) 0 R (bounds c hm hδ R E hE s)
  ⟨r.value, p.cost+r.cost+2⟩

theorem compute_value (s : Certified c) :
    (compute c hm hδ R E hE s).value = SquareDirectEpochRun.prepare c s :=
  SquareDirectCountedEpochPreparation.compute_value c s (E s)
    (cleanupJacobi N) 0 R (bounds c hm hδ R E hE s)

include hm hθ hδ ht hR in
theorem compute_cost (s : Certified c) :
    (compute c hm hδ R E hE s).cost ≤ work R N d := by
  have hp := parameters_cost c s
  change (parameters c s).cost ≤ 100*(m+d+1)^3 at hp
  have hr := SquareDirectCountedEpochPreparation.compute_cost c s (E s)
    (cleanupJacobi N) 0 R (bounds c hm hδ R E hE s)
  have hb := preparation_le c hm hθ hδ ht hR s
  have hw : SquareDirectCountedPreparation.roundBudget m (cleanupJacobi N) 0 R ≤
      SquareDirectCountedPreparation.roundBudget N (cleanupJacobi N) 0 R := by
    unfold SquareDirectCountedPreparation.roundBudget
    gcongr
  have hprod := Nat.mul_le_mul hb hw
  have hsmall : (m+1)^3 ≤ (N+d+1)^3 := Nat.pow_le_pow_left (by omega) _
  have hlarge : (m+d+1)^3 ≤ (N+d+1)^3 := Nat.pow_le_pow_left (by omega) _
  have h1 : 1 ≤ (N+d+1)^3 := Nat.one_le_pow _ _ (by omega)
  dsimp only [compute]
  unfold work
  omega

end FaithfulMS.SquareDirectCountedCompiledPreparation
