import MatrixSpencer.RealRAMMSScalarFormulas
import MatrixSpencer.MSCountedResponse

/-! Counted exact finite-difference tuning. The fixed arithmetic curvature
formula is evaluated at the current owner dimension, followed by the scalar
query circuit. The zero-dimensional case branches before any division by k. -/
noncomputable section
namespace MatrixSpencer.RealRAM.MSResponseScalarSetup
open JacobiIteration (Counted)
open MSManuscriptSupportedGamma (Parameters)
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

def curvature (R : ℝ) (m d k : ℕ) : Counted ℝ :=
  ⟨MSQueryFormula.second.eval (MSQueryFormula.input R k m d),MSQueryFormula.second.cost+5⟩
theorem curvature_value (R : ℝ) (m d k : ℕ) :
    (curvature R m d k).value=MSManuscriptGammaInputBoundScaled.secondCap k d R 1 (1/8192) m :=
  MSQueryFormula.second_eval R k m d

def compute (R : ℝ) (m d k : ℕ) : Counted (ℝ×ℝ) :=
  if k=0 then ⟨(0,0),2⟩ else
    let L:=curvature R m d k
    let s:=MSScalarFormulas.compute m k 0 d L.value 1 1
    ⟨(s.value 3,s.value 4),L.cost+s.cost+15⟩

theorem compute_value (R : ℝ) (m d k : ℕ) :
    (compute R m d k).value=
      (MSManuscriptGammaDifference.stepSize (1/8192)
        (MSManuscriptGammaInputBoundScaled.secondCap k d R 1 (1/8192) m)
        (MSManuscriptGammaMatrix.topPrecision k (4096/Real.sqrt (m:ℝ))),
       MSManuscriptGammaDifference.valueTolerance (1/8192)
        (MSManuscriptGammaInputBoundScaled.secondCap k d R 1 (1/8192) m)
        (MSManuscriptGammaMatrix.topPrecision k (4096/Real.sqrt (m:ℝ)))) := by
  unfold compute
  split_ifs with hk
  · subst k
    norm_num [MSManuscriptGammaDifference.stepSize,MSManuscriptGammaDifference.valueTolerance,
      MSManuscriptGammaMatrix.topPrecision]
  · change (MSScalarFormulas.spacing.eval _,MSScalarFormulas.precision.eval _) = _
    rw [MSScalarFormulas.spacing_eval,MSScalarFormulas.precision_eval,curvature_value]

theorem compute_cost (R : ℝ) (m d k : ℕ) : (compute R m d k).cost≤2100020 := by
  unfold compute
  split_ifs
  · norm_num
  · dsimp only [curvature]
    have h:=MSScalarFormulas.compute_cost m k 0 d
      (MSQueryFormula.second.eval (MSQueryFormula.input R k m d)) 1 1
    nlinarith [MSQueryFormula.second_cost]

def scalars {m d : ℕ} (P : Parameters m d)
    (hθ : P.regularizer=1) (hδ : P.floor=1/8192)
    (ht : P.threshold=4096/Real.sqrt (m:ℝ)) : MSCountedResponse.Scalars P where
  compute := compute P.centerCap m d
  compute_value k := by simpa [MSCountedResponse.tuning,hθ,hδ,ht] using compute_value P.centerCap m d k

theorem scalars_cost {m d : ℕ} (P : Parameters m d)
    (hθ : P.regularizer=1) (hδ : P.floor=1/8192)
    (ht : P.threshold=4096/Real.sqrt (m:ℝ)) (k : ℕ) :
    ((scalars P hθ hδ ht).compute k).cost≤2100020 := compute_cost P.centerCap m d k

/-- Both primitive stages are safe on every positive-dimensional response. -/
theorem positive_execution (R : ℝ) (m d k : ℕ) (hR : 0≤R)
    (hm : 0 < m) (hd : 0 < d) (hk : 0 < k) :
    Expr.Executes (MSQueryFormula.input R k m d) MSQueryFormula.second
      (curvature R m d k).value MSQueryFormula.second.cost ∧
    ∀i, Expr.Executes (MSScalarFormulas.input m k 0 d (curvature R m d k).value 1 1)
      (MSScalarFormulas.circuit.output i)
      ((MSScalarFormulas.compute m k 0 d (curvature R m d k).value 1 1).value i)
      (MSScalarFormulas.circuit.output i).cost := by
  constructor
  · exact Expr.executes_of_valid _ _ (MSQueryFormula.second_valid R k m d hR hd)
  · have hL : 0≤(curvature R m d k).value := by
      rw [curvature_value]
      exact MSManuscriptGammaInputBoundScaled.secondCap_nonneg hR (by norm_num)
    exact MSScalarFormulas.execution m k 0 d _ 1 1 hm hk hd hL (by norm_num) (by norm_num)

end MatrixSpencer.RealRAM.MSResponseScalarSetup
