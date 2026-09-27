import MatrixSpencer.KSFullConvexOracleAlgorithm
import MatrixSpencer.KSFullConvexOracleReportBounds
import MatrixSpencer.KSRetirementRuntime
import MatrixSpencer.KSOnlinePathRuntime
import MatrixSpencer.KSJacobiPolynomialBounds
import MatrixSpencer.RealRAMKSLiveCoordinates
import MatrixSpencer.RealRAMJacobiRayleigh

/-! Counted primitive composition of the full-cube convex-solver walk.
The report evaluator includes construction of its exact convex query; its
implementation belongs to the shared direct-SDP compilation layer. Every
other local operation is explicitly composed from finite scalar/array loops.
-/
open Matrix Set
open scoped BigOperators
noncomputable section
namespace MatrixSpencer.KSFullConvexRuntime
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
open RealRAM.JacobiIteration (Counted)
open KSFullManuscriptParameters
attribute [local instance] Classical.propDecidable
variable {N d : ℕ}

structure ValueEvaluator (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ)
    (δ η θ : ℝ) (hd : 0<d) where
  report : ℝ → (Fin N → ℝ) → Counted ℝ
  correct : ∀ ν x, (report ν x).value=KSFullConvexOracleValue.stateReport O v δ η θ hd ν x

variable {O : KSConvexValueOracle.Solver} {v : Fin N → Fin d → ℂ}
variable {δ η θ : ℝ} {hd : 0<d}

def faceReport (E : ValueEvaluator O v δ η θ hd) (M : ℝ) (x : Fin N → ℝ)
    (z : KSNumericalHessian.Space (KSLiveEnumeration.count x)) : Counted ℝ :=
  let p := RealRAM.KSLiveCoordinates.face x z
  let r := E.report (valueTolerance N δ M) p.value
  ⟨r.value,p.cost+r.cost+2⟩

theorem faceReport_value (E : ValueEvaluator O v δ η θ hd) (M : ℝ) (x : Fin N → ℝ)
    (z : KSNumericalHessian.Space (KSLiveEnumeration.count x)) :
    (faceReport E M x z).value=KSFullConvexOracleQueries.faceReport O v δ η θ hd M x z := by
  simp only [faceReport,E.correct,RealRAM.KSLiveCoordinates.face_value]
  rfl

theorem faceReport_cost (E : ValueEvaluator O v δ η θ hd) (M : ℝ) {Q : ℕ}
    (hQ : ∀x∈ksCube 1,(E.report (valueTolerance N δ M) x).cost≤Q)
    {x : Fin N → ℝ} (hx : x∈ksCube 1)
    (hmargin : ∀i, |x i|<1 → δ≤1-|x i|)
    (z : KSNumericalHessian.Space (KSLiveEnumeration.count x)) (hz : ‖z‖<δ) :
    (faceReport E M x z).cost≤Q+26*(N+1)^2+2 := by
  have hc : (RealRAM.KSLiveCoordinates.face x z).value∈ksCube 1 := by
    rw [RealRAM.KSLiveCoordinates.face_value]
    exact KSFullManuscriptLiveCoordinates.face_mem_cube hx z hmargin hz
  have h := hQ _ hc
  have h2 := RealRAM.KSLiveCoordinates.face_cost x z
  dsimp [faceReport]
  omega

def matrix (E : ValueEvaluator O v δ η θ hd) (M : ℝ) (x : Fin N → ℝ) :
    Counted (Matrix (Fin (KSLiveEnumeration.count x)) (Fin (KSLiveEnumeration.count x)) ℝ) :=
  let a := RealRAM.FullHessian.matrix (faceReport E M x) (queryStep N δ M)
  let w := RealRAM.KSLiveCoordinates.weights x
  let b := RealRAM.FullHessian.weighted w.value a.value
  ⟨b.value,a.cost+w.cost+b.cost+3⟩

theorem matrix_value (E : ValueEvaluator O v δ η θ hd) (M : ℝ) (x : Fin N → ℝ) :
    (matrix E M x).value=KSFullManuscriptHessian.weighted
      (KSFullManuscriptLiveCoordinates.weight x)
      (KSFullManuscriptHessian.matrixReport
        (KSFullConvexOracleQueries.faceReport O v δ η θ hd M x) 0 (queryStep N δ M)) := by
  simp only [matrix,RealRAM.FullHessian.weighted_value,RealRAM.KSLiveCoordinates.weights_value,
    RealRAM.FullHessian.matrix_value,faceReport_value]

theorem matrix_cost (E : ValueEvaluator O v δ η θ hd) (M : ℝ)
    (hN : 0<N) (hδ : 0<δ) (hM : 0<M) {Q : ℕ}
    (hQ : ∀x∈ksCube 1,(E.report (valueTolerance N δ M) x).cost≤Q)
    {x : Fin N → ℝ} (hx : x∈ksCube 1)
    (hmargin : ∀i, |x i|<1 → δ≤1-|x i|) :
    (matrix E M x).cost≤200*(N+1)^4*(Q+1) := by
  have ht := queryStep_pos hN hδ hM
  have htR := KSFullManuscriptQueries.queryStep_le_quarter N (M := M) hδ.le
  have hr : ∀z, ‖z‖≤2*|queryStep N δ M| →
      (faceReport E M x z).cost≤Q+26*(N+1)^2+2 := by
    intro z hz
    rw [abs_of_pos ht] at hz
    exact faceReport_cost E M hQ hx hmargin z (by linarith)
  have ha := RealRAM.FullHessian.matrix_cost (faceReport E M x) (queryStep N δ M) hr
  have hw := RealRAM.KSLiveCoordinates.weights_cost x
  have hm := RealRAM.KSLiveCoordinates.count_le x
  have hb := RealRAM.FullHessian.weighted_cost (RealRAM.KSLiveCoordinates.weights x).value
    (RealRAM.FullHessian.matrix (faceReport E M x) (queryStep N δ M)).value
  have ha' : (RealRAM.FullHessian.matrix (faceReport E M x) (queryStep N δ M)).cost≤
      N^2*(4*(Q+26*(N+1)^2+2)+100*(N+1)+6)+1 := ha.trans (by gcongr)
  have hb' : (RealRAM.FullHessian.weighted (RealRAM.KSLiveCoordinates.weights x).value
      (RealRAM.FullHessian.matrix (faceReport E M x) (queryStep N δ M)).value).cost≤12*N^2+1 := by
    rw [hb]
    gcongr
  dsimp only [matrix]
  calc
    _ ≤ (N^2*(4*(Q+26*(N+1)^2+2)+100*(N+1)+6)+1)+(23*N+3)+(12*N^2+1)+3 := by omega
    _ ≤ _ := by ring_nf; omega

def liveDirection (E : ValueEvaluator O v δ η θ hd) (M : ℝ) (x : Fin N → ℝ)
    (hm : 0<KSLiveEnumeration.count x) (cap : ℕ) :
    Counted (KSNumericalHessian.Space (KSLiveEnumeration.count x)) :=
  let a := matrix E M x
  let z := RealRAM.JacobiRayleigh.output a.value (curvatureTolerance N δ) cap hm
  ⟨z.value,a.cost+z.cost+2⟩

theorem liveDirection_value (E : ValueEvaluator O v δ η θ hd) (M : ℝ) (x : Fin N → ℝ)
    (hm : 0<KSLiveEnumeration.count x) (cap : ℕ)
    (hcap : KSJacobiIteration.denominator (KSLiveEnumeration.count x)*
      KSJacobiStep.offDiagonalEnergy (matrix E M x).value/(curvatureTolerance N δ)^2≤cap) :
    (liveDirection E M x hm cap).value=
      KSFullManuscriptHessian.output (KSFullConvexOracleQueries.faceReport O v δ η θ hd M x)
        0 (KSFullManuscriptLiveCoordinates.weight x) N δ M hm := by
  change (RealRAM.JacobiRayleigh.output (matrix E M x).value (curvatureTolerance N δ) cap hm).value = _
  rw [RealRAM.JacobiRayleigh.output_value _ _ _ _ hcap,matrix_value]
  rfl

theorem liveDirection_cost (E : ValueEvaluator O v δ η θ hd) (M : ℝ)
    (hN : 0<N) (hδ : 0<δ) (hM : 0<M) {Q : ℕ}
    (hQ : ∀x∈ksCube 1,(E.report (valueTolerance N δ M) x).cost≤Q)
    {x : Fin N → ℝ} (hx : x∈ksCube 1)
    (hmargin : ∀i, |x i|<1 → δ≤1-|x i|)
    (hm : 0<KSLiveEnumeration.count x) (cap : ℕ) :
    (liveDirection E M x hm cap).cost≤1000*(N+1)^4*(Q+cap+1) := by
  have ha := matrix_cost E M hN hδ hM hQ hx hmargin
  have hz := RealRAM.JacobiRayleigh.output_cost (matrix E M x).value (curvatureTolerance N δ) cap hm
  have hcount := RealRAM.KSLiveCoordinates.count_le x
  have hz' : (RealRAM.JacobiRayleigh.output (matrix E M x).value (curvatureTolerance N δ) cap hm).cost≤
      600*(cap+1)*(N+1)^4 := hz.trans (by gcongr <;> omega)
  dsimp only [liveDirection]
  nlinarith [one_le_pow₀ (show 1≤N+1 by omega) (n := 4)]


def signScan (x : Fin N → ℝ) : List (Fin N) → Counted Bool
  | [] => ⟨true,1⟩
  | i::is =>
    let t := signScan x is
    ⟨(decide (x i=1) || decide (x i= -1)) && t.value,t.cost+12⟩

theorem signScan_value (x : Fin N → ℝ) (is : List (Fin N)) :
    (signScan x is).value=is.all (fun i => decide (x i=1) || decide (x i= -1)) := by
  induction is with
  | nil => rfl
  | cons i is ih => simp [signScan,ih]

theorem signScan_cost (x : Fin N → ℝ) (is : List (Fin N)) :
    (signScan x is).cost=12*is.length+1 := by
  induction is with
  | nil => rfl
  | cons i is ih => simp [signScan,ih]; omega

def terminalTest (x : Fin N → ℝ) : Counted Bool :=
  let t := signScan x (List.finRange N)
  ⟨t.value,t.cost+3*N+1⟩

theorem terminalTest_value (x : Fin N → ℝ) :
    (terminalTest x).value=decide (∀i,IsSign (x i)) := by
  apply Bool.eq_iff_iff.mpr
  simp [terminalTest,signScan_value,List.all_eq_true,IsSign]

theorem terminalTest_cost (x : Fin N → ℝ) : (terminalTest x).cost=15*N+2 := by
  simp [terminalTest,signScan_cost]; omega

variable [Nonempty (Fin d)]

abbrev C (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ)
    (hN : 0<N) {δ η θ M : ℝ} (hδ : 0<δ) (hη : 0<η) (hθ : 0<θ) (hM : 0<M) (hd : 0<d) :=
  KSFullConvexOracleController.controller O v hN hδ hη hθ hM hd

theorem prepared_ext {δ η : ℝ} {report : (Fin N → ℝ) → ℝ}
    {s t : KSDebitWalkRun.PreparedState N δ η report} (h : s.coeff=t.coeff) : s=t := by
  cases s
  cases t
  cases h
  rfl

def retag (C : KSDebitWalkRun.Controller N (Fin d)) (s : KSDebitWalkRun.State C)
    (y : Fin N → ℝ) (hy : y=s.coeff) : KSDebitWalkRun.State C where
  coeff := y
  cube := by rw [hy]; exact s.cube
  exhausted := by rw [hy]; exact s.exhausted
  margin := by rw [hy]; exact s.margin

theorem retag_value (C : KSDebitWalkRun.Controller N (Fin d)) (s : KSDebitWalkRun.State C)
    (y : Fin N → ℝ) (hy : y=s.coeff) : retag C s y hy=s := prepared_ext hy

def prepare (E : ValueEvaluator O v δ η θ hd) (hN : 0<N) {M : ℝ}
    (hδ : 0<δ) (hη : 0<η) (hθ : 0<θ) (hM : 0<M)
    (x : Fin N → ℝ) (hx : x∈ksCube 1) : Counted (KSDebitWalkRun.State (C O v hN hδ hη hθ hM hd)) :=
  let p := KSRetirementRuntime.prepare 1 (-η) (E.report (η/8)) N x
  have hp : p.value=(KSDebitWalkRun.makeState (C O v hN hδ hη hθ hM hd) x hx).coeff := by
    simp only [p,KSRetirementRuntime.prepare_value,E.correct]
    rfl
  ⟨retag _ (KSDebitWalkRun.makeState (C O v hN hδ hη hθ hM hd) x hx) p.value hp,p.cost+2⟩

theorem prepare_value (E : ValueEvaluator O v δ η θ hd) (hN : 0<N) {M : ℝ}
    (hδ : 0<δ) (hη : 0<η) (hθ : 0<θ) (hM : 0<M)
    (x : Fin N → ℝ) (hx : x∈ksCube 1) :
    (prepare E hN hδ hη hθ hM x hx).value=KSDebitWalkRun.makeState (C O v hN hδ hη hθ hM hd) x hx := by
  simp only [prepare,retag_value]

theorem prepare_cost (E : ValueEvaluator O v δ η θ hd) (hN : 0<N) {M : ℝ}
    (hδ : 0<δ) (hη : 0<η) (hθ : 0<θ) (hM : 0<M) {Q : ℕ}
    (hQ : ∀x∈ksCube 1,(E.report (η/8) x).cost≤Q)
    (x : Fin N → ℝ) (hx : x∈ksCube 1) :
    (prepare E hN hδ hη hθ hM x hx).cost≤6*(N+1)^3*(Q+20)+2 := by
  exact Nat.add_le_add_right (KSRetirementRuntime.preparation_cost (by norm_num) (E.report (η/8)) hQ hx) 2

/-- Intermediate cap condition discharged from the primitive input below. -/
def CapValid (E : ValueEvaluator O v δ η θ hd) (M : ℝ) (cap : ℕ) : Prop :=
  ∀x∈ksCube 1, (∀i, |x i|<1 → δ≤1-|x i|) →
    KSJacobiIteration.denominator (KSLiveEnumeration.count x)*
      KSJacobiStep.offDiagonalEnergy (matrix E M x).value/(curvatureTolerance N δ)^2≤cap

def step (E : ValueEvaluator O v δ η θ hd) (hN : 0<N) {M : ℝ}
    (hδ : 0<δ) (hη : 0<η) (hθ : 0<θ) (hM : 0<M) (cap : ℕ) (hcap : CapValid E M cap)
    (s : KSDebitWalkRun.State (C O v hN hδ hη hθ hM hd)) (b : Bool) :
    Counted (KSDebitWalkRun.State (C O v hN hδ hη hθ hM hd)) :=
  if ht : KSDebitWalkRun.terminal s then ⟨s,(terminalTest s.coeff).cost+2⟩ else
    let z := liveDirection E M s.coeff (KSLiveEnumeration.count_pos_of_not_vertex s.cube ht) cap
    let e := RealRAM.KSLiveCoordinates.extension s.coeff z.value
    let y := RealRAM.KSLiveCoordinates.movement s.coeff e.value
      (KSDebitWalkRun.signedStep (C O v hN hδ hη hθ hM hd) b)
    have he : e.value=(C O v hN hδ hη hθ hM hd).direction s := by
      rw [RealRAM.KSLiveCoordinates.extension_value,liveDirection_value E M s.coeff _ cap
        (hcap s.coeff s.cube (fun i hi => (s.margin i hi).le))]
      simp only [C,KSFullConvexOracleController.controller,
        KSFullConvexOracleController.numericalDirection,dif_neg ht,
        KSFullConvexOracleController.liveDirection]
    have hy : y.value∈ksCube 1 := by
      rw [RealRAM.KSLiveCoordinates.movement_value,he]
      exact KSDebitMovement.proposal_mem_cube s.coeff s.cube _
        ((C O v hN hδ hη hθ hM hd).direction_norm s ht) hδ
        (KSDebitWalkRun.signedStep_abs_le _ b) s.margin
    let p := prepare E hN hδ hη hθ hM y.value hy
    ⟨p.value,(terminalTest s.coeff).cost+z.cost+e.cost+y.cost+p.cost+8⟩

theorem step_value (E : ValueEvaluator O v δ η θ hd) (hN : 0<N) {M : ℝ}
    (hδ : 0<δ) (hη : 0<η) (hθ : 0<θ) (hM : 0<M) (cap : ℕ) (hcap : CapValid E M cap)
    (s : KSDebitWalkRun.State (C O v hN hδ hη hθ hM hd)) (b : Bool) :
    (step E hN hδ hη hθ hM cap hcap s b).value=KSDebitWalkRun.step (C O v hN hδ hη hθ hM hd) s b := by
  by_cases ht : KSDebitWalkRun.terminal s
  · simp [step,ht,KSDebitWalkRun.step_terminal _ s ht b]
  · apply prepared_ext
    simp only [step,dif_neg ht,prepare_value,KSDebitWalkRun.step_active_coeff _ s ht b,
      KSDebitWalkRun.makeState,RealRAM.KSLiveCoordinates.movement_value,
      RealRAM.KSLiveCoordinates.extension_value]
    rw [liveDirection_value E M s.coeff _ cap (hcap s.coeff s.cube (fun i hi => (s.margin i hi).le))]
    simp only [C,KSFullConvexOracleController.controller,
      KSFullConvexOracleController.numericalDirection,dif_neg ht,
      KSFullConvexOracleController.liveDirection]

theorem step_cost (E : ValueEvaluator O v δ η θ hd) (hN : 0<N) {M : ℝ}
    (hδ : 0<δ) (hη : 0<η) (hθ : 0<θ) (hM : 0<M) (cap : ℕ) (hcap : CapValid E M cap)
    {Q : ℕ} (hQstate : ∀x∈ksCube 1,(E.report (η/8) x).cost≤Q)
    (hQquery : ∀x∈ksCube 1,(E.report (valueTolerance N δ M) x).cost≤Q)
    (s : KSDebitWalkRun.State (C O v hN hδ hη hθ hM hd)) (b : Bool) :
    (step E hN hδ hη hθ hM cap hcap s b).cost≤2000*(N+1)^4*(Q+cap+20) := by
  by_cases ht : KSDebitWalkRun.terminal s
  · simp only [step,dif_pos ht,terminalTest_cost]
    ring_nf
    omega
  · let z := liveDirection E M s.coeff (KSLiveEnumeration.count_pos_of_not_vertex s.cube ht) cap
    let e := RealRAM.KSLiveCoordinates.extension s.coeff z.value
    let y := RealRAM.KSLiveCoordinates.movement s.coeff e.value
      (KSDebitWalkRun.signedStep (C O v hN hδ hη hθ hM hd) b)
    have heq : e.value=(C O v hN hδ hη hθ hM hd).direction s := by
      rw [RealRAM.KSLiveCoordinates.extension_value,liveDirection_value E M s.coeff _ cap
        (hcap s.coeff s.cube (fun i hi => (s.margin i hi).le))]
      simp only [C,KSFullConvexOracleController.controller,
        KSFullConvexOracleController.numericalDirection,dif_neg ht,
        KSFullConvexOracleController.liveDirection]
    have hyc : y.value∈ksCube 1 := by
      rw [RealRAM.KSLiveCoordinates.movement_value,heq]
      exact KSDebitMovement.proposal_mem_cube s.coeff s.cube _
        ((C O v hN hδ hη hθ hM hd).direction_norm s ht) hδ
        (KSDebitWalkRun.signedStep_abs_le _ b) s.margin
    have hz := liveDirection_cost E M hN hδ hM hQquery s.cube
      (fun i hi => (s.margin i hi).le) (KSLiveEnumeration.count_pos_of_not_vertex s.cube ht) cap
    have he := RealRAM.KSLiveCoordinates.extension_cost s.coeff z.value
    have hy := RealRAM.KSLiveCoordinates.movement_cost s.coeff e.value
      (KSDebitWalkRun.signedStep (C O v hN hδ hη hθ hM hd) b)
    have hp := prepare_cost E hN hδ hη hθ hM hQstate y.value hyc
    change z.cost≤_ at hz
    change e.cost≤_ at he
    change y.cost=_ at hy
    simp only [step,dif_neg ht]
    change (terminalTest s.coeff).cost+z.cost+e.cost+y.cost+
      (prepare E hN hδ hη hθ hM y.value hyc).cost+8≤_
    rw [terminalTest_cost]
    calc
      _ ≤ (15*N+2)+1000*(N+1)^4*(Q+cap+1)+20*(N+1)^2+(16*N+1)+
        (6*(N+1)^3*(Q+20)+2)+8 := by omega
      _ ≤ _ := by ring_nf; omega



def evaluator (E : ValueEvaluator O v δ η θ hd) (hN : 0<N) {M : ℝ}
    (hδ : 0<δ) (hη : 0<η) (hθ : 0<θ) (hM : 0<M) (cap : ℕ) (hcap : CapValid E M cap) :
    KSOnlinePathRuntime.Evaluator KSDebitWalkRun.terminal
      (KSFiniteCoinRun.coinTransition (KSDebitWalkRun.step (C O v hN hδ hη hθ hM hd))) where
  test s := terminalTest s.coeff
  test_correct s := by
    apply Bool.eq_iff_iff.mpr
    rw [terminalTest_value]
    simp only [decide_eq_true_eq]
    exact (KSDebitWalkRun.terminal_iff_full_signing s).symm
  child s i := step E hN hδ hη hθ hM cap hcap s (decide (i.val=0))
  child_correct s i := step_value E hN hδ hη hθ hM cap hcap s _

theorem leaf_execution_bounded (E : ValueEvaluator O v δ η θ hd) (hN : 0<N) {M : ℝ}
    (hδ : 0<δ) (hη : 0<η) (hθ : 0<θ) (hM : 0<M) (cap : ℕ) (hcap : CapValid E M cap)
    {Q : ℕ} (hQstate : ∀x∈ksCube 1,(E.report (η/8) x).cost≤Q)
    (hQquery : ∀x∈ksCube 1,(E.report (valueTolerance N δ M) x).cost≤Q)
    (T : ℕ) (s : KSDebitWalkRun.State (C O v hN hδ hη hθ hM hd))
    (l : (KSDebitWalkRun.run (C O v hN hδ hη hθ hM hd) T s).Leaves) :
    ∃ k r, KSOnlinePathRuntime.Executes (evaluator E hN hδ hη hθ hM cap hcap) T s
      ((KSDebitWalkRun.run (C O v hN hδ hη hθ hM hd) T s).leafState l) k r ∧
      k≤T*((15*N+2)+2000*(N+1)^4*(Q+cap+20)+3)+(15*N+2)+2 ∧ r≤T := by
  exact KSOnlinePathRuntime.coin_leaf_execution_bounded (evaluator E hN hδ hη hθ hM cap hcap)
    (fun s => (terminalTest_cost s.coeff).le)
    (fun s _ i => step_cost E hN hδ hη hθ hM cap hcap hQstate hQquery s (decide (i.val=0))) T s l

/-- No scalar cap hypothesis remains at the original Parseval inputs. -/
theorem actual_cap (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ) (hd : 0<d)
    (hp : (∑i,KSRankOne.atom (v i))=1)
    (E : ValueEvaluator O v (Real.sqrt (KSEighthManuscriptPreprocess.epsilon v))
      (Real.sqrt (KSEighthManuscriptPreprocess.epsilon v)/(N:ℝ))
      (ksRegularizerScale (KSEighthManuscriptPreprocess.epsilon v) (Fin d)) hd) :
    CapValid E (KSFullConvexOracleAlgorithm.taylorBudget v (KSEighthManuscriptPreprocess.epsilon v))
      (KSJacobiPolynomialBounds.fullJacobi N d) := by
  intro x hx hm
  rw [matrix_value]
  have h := KSJacobiPolynomialBounds.full_iterationCount_le v hd hp
    (RealRAM.KSLiveCoordinates.count_le x)
    (KSFullConvexOracleQueries.faceReport O v
      (Real.sqrt (KSEighthManuscriptPreprocess.epsilon v))
      (Real.sqrt (KSEighthManuscriptPreprocess.epsilon v)/(N:ℝ))
      (ksRegularizerScale (KSEighthManuscriptPreprocess.epsilon v) (Fin d)) hd
      (KSFullConvexOracleAlgorithm.taylorBudget v (KSEighthManuscriptPreprocess.epsilon v)) x)
    (fun z hz => KSFullConvexOracleReportBounds.full_faceReport_abs O v hd hp hx hm
      (KSFullConvexOracleAlgorithm.taylorBudget_pos v
        (KSManuscriptInputPolynomialParameters.labels_pos v hd hp)
        (KSEighthManuscriptPreprocess.epsilon_pos v hd hp)) z hz)
    (KSFullManuscriptLiveCoordinates.weight x) (KSFullManuscriptLiveCoordinates.weight_le_one x)
  exact (Nat.le_ceil _).trans (Nat.cast_le.mpr h)

end MatrixSpencer.KSFullConvexRuntime
