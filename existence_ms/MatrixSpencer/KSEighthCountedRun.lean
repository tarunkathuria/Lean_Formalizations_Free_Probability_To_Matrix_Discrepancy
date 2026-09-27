import MatrixSpencer.KSEighthCountedCovariance
import MatrixSpencer.KSEighthCountedMovement
import MatrixSpencer.KSOnlinePathRuntime


open Set
open scoped BigOperators
noncomputable section
namespace MatrixSpencer.KSEighthCountedRun
open RealRAM.JacobiIteration KSEighthManuscriptRun KSEighthLiveEnumeration
open KSEighthWalkRun (terminal PreparedState)
open FiniteBranchingTermination
variable {N : ℕ}
attribute [local instance] Classical.propDecidable

structure Operations (C : Controller N) where
  report : KSRetirementRuntime.Report N
  report_value : ∀x,(report x).value=C.report x
  covariance : (s : State C) → ¬terminal s →
    Counted (Matrix (Fin (count s.coeff)) (Fin (count s.coeff)) ℝ)
  covariance_value : ∀s ht,(covariance s ht).value=C.covariance s

theorem prepared_ext {C : Controller N} {s t : State C} (h : s.coeff=t.coeff) : s=t := by
  cases s
  cases t
  cases h
  rfl

def makeState (C : Controller N) (P : Operations C) (x : Fin N → ℝ)
    (hx : x∈ksCube (1/8)) : Counted (State C) := by
  let p := KSEighthCountedPreparation.prepare (1/8) C.ρ C.τ P.report x
  have he : p.value=(KSEighthManuscriptRun.makeState C x hx).coeff := by
    simp only [p,KSEighthCountedPreparation.prepare_value,P.report_value,
      KSEighthManuscriptRun.makeState]
  exact ⟨{ coeff := p.value
           cube := he ▸ (KSEighthManuscriptRun.makeState C x hx).cube
           exhausted := he ▸ (KSEighthManuscriptRun.makeState C x hx).exhausted
           margin := he ▸ (KSEighthManuscriptRun.makeState C x hx).margin },p.cost+2⟩

theorem makeState_value (C : Controller N) (P : Operations C) (x : Fin N → ℝ)
    (hx : x∈ksCube (1/8)) :
    (makeState C P x hx).value=KSEighthManuscriptRun.makeState C x hx := by
  apply prepared_ext
  simp only [makeState,KSEighthCountedPreparation.prepare_value,P.report_value,
    KSEighthManuscriptRun.makeState]

theorem makeState_cost (C : Controller N) (P : Operations C) {Q : ℕ}
    (hQ : ∀x∈ksCube (1/8),(P.report x).cost≤Q) (x : Fin N → ℝ)
    (hx : x∈ksCube (1/8)) :
    (makeState C P x hx).cost≤50*(N+1)^3*(Q+20)+2 := by
  exact Nat.add_le_add_right (KSEighthCountedPreparation.prepare_cost (ρ:=C.ρ)
    (τ:=C.τ) (by norm_num) P.report hQ hx) 2

def activeChild (C : Controller N) (P : Operations C) (s : State C) (ht : ¬terminal s)
    (z : Fin (count s.coeff) × Bool) : Counted (State C) := by
  let Q := P.covariance s ht
  let y := KSEighthCountedMovement.proposal s.coeff Q.value C.stepSize z
  have hy : y.value∈ksCube (1/8) := by
    rw [KSEighthCountedMovement.proposal_value,P.covariance_value]
    exact KSEighthManuscriptMovement.proposal_mem_cube s.cube (C.covariance_posSemidef s)
      (C.covariance_le_one s) (by simpa only [abs_of_pos C.step_pos] using C.step_le) s.margin z
  let p := makeState C P y.value hy
  exact ⟨p.value,Q.cost+y.cost+p.cost+3⟩

theorem activeChild_value (C : Controller N) (P : Operations C) (s : State C) (ht : ¬terminal s)
    (z : Fin (count s.coeff) × Bool) :
    (activeChild C P s ht z).value=KSEighthManuscriptRun.child C s z := by
  simp only [activeChild,makeState_value,KSEighthCountedMovement.proposal_value,
    P.covariance_value,KSEighthManuscriptRun.child]

def childBudget (N Q V : ℕ) : ℕ :=
  V+KSEighthCountedMovement.costBudget N+50*(N+1)^3*(Q+20)+5

theorem activeChild_cost (C : Controller N) (P : Operations C) {Q V : ℕ}
    (hQ : ∀x∈ksCube (1/8),(P.report x).cost≤Q)
    (hV : ∀s ht,(P.covariance s ht).cost≤V) (s : State C) (ht : ¬terminal s)
    (z : Fin (count s.coeff) × Bool) :
    (activeChild C P s ht z).cost≤childBudget N Q V := by
  have hc := hV s ht
  have hm := KSEighthCountedMovement.proposal_cost s.coeff (P.covariance s ht).value C.stepSize z
  have hy : (KSEighthCountedMovement.proposal s.coeff (P.covariance s ht).value C.stepSize z).value∈
      ksCube (1/8) := by
    rw [KSEighthCountedMovement.proposal_value,P.covariance_value]
    exact KSEighthManuscriptMovement.proposal_mem_cube s.cube (C.covariance_posSemidef s)
      (C.covariance_le_one s) (by simpa only [abs_of_pos C.step_pos] using C.step_le) s.margin z
  have hp := makeState_cost C P hQ _ hy
  dsimp only [activeChild,childBudget]
  omega

theorem count_zero_iff (C : Controller N) (s : State C) : count s.coeff=0↔terminal s := by
  constructor
  · intro h
    by_contra ht
    have hh := count_pos_of_not_vertex s.cube ht
    omega
  · intro ht
    change (labels s.coeff).length=0
    rw [List.length_eq_zero_iff]
    unfold labels
    apply List.filter_eq_nil_iff.mpr
    intro i _
    have hi : |s.coeff i|=(1/8:ℝ) := by
      rcases ht i with hi|hi <;> rw [hi] <;> norm_num
    simp [hi]

def test (C : Controller N) (s : State C) : Counted Bool :=
  let l := KSEighthCountedHessian.liveLabels s.coeff
  ⟨decide (l.value.length=0),l.cost+3⟩

theorem test_value (C : Controller N) (s : State C) : (test C s).value=decide (terminal s) := by
  simp only [test,KSEighthCountedHessian.liveLabels_value]
  change decide (count s.coeff=0)=_
  simp only [count_zero_iff]

theorem test_cost (C : Controller N) (s : State C) : (test C s).cost≤23*N+5 := by
  have h := KSEighthCountedHessian.liveLabels_cost s.coeff
  dsimp only [test]
  omega

def childCertificate (C : Controller N) (P : Operations C) {Q V : ℕ}
    (hQ : ∀x∈ksCube (1/8),(P.report x).cost≤Q)
    (hV : ∀s ht,(P.covariance s ht).cost≤V) (s : State C) :
    ∀i : Fin (KSEighthManuscriptRun.step C s).arity,
      {r : Counted (State C) // r.value=(KSEighthManuscriptRun.step C s).child i ∧
        (¬terminal s → r.cost≤childBudget N Q V)} := by
  generalize he : KSEighthManuscriptRun.step C s = b
  have hb : b=KSEighthManuscriptRun.step C s := he.symm
  unfold KSEighthManuscriptRun.step at hb
  split at hb
  · rename_i ht
    rw [hb]
    intro i
    exact ⟨⟨s,1⟩,rfl,fun hn=>False.elim (hn ht)⟩
  · rename_i ht
    rw [hb]
    intro i
    let z := (Fintype.equivFin (Fin (count s.coeff) × Bool)).symm i
    exact ⟨activeChild C P s ht z,activeChild_value C P s ht z,
      fun _=>activeChild_cost C P hQ hV s ht z⟩

def evaluator (C : Controller N) (P : Operations C) {Q V : ℕ}
    (hQ : ∀x∈ksCube (1/8),(P.report x).cost≤Q)
    (hV : ∀s ht,(P.covariance s ht).cost≤V) :
    KSOnlinePathRuntime.Evaluator terminal (KSEighthManuscriptRun.step C) where
  test := test C
  test_correct := test_value C
  child := fun s i=>(childCertificate C P hQ hV s i).val
  child_correct := fun s i=>(childCertificate C P hQ hV s i).property.1

theorem leaf_execution (C : Controller N) (P : Operations C) {Q V : ℕ}
    (hQ : ∀x∈ksCube (1/8),(P.report x).cost≤Q)
    (hV : ∀s ht,(P.covariance s ht).cost≤V) (T : ℕ) (s : State C)
    (l : (KSEighthManuscriptRun.run C T s).Leaves) :
    ∃k r,KSOnlinePathRuntime.Executes (evaluator C P hQ hV) T s
      ((KSEighthManuscriptRun.run C T s).leafState l) k r ∧
      k≤T*((23*N+5)+childBudget N Q V+3)+(23*N+5)+2 ∧ r≤T :=
  KSOnlinePathRuntime.leaf_execution_bounded (evaluator C P hQ hV) (test_cost C)
    (fun s hs i=>(childCertificate C P hQ hV s i).property.2 hs) T s l

end MatrixSpencer.KSEighthCountedRun
