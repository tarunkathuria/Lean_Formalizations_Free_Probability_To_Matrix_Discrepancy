import MatrixSpencer.KSOnlinePathRuntime
import MatrixSpencer.KSDebitWalkRetry

/-! Sequential first-success retries, including online trial executions,
the actual acceptance predicate, output copying and retry control. Products
of hypothetical draws specify the random law; later trials are not executed
after acceptance. -/
noncomputable section
namespace MatrixSpencer.KSCountedRetry
open RealRAM.JacobiIteration (Counted)
open KSEighthManuscriptRetry (Draws)
variable {L State Output : Type}

inductive Executes (trial : L → ℕ → ℕ → Prop) (state : L → State)
    (accept : State → Counted Bool) (output : State → Counted Output) :
    (r : ℕ) → Draws L r → Option Output → ℕ → ℕ → Prop where
  | exhausted (z : Draws L 0) : Executes trial state accept output 0 z none 1 0
  | accepted {r : ℕ} (z : Draws L (r+1)) {k draws : ℕ} :
      trial z.1 k draws → (accept (state z.1)).value=true →
      Executes trial state accept output (r+1) z (some (output (state z.1)).value)
        (k+(accept (state z.1)).cost+(output (state z.1)).cost+3) draws
  | rejected {r : ℕ} (z : Draws L (r+1)) {k draws rest extra : ℕ} {result : Option Output} :
      trial z.1 k draws → (accept (state z.1)).value=false →
      Executes trial state accept output r z.2 result rest extra →
      Executes trial state accept output (r+1) z result
        (k+(accept (state z.1)).cost+rest+3) (draws+extra)

theorem executes_result {trial : L → ℕ → ℕ → Prop} {state : L → State}
    {accept : State → Counted Bool} {output : State → Counted Output}
    {r k draws : ℕ} {z : Draws L r} {result : Option Output}
    (h : Executes trial state accept output r z result k draws) :
    result=KSEighthManuscriptRetry.firstAccepted (fun l => (output (state l)).value)
      (fun l => (accept (state l)).value) r z := by
  induction h with
  | exhausted z => rfl
  | accepted z ht ha => simp only [KSEighthManuscriptRetry.firstAccepted,ha,↓reduceIte]
  | rejected z ht ha hr ih => simp only [KSEighthManuscriptRetry.firstAccepted,ha,↓reduceIte]; exact ih

theorem executes_budget {trial : L → ℕ → ℕ → Prop} {state : L → State}
    {accept : State → Counted Bool} {output : State → Counted Output}
    {B A S T : ℕ}
    (htrial : ∀ l k draws, trial l k draws → k≤B ∧ draws≤T)
    (haccept : ∀ l, (accept (state l)).cost≤A)
    (houtput : ∀ l, (output (state l)).cost≤S)
    {r k draws : ℕ} {z : Draws L r} {result : Option Output}
    (h : Executes trial state accept output r z result k draws) :
    k≤r*(B+A+S+3)+1 ∧ draws≤r*T := by
  induction h with
  | exhausted z => simp
  | @accepted r z k draws ht ha =>
    have hh := htrial z.1 k draws ht
    have ha := haccept z.1
    have ho := houtput z.1
    constructor <;> nlinarith [Nat.zero_le (r*(B+A+S+3)),Nat.zero_le (r*T)]
  | @rejected r z k draws rest extra result ht ha hr ih =>
    have hh := htrial z.1 k draws ht
    have ha := haccept z.1
    constructor <;> nlinarith [Nat.zero_le S]

/-- Replay an arbitrary prospective draw sequence, evaluating only inspected
trials. The bound on each trial comes from its concrete online walk. -/
theorem exists_execution (trial : L → ℕ → ℕ → Prop) (state : L → State)
    (accept : State → Counted Bool) (output : State → Counted Output)
    (htrial : ∀ l, ∃ k draws, trial l k draws) (r : ℕ) (z : Draws L r) :
    ∃ k draws, Executes trial state accept output r z
      (KSEighthManuscriptRetry.firstAccepted (fun l => (output (state l)).value)
        (fun l => (accept (state l)).value) r z) k draws := by
  induction r with
  | zero => exact ⟨1,0,Executes.exhausted z⟩
  | succ r ih =>
    obtain ⟨k,draws,ht⟩ := htrial z.1
    cases ha : (accept (state z.1)).value with
    | false =>
      obtain ⟨rest,extra,hr⟩ := ih z.2
      refine ⟨k+(accept (state z.1)).cost+rest+3,draws+extra,?_⟩
      simpa only [KSEighthManuscriptRetry.firstAccepted,ha,↓reduceIte] using
        Executes.rejected z ht ha hr
    | true =>
      refine ⟨k+(accept (state z.1)).cost+(output (state z.1)).cost+3,draws,?_⟩
      simpa only [KSEighthManuscriptRetry.firstAccepted,ha,↓reduceIte] using
        Executes.accepted (trial := trial) (output := output) z ht ha

theorem exists_execution_bounded (trial : L → ℕ → ℕ → Prop) (state : L → State)
    (accept : State → Counted Bool) (output : State → Counted Output)
    {B A S T : ℕ}
    (hexists : ∀ l, ∃ k draws, trial l k draws)
    (htrial : ∀ l k draws, trial l k draws → k≤B ∧ draws≤T)
    (haccept : ∀ l, (accept (state l)).cost≤A)
    (houtput : ∀ l, (output (state l)).cost≤S) (r : ℕ) (z : Draws L r) :
    ∃ k draws, Executes trial state accept output r z
      (KSEighthManuscriptRetry.firstAccepted (fun l => (output (state l)).value)
        (fun l => (accept (state l)).value) r z) k draws ∧
      k≤r*(B+A+S+3)+1 ∧ draws≤r*T := by
  obtain ⟨k,draws,h⟩ := exists_execution trial state accept output hexists r z
  exact ⟨k,draws,h,executes_budget htrial haccept houtput h⟩

/-- A proof-level identification of the two existing finite-product types.
Both use the same nested pair representation and the same first-accept rule. -/
def fullDraws : (r : ℕ) → KSDebitWalkRetry.FiniteRetry.Draws L r → Draws L r
  | 0,_ => PUnit.unit
  | r+1,z => (z.1,fullDraws r z.2)

theorem full_firstAccepted (output : L → Output) (accept : L → Bool)
    (r : ℕ) (z : KSDebitWalkRetry.FiniteRetry.Draws L r) :
    KSEighthManuscriptRetry.firstAccepted output accept r (fullDraws r z)=
      KSDebitWalkRetry.FiniteRetry.firstAccepted output accept r z := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simp only [fullDraws,KSEighthManuscriptRetry.firstAccepted,
      KSDebitWalkRetry.FiniteRetry.firstAccepted,ih]

end MatrixSpencer.KSCountedRetry
