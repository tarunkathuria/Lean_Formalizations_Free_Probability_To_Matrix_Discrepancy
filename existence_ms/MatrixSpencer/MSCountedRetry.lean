import MatrixSpencer.MSCountedSampler
import MatrixSpencer.MSManuscriptAcceptanceRetry

/-! Short-circuit execution of the original first-accepted MS sampler.
The original product weights describe prospective trials; later trials are
not evaluated after an acceptance. Every evaluated trial and acceptance
test is charged, including rejected trials. -/

noncomputable section
namespace MatrixSpencer.MSCountedRetry
open MSManuscriptAdaptive MSCountedSampler
open MSManuscriptProbability.FiniteRetry (Draws firstAccepted)
open RealRAM.JacobiIteration (Counted)
variable {α : Type*} {P : Sampler α}

inductive Executes (E : Implementation P) (accept : α → Counted Bool) :
    (r : ℕ) → Draws P.Draws r → Option α → ℕ → ℕ → Prop where
  | exhausted (z : Draws P.Draws 0) : Executes E accept 0 z none 1 0
  | accepted {r : ℕ} (z : Draws P.Draws (r+1)) {k draws : ℕ} :
      E.Executes z.1 (P.value z.1) k draws → (accept (P.value z.1)).value=true →
      Executes E accept (r+1) z (some (P.value z.1))
        (k+(accept (P.value z.1)).cost+3) draws
  | rejected {r : ℕ} (z : Draws P.Draws (r+1))
      {k draws rest extra : ℕ} {result : Option α} :
      E.Executes z.1 (P.value z.1) k draws → (accept (P.value z.1)).value=false →
      Executes E accept r z.2 result rest extra →
      Executes E accept (r+1) z result
        (k+(accept (P.value z.1)).cost+rest+3) (draws+extra)

theorem execution_result (E : Implementation P) (accept : α → Counted Bool)
    {r k draws : ℕ} {z : Draws P.Draws r} {out : Option α}
    (h : Executes E accept r z out k draws) :
    out=firstAccepted P.value (fun z => (accept (P.value z)).value) r z := by
  induction h with
  | exhausted z => rfl
  | accepted z ht ha => simp only [firstAccepted,ha,↓reduceIte]
  | rejected z ht ha hr ih => simp only [firstAccepted,ha,↓reduceIte]; exact ih

theorem execution_budget (E : Implementation P) (accept : α → Counted Bool)
    {B A R : ℕ} (hE : Bounded E B R) (hA : ∀ a, (accept a).cost ≤ A)
    {r k draws : ℕ} {z : Draws P.Draws r} {out : Option α}
    (h : Executes E accept r z out k draws) :
    k ≤ r*(B+A+3)+1 ∧ draws ≤ r*R := by
  induction h with
  | exhausted z => simp
  | @accepted r z k draws ht ha =>
    have hb := hE _ _ _ _ ht
    have hc := hA (P.value z.1)
    constructor <;> nlinarith [Nat.zero_le (r*(B+A+3)),Nat.zero_le (r*R)]
  | @rejected r z k draws rest extra out ht ha hr ih =>
    have hb := hE _ _ _ _ ht
    have hc := hA (P.value z.1)
    constructor <;> nlinarith

theorem complete (E : Implementation P) (accept : α → Counted Bool)
    (r : ℕ) (z : Draws P.Draws r) :
    ∃ k draws, Executes E accept r z
      (firstAccepted P.value (fun z => (accept (P.value z)).value) r z) k draws := by
  induction r with
  | zero => exact ⟨1,0,Executes.exhausted z⟩
  | succ r ih =>
    obtain ⟨k,draws,ht⟩ := E.complete z.1
    cases ha : (accept (P.value z.1)).value with
    | false =>
      obtain ⟨rest,extra,hr⟩ := ih z.2
      refine ⟨k+(accept (P.value z.1)).cost+rest+3,draws+extra,?_⟩
      simpa only [firstAccepted,ha,↓reduceIte] using Executes.rejected z ht ha hr
    | true =>
      refine ⟨k+(accept (P.value z.1)).cost+3,draws,?_⟩
      simpa only [firstAccepted,ha,↓reduceIte] using Executes.accepted z ht ha

def implementation (E : Implementation P) (accept : α → Counted Bool) (r : ℕ) :
    Implementation (MSManuscriptAcceptanceRetry.output P (fun a => (accept a).value) r) where
  Executes := Executes E accept r
  result _ _ _ _ h := execution_result E accept h
  complete := complete E accept r

theorem implementation_bounded (E : Implementation P) (accept : α → Counted Bool)
    {B A R : ℕ} (hE : Bounded E B R) (hA : ∀ a, (accept a).cost ≤ A) (r : ℕ) :
    Bounded (implementation E accept r) (r*(B+A+3)+1) (r*R) := by
  intro z out cost draws h
  exact execution_budget E accept hE hA h

end MatrixSpencer.MSCountedRetry
