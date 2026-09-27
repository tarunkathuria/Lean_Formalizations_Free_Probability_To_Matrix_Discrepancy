import MatrixSpencer.MSCountedSampler
import MatrixSpencer.MSManuscriptBoundedProcess

/-! Counted failure-absorbing adaptive loops and proof-ledger attachment.
Only the selected continuation is executed. The scalar test and numerical
step implementations remain explicit arguments until their concrete MS
implementations discharge them. -/

noncomputable section
namespace MatrixSpencer.MSCountedSampler
open MSManuscriptAdaptive
variable {α β : Type*}

def overhead {P : Sampler α} (E : Implementation P) (extra : ℕ) : Implementation P where
  Executes z out cost draws := ∃ k, E.Executes z out k draws ∧ cost=k+extra
  result z out cost draws h := by
    obtain ⟨k,h,_⟩ := h
    exact E.result z out k draws h
  complete z := by
    obtain ⟨k,r,h⟩ := E.complete z
    exact ⟨k+extra,r,k,h,rfl⟩

theorem overhead_bounded {P : Sampler α} (E : Implementation P) (extra : ℕ)
    {B R : ℕ} (hE : Bounded E B R) : Bounded (overhead E extra) (B+extra) R := by
  intro z out cost draws h
  obtain ⟨k,h,rfl⟩ := h
  have hb := hE z out k draws h
  constructor <;> omega

/-- Attach only a proof to an already computed optional data value. -/
def certify {P : Sampler (Option α)} (E : Implementation P) (q : α → Prop)
    (hq : ∀ z y, P.value z=some y → q y) : Implementation (P.certify q hq) where
  Executes z out cost draws := ∃ k, E.Executes z (out.map Subtype.val) k draws ∧ cost=k+2
  result z out cost draws h := by
    obtain ⟨k,h,_⟩ := h
    have he := E.result _ _ _ _ h
    have hc := Sampler.certify_map_val P q hq z
    have hinj : Function.Injective (Option.map (Subtype.val : {a // q a} → α)) :=
      Option.map_injective Subtype.val_injective
    exact hinj (he.trans hc.symm)
  complete z := by
    obtain ⟨k,r,h⟩ := E.complete z
    refine ⟨k+2,r,k,?_,rfl⟩
    rwa [Sampler.certify_map_val]

theorem certify_bounded {P : Sampler (Option α)} (E : Implementation P)
    (q : α → Prop) (hq : ∀ z y, P.value z=some y → q y)
    {B R : ℕ} (hE : Bounded E B R) : Bounded (certify E q hq) (B+2) R := by
  intro z out cost draws h
  obtain ⟨k,h,rfl⟩ := h
  have hb := hE _ _ _ _ h
  constructor <;> omega

def nextSample {Q : α → Sampler (Option β)} (E : ∀ a, Implementation (Q a)) :
    (a : Option α) → Implementation (MSManuscriptAdaptive.nextSample Q a)
  | none => pure none 0
  | some a => overhead (E a) 1

theorem nextSample_bounded {Q : α → Sampler (Option β)} (E : ∀ a, Implementation (Q a))
    {B R : ℕ} (hE : ∀ a, Bounded (E a) B R) (a : Option α) :
    Bounded (nextSample E a) (B+1) R := by
  cases a with
  | none =>
    intro z out cost draws h
    rcases h with ⟨_,rfl,rfl⟩
    constructor <;> omega
  | some a => exact overhead_bounded (E a) 1 (hE a)

def adaptiveRun {State : ℕ → Type*}
    {step : ∀ j, State j → Sampler (Option (State (j+1)))}
    (E : ∀ j s, Implementation (step j s)) (start : State 0) :
    (K : ℕ) → Implementation (MSManuscriptAdaptive.run step start K)
  | 0 => pure (some start) 0
  | K+1 => bind (adaptiveRun E start K) (nextSample (E K))

theorem adaptiveRun_bounded {State : ℕ → Type*}
    {step : ∀ j, State j → Sampler (Option (State (j+1)))}
    (E : ∀ j s, Implementation (step j s)) (start : State 0)
    {B R : ℕ} (hE : ∀ j s, Bounded (E j s) B R) (K : ℕ) :
    Bounded (adaptiveRun E start K) (K*(B+3)+1) (K*R) := by
  induction K with
  | zero => simpa only [Nat.zero_mul, Nat.zero_add] using pure_bounded (some start) 0
  | succ K ih =>
    have h := bind_bounded (adaptiveRun E start K) (nextSample (E K))
      ih (nextSample_bounded (E K) (hE K))
    convert h using 1 <;> ring

def iterateSample (step : α → Sampler α) : ℕ → α → Sampler α
  | 0,s => Sampler.pure s
  | K+1,s => (step s).bind (iterateSample step K)

def iterate {step : α → Sampler α} (E : ∀ s, Implementation (step s)) :
    (K : ℕ) → (s : α) → Implementation (iterateSample step K s)
  | 0,s => pure s 0
  | K+1,s => bind (E s) (iterate E K)

theorem iterate_bounded {step : α → Sampler α} (E : ∀ s, Implementation (step s))
    {B R : ℕ} (hE : ∀ s, Bounded (E s) B R) (K : ℕ) (s : α) :
    Bounded (iterate E K s) (K*(B+2)+1) (K*R) := by
  induction K generalizing s with
  | zero => simpa only [Nat.zero_mul, Nat.zero_add] using pure_bounded s 0
  | succ K ih =>
    have h := bind_bounded (E s) (iterate E K) (hE s) ih
    convert h using 1 <;> ring

end MatrixSpencer.MSCountedSampler
