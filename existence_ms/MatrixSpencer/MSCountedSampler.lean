import MatrixSpencer.MSManuscriptSamplerTools
import MatrixSpencer.RealRAMJacobiIteration

/-! Compositional execution certificates for the existing finite MS samplers.
Binding follows only the selected first output and its selected continuation.
The finite probability space is a specification and is never enumerated.

Primitive numerical implementations provide the leaf execution relations.
`pure` only returns an already available value; it does not compute that value.
`map` receives a counted implementation, whose primitive scalar realization
must be proved by its caller. This module supplies no numerical oracle. -/

noncomputable section
namespace MatrixSpencer.MSCountedSampler
open MSManuscriptAdaptive
open RealRAM.JacobiIteration (Counted)
variable {α β γ : Type*}

structure Implementation (P : Sampler α) where
  Executes : P.Draws → α → ℕ → ℕ → Prop
  result : ∀ z out cost draws, Executes z out cost draws → out = P.value z
  complete : ∀ z, ∃ cost draws, Executes z (P.value z) cost draws

def Bounded {P : Sampler α} (E : Implementation P) (B R : ℕ) : Prop :=
  ∀ z out cost draws, E.Executes z out cost draws → cost ≤ B ∧ draws ≤ R

theorem execution_bounded {P : Sampler α} (E : Implementation P) {B R : ℕ}
    (h : Bounded E B R) (z : P.Draws) :
    ∃ cost draws, E.Executes z (P.value z) cost draws ∧ cost ≤ B ∧ draws ≤ R := by
  obtain ⟨cost,draws,he⟩ := E.complete z
  exact ⟨cost,draws,he,h z _ cost draws he⟩

def pure (a : α) (copyCost : ℕ) : Implementation (Sampler.pure a) where
  Executes _ out cost draws := out = a ∧ cost = copyCost+1 ∧ draws = 0
  result _ _ _ _ h := h.1
  complete _ := ⟨copyCost+1,0,rfl,rfl,rfl⟩

theorem pure_bounded (a : α) (copyCost : ℕ) :
    Bounded (pure a copyCost) (copyCost+1) 0 := by
  intro z out cost draws h
  rcases h with ⟨_,rfl,rfl⟩
  exact ⟨le_rfl,le_rfl⟩

inductive BindExec {P : Sampler α} {Q : α → Sampler β}
    (E : Implementation P) (F : ∀ a, Implementation (Q a)) :
    (P.bind Q).Draws → β → ℕ → ℕ → Prop where
  | bind (z : (P.bind Q).Draws) {out : β} {k₁ k₂ r₁ r₂ : ℕ} :
      E.Executes z.1 (P.value z.1) k₁ r₁ →
      (F (P.value z.1)).Executes z.2 out k₂ r₂ →
      BindExec E F z out (k₁+k₂+2) (r₁+r₂)

def bind {P : Sampler α} {Q : α → Sampler β}
    (E : Implementation P) (F : ∀ a, Implementation (Q a)) :
    Implementation (P.bind Q) where
  Executes := BindExec E F
  result z out cost draws h := by
    cases h with
    | bind h₁ h₂ => exact (F (P.value z.1)).result _ _ _ _ h₂
  complete z := by
    obtain ⟨k₁,r₁,h₁⟩ := E.complete z.1
    obtain ⟨k₂,r₂,h₂⟩ := (F (P.value z.1)).complete z.2
    exact ⟨k₁+k₂+2,r₁+r₂,BindExec.bind z h₁ h₂⟩

theorem bind_bounded {P : Sampler α} {Q : α → Sampler β}
    (E : Implementation P) (F : ∀ a, Implementation (Q a))
    {B C R S : ℕ} (hE : Bounded E B R) (hF : ∀ a, Bounded (F a) C S) :
    Bounded (bind E F) (B+C+2) (R+S) := by
  intro z out cost draws h
  cases h with
  | bind h₁ h₂ =>
    have hb := hE _ _ _ _ h₁
    have hc := hF _ _ _ _ _ h₂
    constructor <;> omega

inductive MapExec {P : Sampler α} (E : Implementation P) (f : α → Counted β) :
    P.Draws → β → ℕ → ℕ → Prop where
  | map (z : P.Draws) {k r : ℕ} : E.Executes z (P.value z) k r →
      MapExec E f z (f (P.value z)).value (k+(f (P.value z)).cost+2) r

def map {P : Sampler α} (E : Implementation P) (f : α → Counted β) :
    Implementation (P.map (fun a => (f a).value)) where
  Executes := MapExec (P := P) E f
  result z out cost draws h := by cases h; rfl
  complete z := by
    obtain ⟨k,r,h⟩ := E.complete z
    exact ⟨k+(f (P.value z)).cost+2,r,MapExec.map (P := P) (E := E) (f := f) z h⟩

theorem map_bounded {P : Sampler α} (E : Implementation P) (f : α → Counted β)
    {B C R : ℕ} (hE : Bounded E B R) (hf : ∀ a, (f a).cost ≤ C) :
    Bounded (map E f) (B+C+2) R := by
  intro z out cost draws h
  cases h with
  | map h =>
    have hb := hE _ _ _ _ h
    have hc := hf (P.value z)
    constructor <;> omega

/-- Identifying a definitionally represented sampler changes no computation.
This is used only for named wrappers and proof-certificate erasure. -/
def congr {P Q : Sampler α} (h : P = Q) (E : Implementation P) : Implementation Q := h ▸ E

theorem congr_bounded {P Q : Sampler α} (h : P = Q) (E : Implementation P)
    {B R : ℕ} (hE : Bounded E B R) : Bounded (congr h E) B R := by
  subst Q
  exact hE

/-- Erasing a subtype's proof field leaves its stored data untouched. -/
def eraseSubtype {p : α → Prop} {P : Sampler {a // p a}}
    (E : Implementation P) : Implementation (P.map Subtype.val) :=
  map E (fun a => ⟨a.val,0⟩)

theorem eraseSubtype_bounded {p : α → Prop} {P : Sampler {a // p a}}
    (E : Implementation P) {B R : ℕ} (hE : Bounded E B R) :
    Bounded (eraseSubtype E) (B+2) R := by
  exact map_bounded E (fun a => ⟨a.val,0⟩) hE (fun _ => le_rfl)

end MatrixSpencer.MSCountedSampler
