import FaithfulMS.RectangularSamplingMovement
import MatrixSpencer.MSCountedSamplingLaw
import MatrixSpencer.RectangularRidgeCountedPhase

/-! Compositional finite conditional-kernel semantics for counted MS code.
The rectangular random leaf is the literal measured uniform-input selector;
square code can be embedded using its independently proved refinement.
Deterministic operations, adaptive composition, and short-circuit retries
preserve this law. This is not a claim about an infinite executable random tape.
The prospective unused retry tails are integrated out in `retry_expectation`.
No constructor can assign an arbitrary implementation a stochastic law. -/
open scoped BigOperators
noncomputable section
namespace FaithfulMS.RectangularSampling
open MatrixSpencer MatrixSpencer.MSCountedSampler MatrixSpencer.MSManuscriptAdaptive MeasureTheory
open RealRAM.JacobiIteration (Counted)
attribute [local instance] Classical.propDecidable

/-- A single uniform-real call with a proved literal selector and counted
same-input execution. In an instantiated theorem this record is constructed,
not assumed as an unexplained stochastic-law premise. It lets new preparation
and density-solver state representations reuse the compositional semantics. -/
structure UniformInput {α : Type} {P : Sampler α} (E : Implementation P) where
  pick : ℝ → Option P.Draws
  cost : ℝ → P.Draws → ℕ
  total : ∀ u, u ∈ Set.Ico (0 : ℝ) 1 → ∃ z, pick u = some z
  probability : ∀ z, (volume.restrict (Set.Ico (0 : ℝ) 1)) {u | pick u = some z} =
    ENNReal.ofReal (P.weight z)
  execution : ∀ u, u ∈ Set.Ico (0 : ℝ) 1 → ∀ z, pick u = some z →
    E.Executes z (P.value z) (cost u z) 1

namespace UniformInput

def rectangular {N d : ℕ} [Nonempty (Fin d)]
    (c : RectangularRidgeEpochInput.Config N d) (s : RectangularRidgeEpochRun.Certified c)
    (hfloor : s.val.owner.Valid (2*RectangularRidgePreparationData.floor))
    (hnt : ¬RectangularRidgeEpochRun.Stopped c s.val) :
    UniformInput (RectangularRidgeMovementWork.implementation c s hfloor hnt) where
  pick := RectangularSamplingMovement.pick s.val
  cost := RectangularRidgeMovementWork.cost c s hfloor hnt
  total := RectangularSamplingMovement.pick_total c s hnt
  probability := RectangularSamplingMovement.pick_probability c s hfloor hnt
  execution := RectangularSamplingMovement.selected_execution c s hfloor hnt

end UniformInput

inductive Refinement : {α : Type} → {P : Sampler α} → Implementation P → Type 1 where
  | uniform {α : Type} {P : Sampler α} {E : Implementation P}
      (primitive : UniformInput E) : Refinement E
  | uniformMovement {N d : ℕ} [Nonempty (Fin d)] (c : RectangularRidgeEpochInput.Config N d)
      (s : RectangularRidgeEpochRun.Certified c)
      (hfloor : s.val.owner.Valid (2*RectangularRidgePreparationData.floor))
      (hnt : ¬RectangularRidgeEpochRun.Stopped c s.val) :
      Refinement (RectangularRidgeMovementWork.implementation c s hfloor hnt)
  | square {α : Type} {P : Sampler α} {E : Implementation P}
      (code : MSCountedSampler.Refinement E) : Refinement E
  | retain {N : ℕ} {f : EuclideanSpace ℝ (Fin N) → ℝ} {ε τ K p : ℝ}
      (F : RectangularRidgePhaseAssembly.EpochFactory f ε τ K p)
      (start : RectangularRidgePhaseAssembly.Point (N := N) ε)
      (x : RectangularRidgePhaseAssembly.PhasePoint start)
      (hx : 32 ≤ RectangularRidgeRemainingPotential.liveCount x.val.val)
      {E : Implementation (F.sample x.val hx)} (first : Refinement E) :
      Refinement (RectangularRidgeCountedPhase.retain F start x hx E)
  | pure {α : Type} (a : α) (cost : ℕ) : Refinement (MSCountedSampler.pure a cost)
  | bind {α β : Type} {P : Sampler α} {Q : α → Sampler β}
      {E : Implementation P} {F : ∀ a, Implementation (Q a)}
      (first : Refinement E) (next : ∀ a, Refinement (F a)) :
      Refinement (MSCountedSampler.bind E F)
  | map {α β : Type} {P : Sampler α} {E : Implementation P}
      (first : Refinement E) (f : α → Counted β) :
      Refinement (MSCountedSampler.map E f)
  | congr {α : Type} {P Q : Sampler α} (h : P = Q) {E : Implementation P}
      (first : Refinement E) : Refinement (MSCountedSampler.congr h E)
  | overhead {α : Type} {P : Sampler α} {E : Implementation P}
      (first : Refinement E) (extra : ℕ) :
      Refinement (MSCountedSampler.overhead E extra)
  | certify {α : Type} {P : Sampler (Option α)} {E : Implementation P}
      (first : Refinement E) (q : α → Prop)
      (hq : ∀ z y, P.value z = some y → q y) :
      Refinement (MSCountedSampler.certify E q hq)
  | retry {α : Type} {P : Sampler α} {E : Implementation P}
      (trial : Refinement E) (accept : α → Counted Bool) (r : ℕ) :
      Refinement (MSCountedRetry.implementation E accept r)
  | setup {α : Type} {P : Sampler α} {E : Implementation P}
      (first : Refinement E) (setupCost : ℕ) :
      Refinement (MSCountedEpochFactory.addSetup E setupCost)

namespace Refinement

def mass {α : Type} {P : Sampler α} {E : Implementation P}
    (code : Refinement E) : P.Draws → ℝ := by
  induction code with
  | uniform primitive =>
    exact fun z => ((volume.restrict (Set.Ico (0 : ℝ) 1))
      {u | primitive.pick u = some z}).toReal
  | uniformMovement c s hfloor hnt =>
    exact fun z => ((volume.restrict (Set.Ico (0 : ℝ) 1))
      {u | RectangularSamplingMovement.pick s.val u = some z}).toReal
  | square code => exact code.mass
  | retain F start x hx first ih => exact ih
  | pure a cost => exact fun _ => 1
  | bind first next ih₁ ih₂ => exact fun z => ih₁ z.1 * ih₂ _ z.2
  | map first f ih => exact ih
  | congr h first ih => subst h; exact ih
  | overhead first extra ih => exact ih
  | certify first q hq ih => exact ih
  | retry trial accept r ih => exact MSManuscriptProbability.FiniteRetry.weight ih r
  | setup first setupCost ih => exact ih

theorem mass_eq {α : Type} {P : Sampler α} {E : Implementation P}
    (code : Refinement E) (z : P.Draws) : code.mass z = P.weight z := by
  induction code with
  | @uniform α P E primitive =>
    exact (congrArg ENNReal.toReal (primitive.probability z)).trans
      (ENNReal.toReal_ofReal (P.weight_nonneg z))
  | uniformMovement c s hfloor hnt =>
    exact (congrArg ENNReal.toReal
      (RectangularSamplingMovement.pick_probability c s hfloor hnt z)).trans
      (ENNReal.toReal_ofReal
        ((RectangularRidgeEpochRun.movement c s hfloor hnt).weight_nonneg z))
  | square code => exact code.mass_eq z
  | retain F start x hx first ih => exact ih z
  | pure a cost => rfl
  | bind first next ih₁ ih₂ =>
    change first.mass z.1 * (next _).mass z.2 = _
    rw [ih₁, ih₂]
    rfl
  | map first f ih => exact ih z
  | congr h first ih => subst h; exact ih z
  | overhead first extra ih => exact ih z
  | certify first q hq ih => exact ih z
  | retry trial accept r ih =>
    change MSManuscriptProbability.FiniteRetry.weight trial.mass r z = _
    have he : trial.mass = _ := funext ih
    rw [he]
    rfl
  | setup first setupCost ih => exact ih z

theorem mass_nonneg {α : Type} {P : Sampler α} {E : Implementation P}
    (code : Refinement E) (z : P.Draws) : 0 ≤ code.mass z := by
  rw [code.mass_eq]; exact P.weight_nonneg z

theorem mass_sum {α : Type} {P : Sampler α} {E : Implementation P}
    (code : Refinement E) : ∑ z, code.mass z = 1 := by
  simp only [code.mass_eq]; exact P.weight_sum

def expectation {α : Type} {P : Sampler α} {E : Implementation P}
    (code : Refinement E) (f : α → ℝ) : ℝ :=
  ∑ z, code.mass z * f (P.value z)

theorem expectation_eq {α : Type} {P : Sampler α} {E : Implementation P}
    (code : Refinement E) (f : α → ℝ) : code.expectation f = P.expectation f := by
  simp only [expectation, code.mass_eq, Sampler.expectation]

theorem bind_expectation {α β : Type} {P : Sampler α} {Q : α → Sampler β}
    {E : Implementation P} {F : ∀ a, Implementation (Q a)}
    (first : Refinement E) (next : ∀ a, Refinement (F a)) (f : β → ℝ) :
    (first.bind next).expectation f = first.expectation (fun a => (next a).expectation f) := by
  simp only [expectation_eq, Sampler.expectation_bind]

/-- Accepted branches return immediately. Summing over their unused
prospective tail contributes exactly one, so no later random call is part
of the operational branch. Rejected branches use the fresh trial kernel. -/
theorem retry_expectation {α : Type} {P : Sampler α} {E : Implementation P}
    (trial : Refinement E) (accept : α → Counted Bool) (r : ℕ) (f : Option α → ℝ) :
    (trial.retry accept (r+1)).expectation f =
      trial.expectation (fun a => if (accept a).value then f (some a)
        else (trial.retry accept r).expectation f) := by
  simp only [expectation_eq]
  change (∑ z : P.Draws × MSManuscriptProbability.FiniteRetry.Draws P.Draws r,
    (P.weight z.1 * MSManuscriptProbability.FiniteRetry.weight P.weight r z.2) *
      f (if (accept (P.value z.1)).value then some (P.value z.1)
        else MSManuscriptProbability.FiniteRetry.firstAccepted P.value
          (fun z => (accept (P.value z)).value) r z.2)) = _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro z hz
  cases ha : (accept (P.value z)).value
  · simp only [ha, Bool.false_eq_true, ↓reduceIte, Sampler.expectation,
      MSManuscriptAcceptanceRetry.output, Finset.mul_sum, mul_assoc]
  · simp only [ha, ↓reduceIte]
    simp only [mul_assoc]
    rw [← Finset.mul_sum, ← Finset.sum_mul,
      MSManuscriptProbability.FiniteRetry.weight_sum P.weight P.weight_sum, one_mul]

/-- The event includes the actual bounded execution, not just a valid
abstract output. This transfers a success theorem after all costs have
been supplied by the concrete implementation. -/
theorem bounded_event {α : Type} {P : Sampler α} {E : Implementation P}
    (code : Refinement E) {B R : ℕ} (hB : Bounded E B R) (good : α → Prop) :
    (∑ z, code.mass z * (if ∃ out k r, E.Executes z out k r ∧ k ≤ B ∧ r ≤ R ∧ good out
      then 1 else 0)) = P.expectation (fun out => if good out then 1 else 0) := by
  classical
  unfold Sampler.expectation
  apply Finset.sum_congr rfl
  intro z hz
  rw [code.mass_eq]
  congr 1
  apply if_congr
  · constructor
    · rintro ⟨out,k,r,he,hk,hr,hg⟩
      rwa [E.result z out k r he] at hg
    · intro hg
      obtain ⟨k,r,he,hk,hr⟩ := execution_bounded E hB z
      exact ⟨P.value z,k,r,he,hk,hr,hg⟩
  · rfl
  · rfl

def nextSample {α β : Type} {Q : α → Sampler (Option β)}
    {E : ∀ a, Implementation (Q a)} (code : ∀ a, Refinement (E a)) :
    (a : Option α) → Refinement (MSCountedSampler.nextSample E a)
  | none => .pure none 0
  | some a => .overhead (code a) 1

def adaptiveRun {State : ℕ → Type}
    {step : ∀ j, State j → Sampler (Option (State (j+1)))}
    {E : ∀ j s, Implementation (step j s)} (code : ∀ j s, Refinement (E j s))
    (start : State 0) : (K : ℕ) → Refinement (MSCountedSampler.adaptiveRun E start K)
  | 0 => .pure (some start) 0
  | K+1 => .bind (adaptiveRun code start K) (nextSample (code K))

def iterate {α : Type} {step : α → Sampler α} {E : ∀ s, Implementation (step s)}
    (code : ∀ s, Refinement (E s)) :
    (K : ℕ) → (s : α) → Refinement (MSCountedSampler.iterate E K s)
  | 0,s => .pure s 0
  | K+1,s => .bind (code s) (iterate code K)

end Refinement
end FaithfulMS.RectangularSampling
