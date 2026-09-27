import Mathlib

/-!
# Finite adaptive sampling and accumulated failure probability

A sampler has explicit finite draws, weights, and outputs. Binding samples the
second draw from the distribution attached to the first actual output, using
the product weight. Thus later signing calls can depend on all earlier results.
`run` absorbs failure and retains every successful intermediate output.
-/

open scoped BigOperators
noncomputable section
namespace MatrixSpencer.MSManuscriptAdaptive

structure Sampler (α : Type*) where
  Draws : Type
  fintypeDraws : Fintype Draws
  weight : Draws → ℝ
  value : Draws → α
  weight_nonneg : ∀ z, 0 ≤ weight z
  weight_sum : ∑ z, weight z = 1

attribute [instance] Sampler.fintypeDraws

namespace Sampler
variable {α β : Type*}

def pure (a : α) : Sampler α where
  Draws := PUnit
  fintypeDraws := inferInstance
  weight := fun _ => 1
  value := fun _ => a
  weight_nonneg := fun _ => zero_le_one
  weight_sum := by simp

def bind (P : Sampler α) (Q : α → Sampler β) : Sampler β where
  Draws := Σ z : P.Draws, (Q (P.value z)).Draws
  fintypeDraws := inferInstance
  weight := fun z => P.weight z.1 * (Q (P.value z.1)).weight z.2
  value := fun z => (Q (P.value z.1)).value z.2
  weight_nonneg := fun z => mul_nonneg (P.weight_nonneg z.1)
    ((Q (P.value z.1)).weight_nonneg z.2)
  weight_sum := by
    rw [Fintype.sum_sigma]
    simp only [← Finset.mul_sum, Sampler.weight_sum, mul_one]

def expectation (P : Sampler α) (f : α → ℝ) : ℝ :=
  ∑ z, P.weight z * f (P.value z)

@[simp] theorem expectation_pure (a : α) (f : α → ℝ) :
    (pure a).expectation f = f a := by simp [expectation, pure]

theorem expectation_bind (P : Sampler α) (Q : α → Sampler β) (f : β → ℝ) :
    (P.bind Q).expectation f = P.expectation (fun a => (Q a).expectation f) := by
  unfold expectation bind
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro z hz
  simp only [Finset.mul_sum, mul_assoc]

theorem expectation_const (P : Sampler α) (c : ℝ) :
    P.expectation (fun _ => c) = c := by
  simp only [expectation, ← Finset.sum_mul, P.weight_sum, one_mul]

theorem expectation_nonneg (P : Sampler α) (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) :
    0 ≤ P.expectation f :=
  Finset.sum_nonneg (fun z _ => mul_nonneg (P.weight_nonneg z) (hf (P.value z)))

theorem expectation_mono (P : Sampler α) {f g : α → ℝ} (h : ∀ a, f a ≤ g a) :
    P.expectation f ≤ P.expectation g :=
  Finset.sum_le_sum (fun z _ => mul_le_mul_of_nonneg_left (h (P.value z))
    (P.weight_nonneg z))

theorem expectation_sub (P : Sampler α) (f g : α → ℝ) :
    P.expectation (fun a => f a - g a) = P.expectation f - P.expectation g := by
  simp only [expectation, mul_sub, Finset.sum_sub_distrib]

end Sampler

def success {α : Type*} (x : Option α) : ℝ := if x.isSome then 1 else 0
def failure {α : Type*} (x : Option α) : ℝ := if x.isSome then 0 else 1

@[simp] theorem success_none {α : Type*} : success (none : Option α) = 0 := rfl
@[simp] theorem success_some {α : Type*} (a : α) : success (some a) = 1 := rfl
@[simp] theorem failure_none {α : Type*} : failure (none : Option α) = 1 := rfl
@[simp] theorem failure_some {α : Type*} (a : α) : failure (some a) = 0 := rfl

theorem success_eq_one_sub_failure {α : Type*} (x : Option α) :
    success x = 1 - failure x := by cases x <;> norm_num

theorem success_add_failure {α : Type*} (P : Sampler (Option α)) :
    P.expectation success + P.expectation failure = 1 := by
  have h := P.expectation_sub (fun _ => 1) failure
  have he : P.expectation success = P.expectation (fun x => 1 - failure x) := by
    congr 1
    funext x
    exact success_eq_one_sub_failure x
  rw [he, h, P.expectation_const]
  ring

/-- Failure is absorbing; successful values are passed to the actual next call. -/
def nextSample {α β : Type*} (Q : α → Sampler (Option β)) : Option α → Sampler (Option β)
  | none => Sampler.pure none
  | some a => Q a

/-- The finite adaptive run, permitting a different certified state type at each stage. -/
def run {State : ℕ → Type*}
    (step : ∀ j, State j → Sampler (Option (State (j + 1)))) (initial : State 0) :
    (k : ℕ) → Sampler (Option (State k))
  | 0 => Sampler.pure (some initial)
  | k + 1 => (run step initial k).bind (nextSample (step k))

theorem nextSample_failure_le {α β : Type*} (Q : α → Sampler (Option β))
    {p : ℝ} (hp : 0 ≤ p) (hQ : ∀ a, (Q a).expectation failure ≤ p)
    (a : Option α) : (nextSample Q a).expectation failure ≤ failure a + p := by
  cases a with
  | none => simpa [nextSample] using hp
  | some a => simpa [nextSample] using hQ a

/-- An adaptive union bound: the failure mass is at most the sum of the actual
per-call failure bounds. No independence of the success events is assumed. -/
theorem run_failure_le {State : ℕ → Type*}
    (step : ∀ j, State j → Sampler (Option (State (j + 1)))) (initial : State 0)
    (p : ℕ → ℝ) (hp : ∀ j, 0 ≤ p j)
    (hstep : ∀ j a, (step j a).expectation failure ≤ p j) (k : ℕ) :
    (run step initial k).expectation failure ≤ ∑ j ∈ Finset.range k, p j := by
  induction k with
  | zero => simp [run]
  | succ k ih =>
    rw [run, Sampler.expectation_bind]
    have hmono := (run step initial k).expectation_mono
      (nextSample_failure_le (step k) (hp k) (hstep k))
    have he : (run step initial k).expectation (fun a => failure a + p k) =
        (run step initial k).expectation failure + p k := by
      simp only [Sampler.expectation, mul_add, Finset.sum_add_distrib,
        ← Finset.sum_mul, Sampler.weight_sum, one_mul]
    rw [he] at hmono
    rw [Finset.sum_range_succ]
    exact hmono.trans (add_le_add_right ih _)

theorem run_success_ge {State : ℕ → Type*}
    (step : ∀ j, State j → Sampler (Option (State (j + 1)))) (initial : State 0)
    (p : ℕ → ℝ) (hp : ∀ j, 0 ≤ p j)
    (hstep : ∀ j a, (step j a).expectation failure ≤ p j) (k : ℕ) :
    1 - (∑ j ∈ Finset.range k, p j) ≤ (run step initial k).expectation success := by
  have hf := run_failure_le step initial p hp hstep k
  have hs := success_add_failure (run step initial k)
  linarith

/-- Expanded event form for the actual finite draw space and product weights. -/
theorem run_success_event_ge {State : ℕ → Type*}
    (step : ∀ j, State j → Sampler (Option (State (j + 1)))) (initial : State 0)
    (p : ℕ → ℝ) (hp : ∀ j, 0 ≤ p j)
    (hstep : ∀ j a, (step j a).expectation failure ≤ p j) (k : ℕ) :
    1 - (∑ j ∈ Finset.range k, p j) ≤
      ∑ z : (run step initial k).Draws, (run step initial k).weight z *
        (if ((run step initial k).value z).isSome then 1 else 0) :=
  run_success_ge step initial p hp hstep k

end MatrixSpencer.MSManuscriptAdaptive
