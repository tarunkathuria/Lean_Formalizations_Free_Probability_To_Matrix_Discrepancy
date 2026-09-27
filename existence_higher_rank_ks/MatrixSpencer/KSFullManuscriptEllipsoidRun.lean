import MatrixSpencer.KSFullManuscriptEllipsoidAffine

/-!
# A finite central-cut ellipsoid recursion

This is an actual recursion, including an absorbing feasible-center branch.
It proves preservation of the target body and soundness of returned points.
The separation procedure is still an explicit input with a correctness
certificate. No claim that the SDP separation procedure or the finite
volume-based feasibility cutoff has been constructed is made here.
-/

open scoped InnerProductSpace
noncomputable section
namespace MatrixSpencer.KSFullManuscriptEllipsoidRun

open KSFullManuscriptEllipsoidAffine
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- A `none` answer certifies membership; a separating vector certifies a
central retaining half-space and is nonzero. This is an intermediate contract. -/
structure SeparationProcedure (target : Set E) where
  query : E → Option E
  feasible : ∀ x, query x = none → x ∈ target
  separates : ∀ x g, query x = some g → g ≠ 0 ∧
    ∀ y ∈ target, ⟪g, y - x⟫_ℝ ≤ 0

def step (ℓ : ℝ) (query : E → Option E) (s : State E) : State E :=
  match query s.center with
  | none => s
  | some g => update ℓ s g

def run (ℓ : ℝ) (query : E → Option E) : ℕ → State E → State E
  | 0, s => s
  | T + 1, s => step ℓ query (run ℓ query T s)

theorem run_of_feasible (ℓ : ℝ) (query : E → Option E) (s : State E)
    (hs : query s.center = none) (T : ℕ) : run ℓ query T s = s := by
  induction T with
  | zero => rfl
  | succ T ih => simp only [run, ih, step, hs]

theorem step_surjective {ℓ : ℝ} (hℓ : 1 < ℓ) {target : Set E}
    (sep : SeparationProcedure target) (s : State E)
    (hs : Function.Surjective s.factor) :
    Function.Surjective (step ℓ sep.query s).factor := by
  cases hq : sep.query s.center with
  | none => simpa only [step, hq] using hs
  | some g =>
    simpa only [step, hq] using update_surjective hℓ s hs (sep.separates _ _ hq).1

theorem step_contains_target {ℓ : ℝ} (hℓ : 1 < ℓ) {target : Set E}
    (sep : SeparationProcedure target) (s : State E)
    (hs : Function.Surjective s.factor) (hbody : target ⊆ body s) :
    target ⊆ body (step ℓ sep.query s) := by
  cases hq : sep.query s.center with
  | none => simpa only [step, hq] using hbody
  | some g =>
    intro y hy
    have hh := sep.separates _ _ hq
    have hc := retained_subset_update hℓ s hs hh.1 ⟨hbody hy, hh.2 y hy⟩
    simpa only [step, hq] using hc

theorem run_invariant {ℓ : ℝ} (hℓ : 1 < ℓ) {target : Set E}
    (sep : SeparationProcedure target) (s : State E)
    (hs : Function.Surjective s.factor) (hbody : target ⊆ body s) (T : ℕ) :
    Function.Surjective (run ℓ sep.query T s).factor ∧
      target ⊆ body (run ℓ sep.query T s) := by
  induction T with
  | zero => exact ⟨hs, hbody⟩
  | succ T ih =>
    exact ⟨step_surjective hℓ sep _ ih.1, step_contains_target hℓ sep _ ih.1 ih.2⟩

/-- Return the actual final center if its separation query certifies it;
otherwise report that the finite cutoff has not found a feasible center. -/
def output (ℓ : ℝ) (query : E → Option E) (T : ℕ) (s : State E) : Option E :=
  let finalState := run ℓ query T s
  match query finalState.center with
  | none => some finalState.center
  | some _ => none

theorem output_sound (ℓ : ℝ) {target : Set E} (sep : SeparationProcedure target)
    (T : ℕ) (s : State E) {y : E} (hy : output ℓ sep.query T s = some y) : y ∈ target := by
  unfold output at hy
  cases hq : sep.query (run ℓ sep.query T s).center with
  | none =>
    simp only [hq, Option.some.injEq] at hy
    rw [← hy]
    exact sep.feasible _ hq
  | some g => simp [hq] at hy

end MatrixSpencer.KSFullManuscriptEllipsoidRun
