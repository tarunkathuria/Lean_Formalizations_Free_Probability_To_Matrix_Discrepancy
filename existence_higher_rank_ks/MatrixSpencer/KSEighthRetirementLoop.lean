import MatrixSpencer.KSCubePreparation
import MatrixSpencer.KSStateRetirement



open scoped BigOperators
open Set
noncomputable section
namespace MatrixSpencer.KSEighthRetirementLoop

attribute [local instance] Classical.propDecidable

variable {N : ℕ}

abbrev Candidate (N : ℕ) := Fin N × Bool

def endpoint (a : ℝ) (b : Bool) : ℝ := if b then a else -a

def update (a : ℝ) (x : Fin N → ℝ) (c : Candidate N) : Fin N → ℝ :=
  Function.update x c.1 (endpoint a c.2)

def accepted (a τ : ℝ) (report : (Fin N → ℝ) → ℝ)
    (x : Fin N → ℝ) (c : Candidate N) : Prop :=
  |x c.1| < a ∧ report (update a x c) - report x ≤ τ / 2

def scan (a τ : ℝ) (report : (Fin N → ℝ) → ℝ) (x : Fin N → ℝ) :
    List (Candidate N) → Option (Candidate N)
  | [] => none
  | c :: cs => if accepted a τ report x c then some c else scan a τ report x cs

def select (a τ : ℝ) (report : (Fin N → ℝ) → ℝ) (x : Fin N → ℝ) :
    Option (Candidate N) := scan a τ report x Finset.univ.toList

def prepare (a τ : ℝ) (report : (Fin N → ℝ) → ℝ) :
    ℕ → (Fin N → ℝ) → (Fin N → ℝ)
  | 0, x => x
  | k + 1, x => match select a τ report x with
    | none => x
    | some c => prepare a τ report k (update a x c)

theorem endpoint_eq (a : ℝ) (b : Bool) : endpoint a b = -a ∨ endpoint a b = a := by
  cases b <;> simp [endpoint]

theorem endpoint_abs {a : ℝ} (ha : 0 ≤ a) (b : Bool) : |endpoint a b| = a := by
  cases b <;> simp [endpoint, abs_of_nonneg ha]

theorem scan_some {a τ : ℝ} {report : (Fin N → ℝ) → ℝ} {x : Fin N → ℝ}
    {cs : List (Candidate N)} {c : Candidate N}
    (h : scan a τ report x cs = some c) : accepted a τ report x c := by
  induction cs with
  | nil => simp [scan] at h
  | cons d ds ih =>
    by_cases hd : accepted a τ report x d
    · simp only [scan, if_pos hd, Option.some.injEq] at h
      exact h ▸ hd
    · exact ih (by simpa only [scan, if_neg hd] using h)

theorem scan_none {a τ : ℝ} {report : (Fin N → ℝ) → ℝ} {x : Fin N → ℝ}
    {cs : List (Candidate N)} (h : scan a τ report x cs = none) :
    ∀ c ∈ cs, ¬accepted a τ report x c := by
  induction cs with
  | nil => simp
  | cons d ds ih =>
    have hd : ¬accepted a τ report x d := by
      intro hd
      simp only [scan, if_pos hd, Option.some_ne_none] at h
    have ht : scan a τ report x ds = none := by
      simpa only [scan, if_neg hd] using h
    intro c hc
    rcases List.mem_cons.mp hc with he | he
    · exact he ▸ hd
    · exact ih ht c he

theorem select_some {a τ : ℝ} {report : (Fin N → ℝ) → ℝ} {x : Fin N → ℝ}
    {c : Candidate N} (h : select a τ report x = some c) : accepted a τ report x c :=
  scan_some h

theorem select_none {a τ : ℝ} {report : (Fin N → ℝ) → ℝ} {x : Fin N → ℝ}
    (h : select a τ report x = none) (c : Candidate N) : ¬accepted a τ report x c :=
  scan_none h c (by simp)

theorem update_mem_cube {a : ℝ} (ha : 0 ≤ a) {x : Fin N → ℝ}
    (hx : x ∈ ksCube a) (c : Candidate N) : update a x c ∈ ksCube a :=
  ksCube_update_endpoint ha hx c.1 (endpoint_eq a c.2)

theorem update_frozen_lt {a τ : ℝ} (ha : 0 ≤ a)
    {report : (Fin N → ℝ) → ℝ} {x : Fin N → ℝ} {c : Candidate N}
    (hc : accepted a τ report x c) :
    (ksFrozen a x).card < (ksFrozen a (update a x c)).card :=
  ksFrozen_lt_update x c.1 hc.1 _ (endpoint_abs ha _)

theorem prepare_mem_cube {a τ : ℝ} (ha : 0 ≤ a)
    (report : (Fin N → ℝ) → ℝ) (k : ℕ) {x : Fin N → ℝ}
    (hx : x ∈ ksCube a) : prepare a τ report k x ∈ ksCube a := by
  induction k generalizing x with
  | zero => exact hx
  | succ k ih =>
    cases hs : select a τ report x with
    | none => simpa only [prepare, hs] using hx
    | some c => simpa only [prepare, hs] using ih (update_mem_cube ha hx c)

theorem update_preserves_frozen {a τ : ℝ}
    {report : (Fin N → ℝ) → ℝ} {x : Fin N → ℝ} {c : Candidate N}
    (hc : accepted a τ report x c) (i : Fin N) (hi : |x i| = a) :
    update a x c i = x i := by
  have hne : i ≠ c.1 := by
    intro he
    subst i
    exact (ne_of_lt hc.1) hi
  exact Function.update_of_ne hne _ _

theorem prepare_preserves_frozen {a τ : ℝ}
    (report : (Fin N → ℝ) → ℝ) (k : ℕ) (x : Fin N → ℝ)
    (i : Fin N) (hi : |x i| = a) : prepare a τ report k x i = x i := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    cases hs : select a τ report x with
    | none => simp only [prepare, hs]
    | some c =>
      have he := update_preserves_frozen (select_some hs) i hi
      simpa only [prepare, hs, he] using ih (update a x c) (by rwa [he])

theorem update_energy_progress {a : ℝ}
    {x : Fin N → ℝ} (hx : x ∈ ksCube a)
    (c : Candidate N) :
    KSCubePreparation.energy x ≤ KSCubePreparation.energy (update a x c) := by
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : i = c.1
  · subst i
    change x c.1 ^ 2 ≤ (Function.update x c.1 (endpoint a c.2) c.1) ^ 2
    rw [Function.update_self]
    have he : endpoint a c.2 ^ 2 = a ^ 2 := by
      rcases endpoint_eq a c.2 with h | h <;> rw [h] <;> ring
    rw [he]
    exact KSCubePreparation.coordinate_sq_le ⟨hx.1 c.1, hx.2 c.1⟩
  · simp only [update, Function.update_of_ne hi, le_refl]

theorem prepare_energy_progress {a τ : ℝ} (ha : 0 ≤ a)
    (report : (Fin N → ℝ) → ℝ) (k : ℕ) {x : Fin N → ℝ}
    (hx : x ∈ ksCube a) :
    KSCubePreparation.energy x ≤ KSCubePreparation.energy (prepare a τ report k x) := by
  induction k generalizing x with
  | zero => exact le_rfl
  | succ k ih =>
    cases hs : select a τ report x with
    | none => simp only [prepare, hs, le_refl]
    | some c =>
      simp only [prepare, hs]
      exact (update_energy_progress hx c).trans (ih (update_mem_cube ha hx c))

theorem prepare_frozen_lower_if_enabled {a τ : ℝ} (ha : 0 ≤ a)
    (report : (Fin N → ℝ) → ℝ) (k : ℕ) (x : Fin N → ℝ)
    (henabled : ∃ c, select a τ report (prepare a τ report k x) = some c) :
    (ksFrozen a x).card + k ≤ (ksFrozen a (prepare a τ report k x)).card := by
  induction k generalizing x with
  | zero => simp [prepare]
  | succ k ih =>
    cases hs : select a τ report x with
    | none =>
      simp only [prepare, hs] at henabled
      obtain ⟨c, hc⟩ := henabled
      contradiction
    | some c =>
      simp only [prepare, hs] at henabled ⊢
      have hnext := ih (update a x c) henabled
      have hinc := update_frozen_lt ha (select_some hs)
      omega

/-- This is termination of the defined endpoint-test loop, not a claim that
the movement process is already formalized. -/
theorem prepare_exhausts_tests {a τ : ℝ} (ha : 0 ≤ a)
    (report : (Fin N → ℝ) → ℝ) (x : Fin N → ℝ) :
    select a τ report (prepare a τ report N x) = none := by
  cases hs : select a τ report (prepare a τ report N x) with
  | none => rfl
  | some c =>
    have hl := prepare_frozen_lower_if_enabled ha report N x ⟨c, hs⟩
    have hi := update_frozen_lt ha (select_some hs)
    have hb := ksFrozen_card_le a (update a (prepare a τ report N x) c)
    omega

theorem accepted_true_cost {a τ : ℝ} {report F : (Fin N → ℝ) → ℝ}
    {x : Fin N → ℝ} {c : Candidate N} (hc : accepted a τ report x c)
    (hcurrent : |report x - F x| ≤ τ / 8)
    (hendpoint : |report (update a x c) - F (update a x c)| ≤ τ / 8) :
    F (update a x c) ≤ F x + 3 * τ / 4 := by
  rcases abs_le.mp hcurrent with ⟨hcl, hcu⟩
  rcases abs_le.mp hendpoint with ⟨hel, heu⟩
  have ht := hc.2
  linarith

theorem exact_safe_is_accepted {a τ : ℝ} (hτ : 0 ≤ τ)
    {report F : (Fin N → ℝ) → ℝ} {x : Fin N → ℝ} {c : Candidate N}
    (hlive : |x c.1| < a) (hsafe : F (update a x c) ≤ F x)
    (hcurrent : |report x - F x| ≤ τ / 8)
    (hendpoint : |report (update a x c) - F (update a x c)| ≤ τ / 8) :
    accepted a τ report x c := by
  refine ⟨hlive, ?_⟩
  rcases abs_le.mp hcurrent with ⟨hcl, hcu⟩
  rcases abs_le.mp hendpoint with ⟨hel, heu⟩
  linarith

theorem prepare_potential_cost {a τ : ℝ} (ha : 0 ≤ a) (hτ : 0 ≤ τ)
    (report F : (Fin N → ℝ) → ℝ)
    (haccuracy : ∀ x ∈ ksCube a, |report x - F x| ≤ τ / 8)
    (k : ℕ) {x : Fin N → ℝ} (hx : x ∈ ksCube a) :
    F (prepare a τ report k x) ≤ F x + (k : ℝ) * (3 * τ / 4) := by
  induction k generalizing x with
  | zero => simp [prepare]
  | succ k ih =>
    cases hs : select a τ report x with
    | none =>
      simp only [prepare, hs]
      exact le_add_of_nonneg_right (by positivity)
    | some c =>
      have hu := update_mem_cube ha hx c
      have hcost := accepted_true_cost (select_some hs) (haccuracy x hx)
        (haccuracy _ hu)
      have hrest := ih hu
      simp only [prepare, hs, Nat.cast_add, Nat.cast_one]
      linarith

/-- Failed numerical preparation rules out every genuinely nonincreasing
endpoint update, once the reported values have their stated accuracy. -/
theorem no_safe_after_prepare {a τ : ℝ} (ha : 0 ≤ a) (hτ : 0 ≤ τ)
    (report F : (Fin N → ℝ) → ℝ)
    (haccuracy : ∀ x ∈ ksCube a, |report x - F x| ≤ τ / 8)
    {x : Fin N → ℝ} (hx : x ∈ ksCube a) (c : Candidate N)
    (hlive : |prepare a τ report N x c.1| < a) :
    F (prepare a τ report N x) < F (update a (prepare a τ report N x) c) := by
  let y := prepare a τ report N x
  have hy : y ∈ ksCube a := prepare_mem_cube ha report N hx
  apply lt_of_not_ge
  intro hs
  have haccept := exact_safe_is_accepted hτ hlive hs (haccuracy y hy)
    (haccuracy _ (update_mem_cube ha hy c))
  exact select_none (prepare_exhausts_tests ha report x) c haccept

open KSPotentialModels Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

/-- The exact transport safe tests fail at the output of the actual numerical
endpoint loop. No minimum of the potential is assumed. The reporting accuracy
is the remaining value-oracle obligation. -/
theorem eighth_noSafe_after_prepare {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (v : Fin N → n → ℂ) {θ τ : ℝ} (hθ : 0 < θ) (hτ : 0 ≤ τ)
    (report : (Fin N → ℝ) → ℝ)
    (haccuracy : ∀ x ∈ ksCube (1 / 8),
      |report x - eighthPotential (fun j => KSRankOne.atom (v j)) θ x| ≤ τ / 8)
    {x : Fin N → ℝ} (hx : x ∈ ksCube (1 / 8)) (i : Fin N)
    (hlive : |prepare (1 / 8) τ report N x i| < 1 / 8) :
    let y := prepare (1 / 8) τ report N x
    truncatedOwners (1 / 8) 64 y i *
      realTrace (leftDensity (KSRankOne.atom (v i)) * independentStateTransport v θ y) < 1 / 8 - y i ∧
    truncatedOwners (1 / 8) 64 y i *
      realTrace (rightDensity (KSRankOne.atom (v i)) * independentStateTransport v θ y) < 1 / 8 + y i := by
  dsimp only
  let y := prepare (1 / 8) τ report N x
  have hy : y ∈ ksCube (1 / 8) := prepare_mem_cube (by norm_num) report N hx
  constructor
  · apply lt_of_not_ge
    intro hs
    have hcost := eighth_retire_plus v hθ hy i hs
    have hstrict := no_safe_after_prepare (by norm_num : (0 : ℝ) ≤ 1 / 8)
      hτ report _ haccuracy hx (i, true) hlive
    exact (not_lt_of_ge hcost) (by simpa [update, endpoint, y] using hstrict)
  · apply lt_of_not_ge
    intro hs
    have hcost := eighth_retire_minus v hθ hy i hs
    have hstrict := no_safe_after_prepare (by norm_num : (0 : ℝ) ≤ 1 / 8)
      hτ report _ haccuracy hx (i, false) hlive
    exact (not_lt_of_ge hcost) (by simpa [update, endpoint, y] using hstrict)

end MatrixSpencer.KSEighthRetirementLoop
