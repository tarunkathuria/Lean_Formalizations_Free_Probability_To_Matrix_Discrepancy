import MatrixSpencer.CovarianceSampler

/-!
# Finite adaptive process moments and drift telescoping

The state type may contain the complete history of a finite tree. Transition
weights can depend on the time and current state. The recursively constructed
mass, centering conditions, and conditional drift bounds are ordinary finite
sums. All hypotheses needed by a concrete epoch remain explicit.
-/

open scoped BigOperators

namespace MatrixSpencer
namespace FiniteProcessMoments

variable (Ω : Type*) [Fintype Ω]

/-- A normalized finite initial distribution and an adaptive sequence of finite kernels. -/
structure Process where
  initial : Ω → ℝ
  transition : ℕ → Ω → Ω → ℝ
  initial_nonneg : ∀ a, 0 ≤ initial a
  initial_sum : (∑ a, initial a) = 1
  transition_nonneg : ∀ n a b, 0 ≤ transition n a b
  transition_sum : ∀ n a, (∑ b, transition n a b) = 1

variable {Ω}

namespace Process

/-- The actual state mass obtained by recursively multiplying the transition kernels. -/
noncomputable def mass (P : Process Ω) : ℕ → Ω → ℝ
  | 0 => P.initial
  | n + 1 => fun b => ∑ a, mass P n a * P.transition n a b

theorem mass_nonneg (P : Process Ω) (n : ℕ) (a : Ω) : 0 ≤ P.mass n a := by
  induction n generalizing a with
  | zero => exact P.initial_nonneg a
  | succ n ih =>
    exact Finset.sum_nonneg (fun b _ => mul_nonneg (ih b) (P.transition_nonneg n b a))

theorem mass_sum (P : Process Ω) (n : ℕ) : (∑ a, P.mass n a) = 1 := by
  induction n with
  | zero => exact P.initial_sum
  | succ n ih =>
    simp only [mass]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, P.transition_sum, mul_one]
    exact ih

noncomputable def expectation (P : Process Ω) (n : ℕ) (f : Ω → ℝ) : ℝ :=
  ∑ a, P.mass n a * f a

noncomputable def conditional (P : Process Ω) (n : ℕ) (a : Ω) (f : Ω → ℝ) : ℝ :=
  ∑ b, P.transition n a b * f b

noncomputable def edgeExpectation (P : Process Ω) (n : ℕ) (f : Ω → Ω → ℝ) : ℝ :=
  P.expectation n (fun a => P.conditional n a (f a))

theorem expectation_const (P : Process Ω) (n : ℕ) (c : ℝ) :
    P.expectation n (fun _ => c) = c := by
  simp only [expectation, ← Finset.sum_mul, P.mass_sum, one_mul]

theorem expectation_add (P : Process Ω) (n : ℕ) (f g : Ω → ℝ) :
    P.expectation n (fun a => f a + g a) = P.expectation n f + P.expectation n g := by
  simp only [expectation, mul_add, Finset.sum_add_distrib]

theorem conditional_add (P : Process Ω) (n : ℕ) (a : Ω) (f g : Ω → ℝ) :
    P.conditional n a (fun b => f b + g b) =
      P.conditional n a f + P.conditional n a g := by
  simp only [conditional, mul_add, Finset.sum_add_distrib]

/-- The finite tower identity follows from the recursive mass, not an assumed expectation law. -/
theorem expectation_succ (P : Process Ω) (n : ℕ) (f : Ω → ℝ) :
    P.expectation (n + 1) f = P.expectation n (fun a => P.conditional n a f) := by
  simp only [expectation, conditional, mass, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem expectation_eq_of_eq_on_support (P : Process Ω) (n : ℕ) {f g : Ω → ℝ}
    (h : ∀ a, 0 < P.mass n a → f a = g a) : P.expectation n f = P.expectation n g := by
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : 0 < P.mass n a
  · rw [h a ha]
  · have hz : P.mass n a = 0 := le_antisymm (le_of_not_gt ha) (P.mass_nonneg n a)
    simp only [hz, zero_mul]

theorem expectation_le_of_le_on_support (P : Process Ω) (n : ℕ) {f g : Ω → ℝ}
    (h : ∀ a, 0 < P.mass n a → f a ≤ g a) : P.expectation n f ≤ P.expectation n g := by
  apply Finset.sum_le_sum
  intro a _
  by_cases ha : 0 < P.mass n a
  · exact mul_le_mul_of_nonneg_left (h a ha) ha.le
  · have hz : P.mass n a = 0 := le_antisymm (le_of_not_gt ha) (P.mass_nonneg n a)
    simp only [hz, zero_mul, le_refl]

end Process

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The local squared-norm identity uses the actual weighted mean-zero increment. -/
theorem weighted_norm_sq_add (w : Ω → ℝ) (d : Ω → E) (x : E)
    (hw : (∑ b, w b) = 1) (hd : (∑ b, w b • d b) = 0) :
    (∑ b, w b * ‖x + d b‖ ^ 2) = ‖x‖ ^ 2 + ∑ b, w b * ‖d b‖ ^ 2 := by
  have hi : (∑ b, w b * inner ℝ x (d b)) = 0 := by
    simp_rw [← real_inner_smul_right]
    rw [← inner_sum, hd, inner_zero_right]
  have hc : (∑ b, w b * (2 * inner ℝ x (d b))) =
      2 * ∑ b, w b * inner ℝ x (d b) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    ring
  simp only [norm_add_sq_real, mul_add, Finset.sum_add_distrib]
  rw [← Finset.sum_mul, hw, one_mul, hc, hi]
  ring

namespace Process

/-- The next position minus the current position, rather than an unrelated increment variable. -/
def increment (X : ℕ → Ω → E) (n : ℕ) (a b : Ω) : E := X (n + 1) b - X n a

noncomputable def incrementVariance (P : Process Ω) (X : ℕ → Ω → E) (n : ℕ) : ℝ :=
  P.edgeExpectation n (fun a b => ‖increment X n a b‖ ^ 2)

/-- One step of the squared-norm identity, with centering required only on reachable states. -/
theorem norm_sq_step (P : Process Ω) (X : ℕ → Ω → E) (n : ℕ)
    (hcenter : ∀ a, 0 < P.mass n a →
      (∑ b, P.transition n a b • increment X n a b) = 0) :
    P.expectation (n + 1) (fun b => ‖X (n + 1) b‖ ^ 2) =
      P.expectation n (fun a => ‖X n a‖ ^ 2) + P.incrementVariance X n := by
  rw [P.expectation_succ]
  calc
    _ = P.expectation n (fun a => ‖X n a‖ ^ 2 +
        P.conditional n a (fun b => ‖increment X n a b‖ ^ 2)) := by
      apply P.expectation_eq_of_eq_on_support
      intro a ha
      have h := weighted_norm_sq_add (P.transition n a) (increment X n a)
        (X n a) (P.transition_sum n a) (hcenter a ha)
      simpa only [increment, add_sub_cancel, conditional] using h
    _ = _ := P.expectation_add n _ _

end Process

/-- Finite telescoping of exact scalar increments. -/
theorem telescope_eq (A B : ℕ → ℝ) (N : ℕ) :
    (∀ n < N, A (n + 1) = A n + B n) → A N = A 0 + ∑ n ∈ Finset.range N, B n := by
  induction N with
  | zero => intro _; simp
  | succ N ih =>
    intro h
    rw [h N (Nat.lt_succ_self N), ih (fun n hn => h n (Nat.lt_succ_of_lt hn)),
      Finset.sum_range_succ]
    ring

/-- Finite telescoping with a separately accumulated paid loss and allowance. -/
theorem telescope_le (A paid budget : ℕ → ℝ) (N : ℕ) :
    (∀ n < N, A (n + 1) + paid n ≤ A n + budget n) →
      A N + ∑ n ∈ Finset.range N, paid n ≤ A 0 + ∑ n ∈ Finset.range N, budget n := by
  induction N with
  | zero => intro _; simp
  | succ N ih =>
    intro h
    have hp := ih (fun n hn => h n (Nat.lt_succ_of_lt hn))
    have hn := h N (Nat.lt_succ_self N)
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    linarith

namespace Process

/-- Expected endpoint norm squared equals initial energy plus accumulated conditional variance. -/
theorem norm_sq_telescope (P : Process Ω) (X : ℕ → Ω → E) (N : ℕ)
    (hcenter : ∀ n < N, ∀ a, 0 < P.mass n a →
      (∑ b, P.transition n a b • increment X n a b) = 0) :
    P.expectation N (fun a => ‖X N a‖ ^ 2) =
      P.expectation 0 (fun a => ‖X 0 a‖ ^ 2) +
        ∑ n ∈ Finset.range N, P.incrementVariance X n := by
  apply telescope_eq (fun n => P.expectation n (fun a => ‖X n a‖ ^ 2))
    (P.incrementVariance X) N
  intro n hn
  exact P.norm_sq_step X n (hcenter n hn)

theorem norm_sq_telescope_of_initial (P : Process Ω) (X : ℕ → Ω → E) (N : ℕ) (x₀ : E)
    (hinit : ∀ a, 0 < P.mass 0 a → X 0 a = x₀)
    (hcenter : ∀ n < N, ∀ a, 0 < P.mass n a →
      (∑ b, P.transition n a b • increment X n a b) = 0) :
    P.expectation N (fun a => ‖X N a‖ ^ 2) =
      ‖x₀‖ ^ 2 + ∑ n ∈ Finset.range N, P.incrementVariance X n := by
  rw [P.norm_sq_telescope X N hcenter]
  have hi : P.expectation 0 (fun a => ‖X 0 a‖ ^ 2) = ‖x₀‖ ^ 2 := by
    calc
      _ = P.expectation 0 (fun _ => ‖x₀‖ ^ 2) :=
        P.expectation_eq_of_eq_on_support 0 (fun a ha => by rw [hinit a ha])
      _ = _ := P.expectation_const 0 _
  rw [hi]

/-- The scalar martingale second moment, with actual differences as its increments. -/
theorem scalar_second_moment (P : Process Ω) (M : ℕ → Ω → ℝ) (N : ℕ)
    (hcenter : ∀ n < N, ∀ a, 0 < P.mass n a →
      (∑ b, P.transition n a b * (M (n + 1) b - M n a)) = 0) :
    P.expectation N (fun a => (M N a) ^ 2) =
      P.expectation 0 (fun a => (M 0 a) ^ 2) +
        ∑ n ∈ Finset.range N,
          P.edgeExpectation n (fun a b => (M (n + 1) b - M n a) ^ 2) := by
  have hc : ∀ n < N, ∀ a, 0 < P.mass n a →
      (∑ b, P.transition n a b • increment M n a b) = 0 := by
    intro n hn a ha
    simpa only [increment, smul_eq_mul] using hcenter n hn a ha
  simpa only [incrementVariance, increment, Real.norm_eq_abs, sq_abs] using
    P.norm_sq_telescope M N hc

theorem scalar_second_moment_of_zero (P : Process Ω) (M : ℕ → Ω → ℝ) (N : ℕ)
    (hinit : ∀ a, 0 < P.mass 0 a → M 0 a = 0)
    (hcenter : ∀ n < N, ∀ a, 0 < P.mass n a →
      (∑ b, P.transition n a b * (M (n + 1) b - M n a)) = 0) :
    P.expectation N (fun a => (M N a) ^ 2) =
      ∑ n ∈ Finset.range N,
        P.edgeExpectation n (fun a b => (M (n + 1) b - M n a) ^ 2) := by
  rw [P.scalar_second_moment M N hcenter]
  have hzero : P.expectation 0 (fun a => (M 0 a) ^ 2) = 0 := by
    calc
      _ = P.expectation 0 (fun _ => 0) := P.expectation_eq_of_eq_on_support 0
        (fun a ha => by rw [hinit a ha]; norm_num)
      _ = _ := P.expectation_const 0 0
  rw [hzero, zero_add]

theorem scalar_second_moment_le_budget (P : Process Ω) (M : ℕ → Ω → ℝ)
    (v : ℕ → Ω → ℝ) (N : ℕ)
    (hinit : ∀ a, 0 < P.mass 0 a → M 0 a = 0)
    (hcenter : ∀ n < N, ∀ a, 0 < P.mass n a →
      (∑ b, P.transition n a b * (M (n + 1) b - M n a)) = 0)
    (hvar : ∀ n < N, ∀ a, 0 < P.mass n a →
      P.conditional n a (fun b => (M (n + 1) b - M n a) ^ 2) ≤ v n a) :
    P.expectation N (fun a => (M N a) ^ 2) ≤
      ∑ n ∈ Finset.range N, P.expectation n (v n) := by
  rw [P.scalar_second_moment_of_zero M N hinit hcenter]
  apply Finset.sum_le_sum
  intro n hn
  exact P.expectation_le_of_le_on_support n (hvar n (Finset.mem_range.mp hn))

/-- A conditional paid drift estimate lifts to one unconditional step. -/
theorem paid_drift_step (P : Process Ω) (F : ℕ → Ω → ℝ)
    (paid : ℕ → Ω → Ω → ℝ) (budget : ℕ → Ω → ℝ) (n : ℕ)
    (hstep : ∀ a, 0 < P.mass n a →
      P.conditional n a (fun b => F (n + 1) b + paid n a b) ≤ F n a + budget n a) :
    P.expectation (n + 1) (F (n + 1)) + P.edgeExpectation n (paid n) ≤
      P.expectation n (F n) + P.expectation n (budget n) := by
  change P.expectation (n + 1) (F (n + 1)) +
    P.expectation n (fun a => P.conditional n a (paid n a)) ≤ _
  rw [P.expectation_succ, ← P.expectation_add, ← P.expectation_add]
  apply P.expectation_le_of_le_on_support
  intro a ha
  rw [← P.conditional_add]
  exact hstep a ha

/-- All paid losses can be accumulated over a finite horizon without optional stopping. -/
theorem paid_drift_telescope (P : Process Ω) (F : ℕ → Ω → ℝ)
    (paid : ℕ → Ω → Ω → ℝ) (budget : ℕ → Ω → ℝ) (N : ℕ)
    (hstep : ∀ n < N, ∀ a, 0 < P.mass n a →
      P.conditional n a (fun b => F (n + 1) b + paid n a b) ≤ F n a + budget n a) :
    P.expectation N (F N) + ∑ n ∈ Finset.range N, P.edgeExpectation n (paid n) ≤
      P.expectation 0 (F 0) + ∑ n ∈ Finset.range N, P.expectation n (budget n) := by
  apply telescope_le (fun n => P.expectation n (F n))
    (fun n => P.edgeExpectation n (paid n)) (fun n => P.expectation n (budget n)) N
  intro n hn
  exact P.paid_drift_step F paid budget n (hstep n hn)

/-- The version with no separately paid loss. -/
theorem drift_telescope (P : Process Ω) (F : ℕ → Ω → ℝ)
    (budget : ℕ → Ω → ℝ) (N : ℕ)
    (hstep : ∀ n < N, ∀ a, 0 < P.mass n a →
      P.conditional n a (F (n + 1)) ≤ F n a + budget n a) :
    P.expectation N (F N) ≤
      P.expectation 0 (F 0) + ∑ n ∈ Finset.range N, P.expectation n (budget n) := by
  have hp : ∀ n < N, ∀ a, 0 < P.mass n a →
      P.conditional n a (fun b => F (n + 1) b + (0 : ℝ)) ≤ F n a + budget n a := by
    simpa only [add_zero] using hstep
  simpa only [edgeExpectation, conditional, expectation, mul_zero, Finset.sum_const_zero,
    add_zero] using P.paid_drift_telescope F (fun _ _ _ => 0) budget N hp

noncomputable def vectorExpectation (P : Process Ω) (n : ℕ) (f : Ω → E) : E :=
  ∑ a, P.mass n a • f a

theorem vectorExpectation_succ (P : Process Ω) (n : ℕ) (f : Ω → E) :
    P.vectorExpectation (n + 1) f =
      P.vectorExpectation n (fun a => ∑ b, P.transition n a b • f b) := by
  simp only [vectorExpectation, mass, Finset.sum_smul, Finset.smul_sum, mul_smul]
  rw [Finset.sum_comm]

/-- Centering preserves the vector mean, including the affine term used to anchor the potential. -/
theorem vectorExpectation_step (P : Process Ω) (X : ℕ → Ω → E) (n : ℕ)
    (hcenter : ∀ a, 0 < P.mass n a →
      (∑ b, P.transition n a b • increment X n a b) = 0) :
    P.vectorExpectation (n + 1) (X (n + 1)) = P.vectorExpectation n (X n) := by
  rw [P.vectorExpectation_succ]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : 0 < P.mass n a
  · have hc := hcenter a ha
    simp only [increment, smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul,
      P.transition_sum, one_smul, sub_eq_zero] at hc
    change P.mass n a • (∑ b, P.transition n a b • X (n + 1) b) = _
    rw [hc]
  · have hz : P.mass n a = 0 := le_antisymm (le_of_not_gt ha) (P.mass_nonneg n a)
    simp only [hz, zero_smul]

theorem vectorExpectation_telescope (P : Process Ω) (X : ℕ → Ω → E) (N : ℕ) :
    (∀ n < N, ∀ a, 0 < P.mass n a →
      (∑ b, P.transition n a b • increment X n a b) = 0) →
      P.vectorExpectation N (X N) = P.vectorExpectation 0 (X 0) := by
  induction N with
  | zero => intro _; rfl
  | succ N ih =>
    intro hc
    rw [P.vectorExpectation_step X N (hc N (Nat.lt_succ_self N))]
    exact ih (fun n hn => hc n (Nat.lt_succ_of_lt hn))

variable [DecidableEq Ω]

/-- A deterministic initial root with an arbitrary normalized adaptive kernel. -/
noncomputable def ofRoot (root : Ω) (p : ℕ → Ω → Ω → ℝ)
    (hp : ∀ n a b, 0 ≤ p n a b) (hsum : ∀ n a, (∑ b, p n a b) = 1) : Process Ω where
  initial a := if a = root then 1 else 0
  transition := p
  initial_nonneg a := by split_ifs <;> norm_num
  initial_sum := by simp
  transition_nonneg := hp
  transition_sum := hsum

/-- An absorbed state has a deterministic self-transition. -/
def IsAbsorbingAt (P : Process Ω) (n : ℕ) (a : Ω) : Prop :=
  ∀ b, P.transition n a b = if b = a then 1 else 0

theorem conditional_of_absorbing (P : Process Ω) (n : ℕ) (a : Ω)
    (ha : P.IsAbsorbingAt n a) (f : Ω → ℝ) : P.conditional n a f = f a := by
  simp only [IsAbsorbingAt] at ha
  simp [conditional, ha]

theorem paid_drift_zero_of_absorbing (P : Process Ω) (F : ℕ → Ω → ℝ)
    (paid : ℕ → Ω → Ω → ℝ) (n : ℕ) (a : Ω)
    (ha : P.IsAbsorbingAt n a) (hF : F (n + 1) a = F n a) (hp : paid n a a = 0) :
    P.conditional n a (fun b => F (n + 1) b + paid n a b) = F n a := by
  rw [P.conditional_of_absorbing n a ha, hF, hp, add_zero]

theorem centered_of_absorbing (P : Process Ω) (X : ℕ → Ω → E) (n : ℕ) (a : Ω)
    (ha : P.IsAbsorbingAt n a) (hx : X (n + 1) a = X n a) :
    (∑ b, P.transition n a b • increment X n a b) = 0 := by
  simp only [IsAbsorbingAt] at ha
  simp [ha, increment, hx]

omit [InnerProductSpace ℝ E] in
theorem variance_zero_of_absorbing (P : Process Ω) (X : ℕ → Ω → E) (n : ℕ) (a : Ω)
    (ha : P.IsAbsorbingAt n a) (hx : X (n + 1) a = X n a) :
    P.conditional n a (fun b => ‖increment X n a b‖ ^ 2) = 0 := by
  rw [P.conditional_of_absorbing n a ha]
  simp only [increment, hx, sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow]

end Process
end FiniteProcessMoments
end MatrixSpencer
