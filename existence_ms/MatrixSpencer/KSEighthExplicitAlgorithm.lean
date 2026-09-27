import MatrixSpencer.KSEighthAcceptance
import MatrixSpencer.KSDebitWalkRetry

/-!
# Input-only finite eighth-cube Kadison–Singer walk

This endpoint runs the radius-1/8 controller with the original independent
owner source, exact endpoint-deleting preparation, and an actual finite
Jacobi direction at each movement. It returns the first numerically accepted
vertex, rescaled by eight on every original label. The literal finite output
event has probability at least `1-(1/4)^r`. No Taylor, direction, value-report,
optimizer, or progress oracle is an input.

Runtime and bit complexity are not asserted. The real-arithmetic procedure
uses scalar square roots and comparisons and has explicit finite iteration
counts; no extracted machine implementation is supplied by this theorem.
-/

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSEighthExplicitAlgorithm
open KSEighthWalkRun KSEighthInputParameters
namespace Retry
export KSDebitWalkRetry.FiniteRetry (Draws weight weight_nonneg weight_sum firstAccepted
  firstAccepted_sound singleSuccess singleFailure singleFailure_nonneg
  single_success_add_failure successProbability failureProbability
  failureProbability_eq_pow success_add_failure)
end Retry
variable {N d : ℕ}

def trial (v : Fin N → Fin d → ℂ) {ε : ℝ} (hε : 0 < ε) (hd : 0 < d) :=
  let C := controller v hε hd
  run C (cutoff v hε hd) (initialState C)

abbrev Attempt (v : Fin N → Fin d → ℂ) {ε : ℝ} (hε : 0 < ε) (hd : 0 < d) := (trial v hε hd).Leaves
abbrev Draws (v : Fin N → Fin d → ℂ) {ε : ℝ} (hε : 0 < ε) (hd : 0 < d) (r : ℕ) :=
  Retry.Draws (Attempt v hε hd) r

def accept (v : Fin N → Fin d → ℂ) {ε : ℝ} (hε : 0 < ε) (hd : 0 < d)
    (l : Attempt v hε hd) : Bool :=
  KSEighthAcceptance.accepts v ε (controller v hε hd) ((trial v hε hd).leafState l)

/-- The finite first-accepted procedure, returning an explicit failure after `r` attempts. -/
def output (v : Fin N → Fin d → ℂ) {ε : ℝ} (hε : 0 < ε) (hd : 0 < d) (r : ℕ)
    (z : Draws v hε hd r) : Option (Fin N → ℝ) :=
  Retry.firstAccepted (fun l => signing ((trial v hε hd).leafState l)) (accept v hε hd) r z

def drawWeight (v : Fin N → Fin d → ℂ) {ε : ℝ} (hε : 0 < ε) (hd : 0 < d) (r : ℕ)
    (z : Draws v hε hd r) : ℝ := Retry.weight (trial v hε hd).leafWeight r z

theorem drawWeight_nonneg (v : Fin N → Fin d → ℂ) {ε : ℝ} (hε : 0 < ε)
    (hd : 0 < d) (r : ℕ) (z : Draws v hε hd r) : 0 ≤ drawWeight v hε hd r z :=
  Retry.weight_nonneg _ (fun l => ((trial v hε hd).leafWeight_pos l).le) r z

theorem drawWeight_sum (v : Fin N → Fin d → ℂ) {ε : ℝ} (hε : 0 < ε)
    (hd : 0 < d) (r : ℕ) : (∑ z : Draws v hε hd r, drawWeight v hε hd r z) = 1 :=
  Retry.weight_sum _ (trial v hε hd).leafWeight_sum r

/-- Every trajectory endpoint, including failed cutoff leaves, lies in the eighth cube. -/
theorem trial_leaf_mem_cube (v : Fin N → Fin d → ℂ) {ε : ℝ} (hε : 0 < ε) (hd : 0 < d)
    (l : Attempt v hε hd) : ((trial v hε hd).leafState l).coeff ∈ ksCube (1/8) :=
  ((trial v hε hd).leafState l).cube

/-- Every accepted result signs all original labels and has the ordinary operator-norm bound. -/
theorem output_sound (v : Fin N → Fin d → ℂ) {ε : ℝ} (hε : 0 < ε) (hd : 0 < d)
    (r : ℕ) (z : Draws v hε hd r) (σ : Fin N → ℝ) (hout : output v hε hd r z = some σ) :
    (∀ i, IsSign (σ i)) ∧ ‖∑ i, σ i • KSRankOne.atom (v i)‖ ≤ 2048*Real.sqrt ε :=
  Retry.firstAccepted_sound _ _
    (fun σ => (∀ i, IsSign (σ i)) ∧ ‖∑ i, σ i • KSRankOne.atom (v i)‖ ≤ 2048*Real.sqrt ε)
    (fun _l hl => KSEighthAcceptance.accepted_signing_sound v hε _ _ hl) r z σ hout

def successProbability (v : Fin N → Fin d → ℂ) {ε : ℝ} (hε : 0 < ε) (hd : 0 < d) (r : ℕ) : ℝ :=
  ∑ z : Draws v hε hd r, drawWeight v hε hd r z * (if (output v hε hd r z).isSome then 1 else 0)

/-- A quarter failure probability per independent finite attempt. -/
theorem successProbability_ge (v : Fin N → Fin d → ℂ) {ε : ℝ} (hε : 0 < ε) (hd : 0 < d)
    (hparseval : (∑ i, KSRankOne.atom (v i)) = 1)
    (hsize : ∀ i, ‖(WithLp.toLp 2 (v i) : EuclideanSpace ℂ (Fin d))‖^2 ≤ ε) (r : ℕ) :
    1-((1 : ℝ)/4)^r ≤ successProbability v hε hd r := by
  have hs : ∀ i, ‖KSRankOne.atom (v i)‖ ≤ ε := by
    intro i
    rw [KSRankOne.atom_norm, KSRankOne.realTrace_atom_eq_norm_sq]
    exact hsize i
  have htrial := KSEighthAcceptance.probability_ge v hε hd hparseval hs
  let w := (trial v hε hd).leafWeight
  let a := accept v hε hd
  let o := fun l => signing ((trial v hε hd).leafState l)
  have hsum := Retry.single_success_add_failure w (trial v hε hd).leafWeight_sum a
  have hfail : Retry.singleFailure w a ≤ (1 : ℝ)/4 := by
    change (3 : ℝ)/4 ≤ Retry.singleSuccess w a at htrial
    linarith
  have hp := pow_le_pow_left₀ (Retry.singleFailure_nonneg w
    (fun l => ((trial v hε hd).leafWeight_pos l).le) a) hfail r
  have htotal := Retry.success_add_failure w (trial v hε hd).leafWeight_sum o a r
  rw [Retry.failureProbability_eq_pow] at htotal
  change Retry.successProbability w o a r + _ = 1 at htotal
  change 1-((1 : ℝ)/4)^r ≤ Retry.successProbability w o a r
  linarith

/-- Literal finite output-event probability, with only primitive normalized-vector hypotheses. -/
theorem output_event_probability_ge (v : Fin N → Fin d → ℂ) {ε : ℝ} (hε : 0 < ε) (hd : 0 < d)
    (hparseval : (∑ i, KSRankOne.atom (v i)) = 1)
    (hsize : ∀ i, ‖(WithLp.toLp 2 (v i) : EuclideanSpace ℂ (Fin d))‖^2 ≤ ε) (r : ℕ) :
    1-((1 : ℝ)/4)^r ≤ ∑ z : Draws v hε hd r,
      drawWeight v hε hd r z * (if (output v hε hd r z).isSome then 1 else 0) :=
  successProbability_ge v hε hd hparseval hsize r

theorem one_attempt_success (v : Fin N → Fin d → ℂ) {ε : ℝ} (hε : 0 < ε) (hd : 0 < d)
    (hparseval : (∑ i, KSRankOne.atom (v i)) = 1)
    (hsize : ∀ i, ‖(WithLp.toLp 2 (v i) : EuclideanSpace ℂ (Fin d))‖^2 ≤ ε) :
    (3 : ℝ)/4 ≤ successProbability v hε hd 1 := by
  simpa only [pow_one, show (1 : ℝ)-1/4=3/4 by norm_num] using successProbability_ge v hε hd hparseval hsize 1

theorem exists_output (v : Fin N → Fin d → ℂ) {ε : ℝ} (hε : 0 < ε) (hd : 0 < d)
    (hparseval : (∑ i, KSRankOne.atom (v i)) = 1)
    (hsize : ∀ i, ‖(WithLp.toLp 2 (v i) : EuclideanSpace ℂ (Fin d))‖^2 ≤ ε) :
    ∃ z : Draws v hε hd 1, ∃ σ, output v hε hd 1 z = some σ := by
  classical
  have h := one_attempt_success v hε hd hparseval hsize
  by_contra hn
  have hz : ∀ z : Draws v hε hd 1, (output v hε hd 1 z).isSome = false := by
    intro z
    cases he : output v hε hd 1 z with
    | none => rfl
    | some σ => exact False.elim (hn ⟨z,σ,he⟩)
  have he : successProbability v hε hd 1 = 0 := by
    simp only [successProbability, hz, Bool.false_eq_true, ↓reduceIte, mul_zero, Finset.sum_const_zero]
  linarith

/-- The degenerate dimensions/error bound are handled directly, giving total signing existence. -/
theorem exists_full_signing (v : Fin N → Fin d → ℂ) {ε : ℝ} (hε : 0 ≤ ε)
    (hparseval : (∑ i, KSRankOne.atom (v i)) = 1)
    (hsize : ∀ i, ‖(WithLp.toLp 2 (v i) : EuclideanSpace ℂ (Fin d))‖^2 ≤ ε) :
    ∃ σ : Fin N → ℝ, (∀ i, IsSign (σ i)) ∧ ‖∑ i, σ i • KSRankOne.atom (v i)‖ ≤ 2048*Real.sqrt ε := by
  classical
  rcases eq_or_lt_of_le hε with he | he
  · have hz : ∀ i, v i = 0 := by
      intro i
      have hn := hsize i
      have hn0 := norm_nonneg (WithLp.toLp 2 (v i) : EuclideanSpace ℂ (Fin d))
      have hnz : ‖(WithLp.toLp 2 (v i) : EuclideanSpace ℂ (Fin d))‖ = 0 := by nlinarith
      exact WithLp.toLp_injective 2 (norm_eq_zero.mp hnz)
    refine ⟨fun _ => 1, fun _ => by simp [IsSign], ?_⟩
    simp [hz, ← he]
  · by_cases hd : d = 0
    · subst d
      have hz : ∀ i, KSRankOne.atom (v i) = 0 := fun _ => Subsingleton.elim _ _
      refine ⟨fun _ => 1, fun _ => by simp [IsSign], ?_⟩
      simp only [hz, smul_zero, Finset.sum_const_zero, norm_zero]
      positivity
    · obtain ⟨z,σ,ho⟩ := exists_output v he (Nat.pos_of_ne_zero hd) hparseval hsize
      exact ⟨σ, output_sound v he (Nat.pos_of_ne_zero hd) 1 z σ ho⟩

end MatrixSpencer.KSEighthExplicitAlgorithm
