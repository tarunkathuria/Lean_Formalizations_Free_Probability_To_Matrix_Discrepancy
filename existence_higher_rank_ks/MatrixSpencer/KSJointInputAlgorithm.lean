import MatrixSpencer.KSJointBoundsToTaylor
import MatrixSpencer.KSDebitTaylorAlgorithm

/-!
# The input-scaled finite algorithm from actual joint derivative bounds

The primitive size input is the squared Euclidean norm of each original
vector. The atom norm bound is proved from it. A scalar joint cap `B` fixes
the actual Taylor budget, hence the controller's step, numerical tolerances
and finite cutoff. The algorithm and its literal `isSome` event remain those
of `KSDebitInputAlgorithm`.

This is an intermediate theorem: the actual joint second-through-fourth
derivative certificate remains a hypothesis. No completed input-only
algorithm or runtime theorem is asserted.
-/

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSJointInputAlgorithm

open KSDebitInputAlgorithm
variable {N d : ℕ} [Nonempty (Fin d)]

/-- The joint cap selects the actual numerical algorithm's Taylor budget. -/
def taylorBudget (N d : ℕ) (ε B : ℝ) : ℝ :=
  KSTaylorBudget.budget N (Real.sqrt ε) (ksRegularizerScale ε (Fin d)) B

theorem taylorBudget_pos (N : ℕ) {ε B : ℝ} (hε : 0 < ε) (hB : 0 ≤ B) :
    0 < taylorBudget N d ε B :=
  KSTaylorBudget.budget_pos N (δ := Real.sqrt ε) hB (ksRegularizerScale_pos (n := Fin d) hε)

/-- Only actual joint derivative caps remain beyond the primitive inputs. -/
abbrev InputJointBounds (v : Fin N → Fin d → ℂ) (ε B : ℝ) (hd : 0 < d) : Prop :=
  KSJointBoundsToTaylor.JointBounds v (Real.sqrt ε) (debitTolerance N ε)
    (ksRegularizerScale ε (Fin d)) B hd

omit [Nonempty (Fin d)] in
/-- Rank-one operator norms equal the primitive squared Euclidean vector norms. -/
theorem atom_bound_of_vector_size (v : Fin N → Fin d → ℂ) {ε : ℝ}
    (hsize : ∀ i, ‖(WithLp.toLp 2 (v i) : EuclideanSpace ℂ (Fin d))‖ ^ 2 ≤ ε) :
    ∀ i, ‖KSRankOne.atom (v i)‖ ≤ ε := by
  intro i
  rw [KSRankOne.atom_norm, KSRankOne.realTrace_atom_eq_norm_sq]
  exact hsize i

/-- Query and movement Taylor bounds follow from the actual joint certificate. -/
theorem taylorBounds (v : Fin N → Fin d → ℂ) {ε B : ℝ}
    (hε : 0 < ε) (hB : 0 ≤ B) (hd : 0 < d) (hJoint : InputJointBounds v ε B hd) :
    KSDebitTaylorAlgorithm.TaylorBounds v ε (taylorBudget N d ε B) hd :=
  KSJointBoundsToTaylor.remainingTaylorBounds v (Real.sqrt_pos.mpr hε)
    (ksRegularizerScale_pos (n := Fin d) hε) hB hd hJoint

/-- Repeated actual finite attempts succeed with the explicit geometric bound. -/
theorem successProbability_ge (v : Fin N → Fin d → ℂ) {ε B : ℝ}
    (hε : 0 < ε) (hB : 0 ≤ B) (hd : 0 < d)
    (hparseval : (∑ i, KSRankOne.atom (v i)) = 1)
    (hsize : ∀ i, ‖(WithLp.toLp 2 (v i) : EuclideanSpace ℂ (Fin d))‖ ^ 2 ≤ ε)
    (hJoint : InputJointBounds v ε B hd) (r : ℕ) :
    1 - ((15 : ℝ) / 56) ^ r ≤
      successProbability v hε (taylorBudget_pos (d := d) N hε hB).le hd r :=
  KSDebitTaylorAlgorithm.successProbability_ge v hε (taylorBudget_pos (d := d) N hε hB).le hd
    hparseval (atom_bound_of_vector_size v hsize) (taylorBounds v hε hB hd hJoint) r

/-- In particular, one actual finite attempt succeeds with probability at least `41/56`. -/
theorem one_attempt_success (v : Fin N → Fin d → ℂ) {ε B : ℝ}
    (hε : 0 < ε) (hB : 0 ≤ B) (hd : 0 < d)
    (hparseval : (∑ i, KSRankOne.atom (v i)) = 1)
    (hsize : ∀ i, ‖(WithLp.toLp 2 (v i) : EuclideanSpace ℂ (Fin d))‖ ^ 2 ≤ ε)
    (hJoint : InputJointBounds v ε B hd) :
    (41 : ℝ) / 56 ≤ successProbability v hε (taylorBudget_pos (d := d) N hε hB).le hd 1 :=
  KSDebitTaylorAlgorithm.one_attempt_success v hε (taylorBudget_pos (d := d) N hε hB).le hd
    hparseval (atom_bound_of_vector_size v hsize) (taylorBounds v hε hB hd hJoint)

/-- The event is literally a returned `some`, weighted by the actual finite draw distribution. -/
theorem output_event_probability_ge (v : Fin N → Fin d → ℂ) {ε B : ℝ}
    (hε : 0 < ε) (hB : 0 ≤ B) (hd : 0 < d)
    (hparseval : (∑ i, KSRankOne.atom (v i)) = 1)
    (hsize : ∀ i, ‖(WithLp.toLp 2 (v i) : EuclideanSpace ℂ (Fin d))‖ ^ 2 ≤ ε)
    (hJoint : InputJointBounds v ε B hd) (r : ℕ) :
    1 - ((15 : ℝ) / 56) ^ r ≤
      ∑ z : Draws v hε (taylorBudget_pos (d := d) N hε hB).le hd r,
        KSDebitWalkRetry.FiniteRetry.weight
          (KSDebitWalkRun.run (controller v hε (taylorBudget_pos (d := d) N hε hB).le hd)
            (cutoff N ε (taylorBudget N d ε B))
            (KSDebitWalkRun.initialState (controller v hε (taylorBudget_pos (d := d) N hε hB).le hd))).leafWeight r z *
          (if (output v hε (taylorBudget_pos (d := d) N hε hB).le hd r z).isSome then 1 else 0) := by
  rw [← successProbability_eq_output_event]
  exact successProbability_ge v hε hB hd hparseval hsize hJoint r

/-- Soundness of the same actual output requires no joint derivative certificate. -/
theorem output_sound (v : Fin N → Fin d → ℂ) {ε B : ℝ}
    (hε : 0 < ε) (hB : 0 ≤ B) (hd : 0 < d) (r : ℕ)
    (z : Draws v hε (taylorBudget_pos (d := d) N hε hB).le hd r) (σ : Fin N → ℝ)
    (hout : output v hε (taylorBudget_pos (d := d) N hε hB).le hd r z = some σ) :
    (∀ i, IsSign (σ i)) ∧
      ‖∑ i, σ i • KSRankOne.atom (v i)‖ ≤ 9 * (16 * Real.sqrt 2 + 5) * Real.sqrt ε :=
  KSDebitInputAlgorithm.output_sound v hε (taylorBudget_pos (d := d) N hε hB).le hd r z σ hout

/-- The primitive-input, joint-cap-conditional guarantee for the unchanged finite algorithm. -/
theorem algorithm_guarantee_of_jointBounds (v : Fin N → Fin d → ℂ) {ε B : ℝ}
    (hε : 0 < ε) (hB : 0 ≤ B) (hd : 0 < d)
    (hparseval : (∑ i, KSRankOne.atom (v i)) = 1)
    (hsize : ∀ i, ‖(WithLp.toLp 2 (v i) : EuclideanSpace ℂ (Fin d))‖ ^ 2 ≤ ε)
    (hJoint : InputJointBounds v ε B hd) :
    (∀ (r : ℕ) (z : Draws v hε (taylorBudget_pos (d := d) N hε hB).le hd r) (σ : Fin N → ℝ),
      output v hε (taylorBudget_pos (d := d) N hε hB).le hd r z = some σ →
      (∀ i, IsSign (σ i)) ∧
        ‖∑ i, σ i • KSRankOne.atom (v i)‖ ≤ 9 * (16 * Real.sqrt 2 + 5) * Real.sqrt ε) ∧
    ∀ r : ℕ, 1 - ((15 : ℝ) / 56) ^ r ≤
      successProbability v hε (taylorBudget_pos (d := d) N hε hB).le hd r := by
  exact ⟨output_sound v hε hB hd, successProbability_ge v hε hB hd hparseval hsize hJoint⟩

end MatrixSpencer.KSJointInputAlgorithm
