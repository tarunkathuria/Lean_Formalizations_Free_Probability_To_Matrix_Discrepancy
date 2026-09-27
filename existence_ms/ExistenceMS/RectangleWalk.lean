import MatrixSpencer.RectangularRidgeEpochFactory
import MatrixSpencer.RectangularRidgeFullAssembly
import MatrixSpencer.RectangularRidgeRetryParameters

/-!
# Mathematical finite run of the revised rectangular walk

The numerical epoch, acceptance and retries are instantiated, not supplied
as correctness hypotheses. This definition accepts only a mathematical value specification. The pure
existence endpoint constructs that specification internally. The output remains
an explicit finite sampler including failures, with confidence exponent `k`
(failure at most `2⁻ᵏ`).
This file keeps the physical type `Fin d`; signed-lift reindexing and the
ordinary two-sided spectral conclusion are a separate pointwise bridge.
-/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace ExistenceMS.RectangleWalk
open MatrixSpencer
open RectangularRidgeEpochInput (margin)
open RectangularRidgeRemainingPotential (liveCount)
open RectangularRidgePhaseAssembly (Point)
open RectangularRidgePhaseProgress (epochCalls)
open RectangularRidgeRetryParameters (retries selected)
open MSManuscriptAdaptive (Sampler)
variable {N d : ℕ} [Nonempty (Fin d)]
local instance ridgePolynomialAlgorithmCStar : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
attribute [local irreducible] MSManuscriptAdaptive.run MSManuscriptBoundedProcess.run

def potential (hN : 1 ≤ N) (A : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀ i, (A i).IsHermitian) : EuclideanSpace ℝ (Fin N) → ℝ :=
  RectangularRidgeRemainingPotential.potential (RectangularRidgeTuning.depth N d hN)
    (RectangularRidgePrimitiveParameters.weight N d hN) (1 / (d : ℝ)) 0 A hA

theorem zero_regular (hN : 1 ≤ N) : CubeRegular (margin N) (0 : EuclideanSpace ℝ (Fin N)) := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hm : margin N < 1 := by
    unfold margin
    apply (div_lt_one (by positivity : 0 < 16384 * (N : ℝ))).mpr
    nlinarith
  exact ⟨by simp, fun _ => Or.inr (by simpa using sub_pos.mpr hm)⟩

def initial (hN : 1 ≤ N) : Point (N := N) (margin N) := ⟨0, zero_regular hN⟩

theorem initial_liveCount (hN : 1 ≤ N) : liveCount (initial hN).val = N := by
  have hz : frozenCoordinates (0 : EuclideanSpace ℝ (Fin N)) = ∅ := by
    ext i
    simp [mem_frozenCoordinates, IsSign]
  simp only [initial, RectangularRidgeRemainingPotential.liveCount,
    RectangularRidgeLiveOwner.count_eq, hz, Finset.card_empty, Nat.sub_zero]

def output (solver : RectangularRidgeConvexValue.Solver) (a : Fin d)
    (A : Fin N → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ i, (A i).IsHermitian)
    (hAn : ∀ i, ‖A i‖ ≤ 1) (hN : 1 ≤ N) (hND : N ≤ d) (k : ℕ) :
    Sampler (Option (Point (N := N) (margin N))) :=
  RectangularRidgeFullAssembly.output (RectangularRidgeTuning.depth N d hN)
    (RectangularRidgePrimitiveParameters.weight N d hN) (1 / (d : ℝ)) 0 A hA hAn
    (RectangularRidgeEpochFactory.factory solver a A hA hAn hN hND (retries N d k))
    (half_pos (RectangularRidgeUniformResponse.duration_positive hN hND))
    (by norm_num) (by positivity) (epochCalls N d hN)
    (RectangularRidgePhaseProgress.epochCalls_sufficient hN hND) (initial hN)

/-- Every returned branch is complete and satisfies the actual remaining
potential ledger, keeping the original accumulated center throughout. -/
theorem output_sound (solver : RectangularRidgeConvexValue.Solver) (a : Fin d)
    (A : Fin N → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ i, (A i).IsHermitian)
    (hAn : ∀ i, ‖A i‖ ≤ 1) (hN : 1 ≤ N) (hND : N ≤ d) (k : ℕ)
    (z : (output solver a A hA hAn hN hND k).Draws) (y : Point (N := N) (margin N))
    (ho : (output solver a A hA hAn hN hND k).value z = some y) :
    liveCount y.val = 0 ∧ potential hN A hA y.val ≤ potential hN A hA 0 +
      4 * (152 * 27 * (RectangularRidgeUniformResponse.coefficient N d hN + 1) + 64) *
        Real.sqrt (N : ℝ) := by
  have hh := RectangularRidgeFullAssembly.output_sound (RectangularRidgeTuning.depth N d hN)
    (RectangularRidgePrimitiveParameters.weight N d hN) (1 / (d : ℝ)) 0 A hA hAn
    (RectangularRidgeEpochFactory.factory solver a A hA hAn hN hND (retries N d k))
    (half_pos (RectangularRidgeUniformResponse.duration_positive hN hND))
    (by norm_num) (by positivity) (epochCalls N d hN)
    (RectangularRidgePhaseProgress.epochCalls_sufficient hN hND) (initial hN) z y ho
  rw [initial_liveCount] at hh
  change liveCount y.val = 0 ∧ potential hN A hA y.val ≤ potential hN A hA 0 +
    4 * ((epochCalls N d hN : ℝ) * 27 + 64) * Real.sqrt (N : ℝ) at hh
  have hc := RectangularRidgePhaseProgress.epochCalls_le hN hND
  have hm := mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg (N : ℝ))
  exact ⟨hh.1, by nlinarith [hh.2]⟩

/-- The numerical walk itself, including acceptance and every failed trial,
returns a completed branch with probability at least `1−2⁻ᵏ`. -/
theorem output_probability (solver : RectangularRidgeConvexValue.Solver) (a : Fin d)
    (A : Fin N → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ i, (A i).IsHermitian)
    (hAn : ∀ i, ‖A i‖ ≤ 1) (hN : 1 ≤ N) (hND : N ≤ d) (k : ℕ) :
    1 - (1 / 2 : ℝ) ^ k ≤ ∑ z, (output solver a A hA hAn hN hND k).weight z *
      (if ((output solver a A hA hAn hN hND k).value z).isSome then 1 else 0) := by
  have hh := RectangularRidgeFullAssembly.output_probability (RectangularRidgeTuning.depth N d hN)
    (RectangularRidgePrimitiveParameters.weight N d hN) (1 / (d : ℝ)) 0 A hA hAn
    (RectangularRidgeEpochFactory.factory solver a A hA hAn hN hND (retries N d k))
    (half_pos (RectangularRidgeUniformResponse.duration_positive hN hND))
    (by norm_num) (by positivity) (epochCalls N d hN)
    (RectangularRidgePhaseProgress.epochCalls_sufficient hN hND) (initial hN)
  have hf := RectangularRidgeRetryParameters.total_failure_le hN hND k
  push_cast at hf
  change 1 - ((N + 1 : ℕ) : ℝ) * ((epochCalls N d hN : ℝ) * (19 / 50 : ℝ) ^ retries N d k) ≤
    ∑ z, (output solver a A hA hAn hN hND k).weight z *
      (if ((output solver a A hA hAn hN hND k).value z).isSome then 1 else 0) at hh
  push_cast at hh
  nlinarith

end ExistenceMS.RectangleWalk
