import AugmentedHigherRankKS.FourBlockPointwiseResponse
import AugmentedHigherRankKS.FourBlockFrameDirection

/-! Exact trace identities relating the four-center force to the legal response frame. -/
noncomputable section
open Matrix MatrixSpencer HigherRankKS MatrixSpencer.KSFisher
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace AugmentedHigherRankKS
variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
local instance responseGeometryCStar {j : Type*} [Fintype j] [DecidableEq j] :
  CStarAlgebra (Matrix j j ℂ) := {}

namespace Frames

def coefficientForce (A : ι → Matrix n n ℂ) (x h : ι → ℝ) :
    Matrix (FourSpin n) (FourSpin n) ℂ := ∑ i, h i • forceAtom (x i) (A i)

theorem normalized_force_pairing (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) (k : ℕ) (hk : 1 ≤ k)
    (c : ι → ℝ) (hc : ∀ i, 0 < c i) (x y : ι → ℝ) (hx : ∀ i, |x i| ≤ 1)
    {S : Matrix (FourSpin n) (FourSpin n) ℂ} (hS : S.PosDef)
    (X : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ)) :
    tracePairing (coefficientForce A x (direction c y)) X =
      realTrace (synthesis (N A ((1 : ℝ) / 2 ^ k) c x S) y *
        balancedDensity (SupportedSpin.density A X)
          (SupportedSpin.transport A ((1 : ℝ) / 2 ^ k) c S)) := by
  have hZ := SupportedSpin.transport_posDef A hA hc hS k hk
  change realTrace (coefficientForce A x (direction c y) * (X : Matrix (FourSpin n) (FourSpin n) ℂ)) = _
  simp only [coefficientForce, synthesis, Matrix.sum_mul, Matrix.smul_mul, realTrace_sum,
    realTrace_smul, N, BalancedFrames.measurementFrame, direction]
  apply Finset.sum_congr rfl
  intro i _
  rw [SupportedSpin.force_pairing A hA x hx]
  rw [realTrace_mul_comm (balancedKraus _ _ i), balancedKraus,
    KSBalancedSpin.trace_balanced_pair _ _ hZ, realTrace_mul_comm]
  ring

theorem balanced_variation_isHermitian (A : ι → Matrix n n ℂ) (β : ℝ) (c : ι → ℝ)
    (S : Matrix (FourSpin n) (FourSpin n) ℂ)
    (hZ : (SupportedSpin.transport A β c S).PosDef)
    (X : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ)) :
    (balancedDensity (SupportedSpin.density A X) (SupportedSpin.transport A β c S)).IsHermitian := by
  have hI := (transportInverseSqrt_posDef hZ).isHermitian
  have hX : (SupportedSpin.density A X).IsHermitian :=
    KSSupportSymmetry.compress_isHermitian (sourceEmbedding A) X.property
  change (transportInverseSqrt _ * SupportedSpin.density A X * transportInverseSqrt _).IsHermitian
  rw [Matrix.IsHermitian]
  simp only [Matrix.conjTranspose_mul, hI.eq, hX.eq, Matrix.mul_assoc]

end Frames
end AugmentedHigherRankKS
