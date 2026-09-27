import AugmentedHigherRankKS.FourBlockOptimizerBranch
import AugmentedHigherRankKS.FourBlockStrongConcavity
import AugmentedHigherRankKS.EnvelopeThird
import MatrixSpencer.KSActualEnvelope

/-! Third derivative bound for the actual optimized four-block potential. -/
noncomputable section
set_option synthInstance.maxHeartbeats 200000
open Matrix MatrixSpencer HigherRankKS Filter Set
open scoped Topology ContDiff BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace AugmentedHigherRankKS
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
local instance envelopeThirdCStar : CStarAlgebra (Matrix (FourSpin n) (FourSpin n) ℂ) := {}
local instance : NormedAddCommGroup (densityTangent (n := FourSpin n)) := inferInstance
local instance : NormedSpace ℝ (densityTangent (n := FourSpin n)) := inferInstance
/-- Quantitative envelope regularity with genuine objective derivative norms.
The optimizing branch, stationarity and θ/2 coercivity are conclusions of the
matrix objective, not assumptions. -/
theorem potential_third_le
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (k : ℕ) (hk : 1 ≤ k) (θ : ℝ) (hθ : 0 < θ)
    (H : ℝ → Matrix (FourSpin n) (FourSpin n) ℂ) (c : ℝ → ι → ℝ)
    (hH : ContDiffAt ℝ ∞ H 0) (hcs : ContDiffAt ℝ ∞ c 0)
    (hc : ∀ i, 0 < c 0 i)
    (S : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ))
    (hS : (S : Matrix (FourSpin n) (FourSpin n) ℂ) ∈ densitySet)
    (hmax : ∀ T ∈ densitySet, objective (H 0) A ((1 : ℝ) / 2 ^ k) (c 0) θ T ≤
      objective (H 0) A ((1 : ℝ) / 2 ^ k) (c 0) θ S)
    {B2 B3 : ℝ} (hB2 : 0 ≤ B2) (hB3 : 0 ≤ B3)
    (h2 : KSActualEnvelope.secondNorm (chartObjective H A ((1 : ℝ) / 2 ^ k) c θ S) (0, 0) ≤ B2)
    (h3 : KSActualEnvelope.thirdNorm (chartObjective H A ((1 : ℝ) / 2 ^ k) c θ S) (0, 0) ≤ B3) :
    |iteratedDeriv 3 (fun t => potential (H t) A ((1 : ℝ) / 2 ^ k) (c t) θ) 0| ≤
      B3 * (1 + B2 / (θ / 2)) ^ 3 := by
  obtain ⟨g, hg0, hg, hF, hstat, hvalue⟩ :=
    exists_local_optimizer_branch A hA k hk θ hθ H c hH hcs hc S hS hmax
  have hβ : 0 < (1 : ℝ) / 2 ^ k := by positivity
  have hβ1 : (1 : ℝ) / 2 ^ k < 1 := by
    apply (div_lt_one (by positivity)).mpr
    exact one_lt_pow₀ (by norm_num) (by omega)
  have hSpos := maximizer_posDef (H 0) A hβ hβ1 (fun i => (hc i).le) hθ hS hmax
  have hF2 := hF.of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have hcoercive := chartObjective_strongConcavity A hA k hk θ hθ H c hc S hSpos hS.2 hF2
  have henv := EnvelopeThird.value_third_le_at g hg
    (chartObjective H A ((1 : ℝ) / 2 ^ k) c θ S)
    (by simpa only [hg0] using hF) hstat (show 0 < θ / 2 by positivity) hB2 hB3
    (by simpa only [hg0] using h2) (by simpa only [hg0] using h3)
    (by simpa only [hg0] using hcoercive)
  rw [hvalue.iteratedDeriv_eq 3]
  exact henv

theorem potential_second_abs_le
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (k : ℕ) (hk : 1 ≤ k) (θ : ℝ) (hθ : 0 < θ)
    (H : ℝ → Matrix (FourSpin n) (FourSpin n) ℂ) (c : ℝ → ι → ℝ)
    (hH : ContDiffAt ℝ ∞ H 0) (hcs : ContDiffAt ℝ ∞ c 0)
    (hc : ∀ i, 0 < c 0 i)
    (S : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ))
    (hS : (S : Matrix (FourSpin n) (FourSpin n) ℂ) ∈ densitySet)
    (hmax : ∀ T ∈ densitySet, objective (H 0) A ((1 : ℝ) / 2 ^ k) (c 0) θ T ≤
      objective (H 0) A ((1 : ℝ) / 2 ^ k) (c 0) θ S)
    {B2 : ℝ} (hB2 : 0 ≤ B2)
    (h2 : KSActualEnvelope.secondNorm (chartObjective H A ((1 : ℝ) / 2 ^ k) c θ S) (0, 0) ≤ B2) :
    |iteratedDeriv 2 (fun t => potential (H t) A ((1 : ℝ) / 2 ^ k) (c t) θ) 0| ≤
      B2 * (1 + B2 / (θ / 2)) ^ 2 := by
  obtain ⟨g, hg0, hg, hF, hstat, hvalue⟩ :=
    exists_local_optimizer_branch A hA k hk θ hθ H c hH hcs hc S hS hmax
  have hβ : 0 < (1 : ℝ) / 2 ^ k := by positivity
  have hβ1 : (1 : ℝ) / 2 ^ k < 1 := by
    apply (div_lt_one (by positivity)).mpr
    exact one_lt_pow₀ (by norm_num) (by omega)
  have hSpos := maximizer_posDef (H 0) A hβ hβ1 (fun i => (hc i).le) hθ hS hmax
  have hF2 := hF.of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have hcoercive := chartObjective_strongConcavity A hA k hk θ hθ H c hc S hSpos hS.2 hF2
  have henv := EnvelopeThird.value_second_le_at g hg
    (chartObjective H A ((1 : ℝ) / 2 ^ k) c θ S)
    (by simpa only [hg0] using hF) hstat (show 0 < θ / 2 by positivity) hB2
    (by simpa only [hg0] using h2)
    (by simpa only [hg0] using hcoercive)
  rw [hvalue.iteratedDeriv_eq 2]
  exact henv

end AugmentedHigherRankKS
