import AugmentedHigherRankKS.FourBlockNormalizedResponse
import AugmentedHigherRankKS.FourBlockPotentialHessian
import AugmentedHigherRankKS.QuadraticReserveCurve

/-! Negative curvature of the actual optimized four-block potential. -/
noncomputable section
open Matrix MatrixSpencer HigherRankKS Set
open scoped Topology ContDiff BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace AugmentedHigherRankKS.Frames
variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
local instance localCurvatureCStar {j : Type*} [Fintype j] [DecidableEq j] :
  CStarAlgebra (Matrix j j ℂ) := {}
open TwoFrames

def debit (A : ι → Matrix n n ℂ) (β : ℝ) (c : ι → ℝ)
    (S : Matrix (FourSpin n) (FourSpin n) ℂ) (h : ι → ℝ) : ℝ :=
  ∑ i, BalancedFrames.transportMass (SupportedSpin.term A β S)
    (SupportedSpin.transport A β c S) i * h i ^ 2

theorem quadratic_direct (A : ι → Matrix n n ℂ) (β : ℝ) (c : ι → ℝ)
    (a : ℝ) (h : ι → ℝ) (S : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ)) :
    PointwiseResponse.direct A β (QuadraticReserveCurve.curve c a h)
      (SupportedSpin.transport A β c S) S / 2 = -a * debit A β c S h := by
  unfold PointwiseResponse.direct debit
  simp only [QuadraticReserveCurve.scalar_second, BalancedFrames.transportMass,
    SupportedSpin.term_pairing, PointwiseResponse.probeValue, SourceDerivative.probe]
  rw [Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem sSup_div_two_le {E : Type*} [Nonempty E] (f : E → ℝ) (b : ℝ)
    (h : ∀ X, f X / 2 ≤ b) : sSup (Set.range f) / 2 ≤ b := by
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
  apply csSup_le (Set.range_nonempty f)
  rintro a ⟨X, rfl⟩
  exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).1 (h X)

/-- The bound is uniform over all density variations, before taking the optimized response. -/
theorem potential_second_le (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) (hne : ∀ i, A i ≠ 0) (k : ℕ) (hk : 1 ≤ k)
    (c : ι → ℝ) (hc : ∀ i, 0 < c i) (x : ι → ℝ) (hx : ∀ i, |x i| ≤ 1)
    (H : Matrix (FourSpin n) (FourSpin n) ℂ) (θ : ℝ) (hθ : 0 < θ) (a : ℝ)
    (S : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ))
    (hS : (S : Matrix (FourSpin n) (FourSpin n) ℂ).PosDef)
    (ht : realTrace (S : Matrix (FourSpin n) (FourSpin n) ℂ) = 1)
    (hmax : ∀ T ∈ densitySet, objective H A ((1 : ℝ) / 2 ^ k) c θ T ≤
      objective H A ((1 : ℝ) / 2 ^ k) c θ S)
    (w y : ι → ℝ)
    (hlegal : (1 - (channel (E A ((1 : ℝ) / 2 ^ k) c S)
      (F A ((1 : ℝ) / 2 ^ k) c S))ᵀ) *ᵥ w =
      (channel (N A ((1 : ℝ) / 2 ^ k) c x S) (F A ((1 : ℝ) / 2 ^ k) c S))ᵀ *ᵥ y) :
    let β := (1 : ℝ) / 2 ^ k
    let σ := 2 * β / (1 + β)
    let h := direction c y
    iteratedDeriv 2 (fun t : ℝ => potential (H+t • coefficientForce A x h)
      A β (QuadraticReserveCurve.curve c a h t) θ) 0 / 2 ≤
      -a * debit A β c S h +
      realTrace (P A β c S * (IndependentLegalResponse.trial (E A β c S)
        (N A β c x S) w y * IndependentLegalResponse.trial (E A β c S)
          (N A β c x S) w y)) / σ := by
  dsimp only
  let β := (1 : ℝ) / 2 ^ k
  let h := direction c y
  let d := QuadraticReserveCurve.curve c a h
  let K := coefficientForce A x h
  have hd : ContDiffAt ℝ ∞ d 0 := (QuadraticReserveCurve.contDiff c a h).contDiffAt
  have hd0 : d 0 = c := QuadraticReserveCurve.curve_zero c a h
  have hdpos : ∀ i, 0 < d 0 i := by simpa only [hd0] using hc
  have hmax' : ∀ T ∈ densitySet, objective ((fun t : ℝ => H+t • K) 0) A β (d 0) θ T ≤
      objective ((fun t : ℝ => H+t • K) 0) A β (d 0) θ S := by
    simpa only [zero_smul, add_zero, hd0] using hmax
  have hs := potential_second_eq_density_response A hA k hk θ hθ (fun t : ℝ => H+t • K) d
    (by fun_prop) hd hdpos S ⟨hS.posSemidef, ht⟩ hmax'
  change iteratedDeriv 2 (fun t : ℝ => potential (H+t • K) A β (d t) θ) 0 / 2 ≤ _
  rw [hs]
  apply sSup_div_two_le
  intro X
  rw [ObjectiveResponse.chart_hessian_eq_affine_second A hA k hk d hd hdpos H K θ S X hS]
  have hn := normalized_objective_second_le A hA hne k hk d
    (hd.of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))) hdpos
    (QuadraticReserveCurve.scalar_deriv_zero c a h) x hx H θ hθ S X hS w y
    (by simpa only [hd0] using hlegal)
  dsimp only at hn
  simpa only [hd0, d, quadratic_direct] using hn

/-- A capped state has a genuine negative direction for the optimized potential.
The source, optimizer, transport and projection bounds are all derived internally. -/
theorem exists_negative_curvature [Nonempty ι] (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) (hne : ∀ i, A i ≠ 0) (k : ℕ) (hk : 1 ≤ k)
    (c : ι → ℝ) (hc : ∀ i, 0 < c i) (x z : ι → ℝ) (hx : ∀ i, |x i| ≤ 1)
    (H : Matrix (FourSpin n) (FourSpin n) ℂ) (θ : ℝ) (hθ : 0 < θ)
    (S : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ))
    (hS : (S : Matrix (FourSpin n) (FourSpin n) ℂ).PosDef)
    (ht : realTrace (S : Matrix (FourSpin n) (FourSpin n) ℂ) = 1)
    (hmax : ∀ T ∈ densitySet, objective H A ((1 : ℝ) / 2 ^ k) c θ T ≤
      objective H A ((1 : ℝ) / 2 ^ k) c θ S)
    (hcap : ∀ i, r A ((1 : ℝ) / 2 ^ k) c S i ^ 2 ≤ 1 / 48)
    {a : ℝ} (ha : 120 / ((1 : ℝ) / 2 ^ k) ≤ a) :
    ∃ h : ι → ℝ, h ≠ 0 ∧ (∑ i, z i * h i) = 0 ∧
      iteratedDeriv 2 (fun t : ℝ => potential (H+t • coefficientForce A x h)
        A ((1 : ℝ) / 2 ^ k) (QuadraticReserveCurve.curve c a h t) θ) 0 <
        -a * debit A ((1 : ℝ) / 2 ^ k) c S h := by
  obtain ⟨w, y, hy, hlegal, hz, hcost⟩ :=
    exists_direction A hA hne k hk c hc x z hx hS hcap ha
  have hp := potential_second_le A hA hne k hk c hc x hx H θ hθ a S hS ht hmax w y hlegal
  refine ⟨direction c y, hy, hz, ?_⟩
  dsimp only at hp hcost
  change _ < (a / 2) * debit A ((1 : ℝ) / 2 ^ k) c S (direction c y) at hcost
  linarith

theorem debit_pos (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (hne : ∀ i, A i ≠ 0) (k : ℕ) (hk : 1 ≤ k) (c : ι → ℝ) (hc : ∀ i, 0 < c i)
    {S : Matrix (FourSpin n) (FourSpin n) ℂ} (hS : S.PosDef)
    {h : ι → ℝ} (hh : h ≠ 0) : 0 < debit A ((1 : ℝ) / 2 ^ k) c S h := by
  have htau := BalancedFrames.transportMass_pos (SupportedSpin.term A ((1 : ℝ) / 2 ^ k) S)
    (SupportedSpin.term_posSemidef A _ hS.posSemidef)
    (fun i => SupportedSpin.term_ne_zero A hA hS k hk i (hne i))
    (SupportedSpin.transport_posDef A hA hc hS k hk)
  apply Finset.sum_pos'
  · intro i _
    exact mul_nonneg (htau i).le (sq_nonneg (h i))
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp hh
    exact ⟨i, Finset.mem_univ i, mul_pos (htau i) (sq_pos_of_ne_zero hi)⟩

end AugmentedHigherRankKS.Frames
