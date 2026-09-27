import HigherRankKS.PointwisePaidResponse
import HigherRankKS.SupportedLegalResponse
import HigherRankKS.OwnerCurves
import HigherRankKS.PotentialHessian

/-! The actual normalized Hessian bound, over all full density directions. -/

open Matrix MatrixSpencer Set MatrixSpencer.KSSignSymmetry MatrixSpencer.KSSpinDrift MatrixSpencer.KSFisher
open scoped Topology ContDiff BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

noncomputable section
namespace HigherRankKS.NormalizedHessian

variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
local instance normalizedHessianCStar {l : Type*} [Fintype l] [DecidableEq l] :
    CStarAlgebra (Matrix l l ℂ) := {}

open SupportedFrames SourceProfile PointwiseResponse

omit [DecidableEq ι] in
theorem probeValue_div_mass_eq_q (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (β : ℝ) (x : ι → ℝ) (S : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ)) (i : ι) :
    probeValue A β (SupportedSpin.transport A β (weights β x) S) S i /
      realTrace (spinAtom (A i) * (S : Matrix (n ⊕ n) (n ⊕ n) ℂ)) = q A β x S i := by
  unfold q BalancedFrames.transportMass BalancedFrames.carrierMass
  rw [SupportedSpin.probe_pairing A hA, SupportedSpin.term_pairing]
  rfl

/-- The normalized source budget and actual frame response combine before taking the density supremum. -/
theorem reduced_response_le (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (hne : ∀ i, A i ≠ 0) (k : ℕ) (hk : 1 ≤ k) (x : ι → ℝ)
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1)
    (S X : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ))
    (hS : (S : Matrix (n ⊕ n) (n ⊕ n) ℂ).PosDef)
    (hfixed : conjugate signMatrix (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) = S)
    (w y : ι → ℝ)
    (hlegal : (1 - (TwoFrames.channel (E A ((1 : ℝ) / 2 ^ k) x S)
        (F A ((1 : ℝ) / 2 ^ k) x S))ᵀ) *ᵥ w =
      ((TwoFrames.spinChannel (SupportedSpin.involution A) (E A ((1 : ℝ) / 2 ^ k) x S)
        (F A ((1 : ℝ) / 2 ^ k) x S))ᵀ -
        (TwoFrames.channel (E A ((1 : ℝ) / 2 ^ k) x S)
          (F A ((1 : ℝ) / 2 ^ k) x S))ᵀ * Matrix.diagonal (z A ((1 : ℝ) / 2 ^ k) x S)) *ᵥ y) :
    let β := (1 : ℝ) / 2 ^ k
    let h := coefficientDirection β x y
    let c := OwnerCurves.weights β x h
    let dc := fun i => deriv (fun t => c t i) 0
    let Z := SupportedSpin.transport A β (weights β x) S
    let hp := P_posDef A hA k hk x hx hS
    direct A β c Z S / 2 + (1 - β) / β * budget A β c Z S +
      scalarForce A β dc Z (∑ i, h i • signedLift (A i)) S X -
      β / 2 * SylvesterMetric.energy (P A β x S) hp
        (frameMismatch A β (weights β x) dc Z S X) ≤
      legalUpper ((1 / β) • P A β x S) (SupportedSpin.involution A)
        (E A β x S) (R A β x S)
        (fun i => r A β x S i ^ 2 + (2 / ownerScale β) * z A β x S i ^ 2)
        (z A β x S) (ownerScale β) w y := by
  dsimp only
  let β := (1 : ℝ) / 2 ^ k
  let h := coefficientDirection β x y
  let c := OwnerCurves.weights β x h
  let Z := SupportedSpin.transport A β (weights β x) S
  have hb := normalized_owner_budget A hA hne k hk x y hx S hS
  dsimp only at hb
  have hb' : direct A β c Z S / 2 + (1 - β) / β * budget A β c Z S ≤
      -(∑ i, R A β x S i * r A β x S i ^ 2 * y i ^ 2) -
        (2 / ownerScale β) * (∑ i, R A β x S i * z A β x S i ^ 2 * y i ^ 2) := by
    simpa only [direct, budget, probeValue, c, OwnerCurves.weights_second,
      OwnerCurves.weights_deriv, OwnerCurves.weights_zero] using hb
  have hf := normalized_force_pairing A hA k hk x y hx hS hfixed (X : Matrix (n ⊕ n) (n ⊕ n) ℂ)
  dsimp only at hf
  have hf' : scalarForce A β (fun i => deriv (fun t => c t i) 0) Z
      (∑ i, h i • signedLift (A i)) S X =
      (1 / Real.sqrt (ownerScale β)) * realTrace ((SupportedSpin.involution A * synthesis (E A β x S) y -
        synthesis (E A β x S) (Matrix.diagonal (z A β x S) *ᵥ y)) *
          balancedDensity (SupportedSpin.density A X) Z) := by
    simpa only [scalarForce, c, OwnerCurves.weights_deriv, Z,
      probeValue_div_mass_eq_q A hA] using hf
  have hn := normalized_source A hA hne k hk x y hx hS
  dsimp only at hn
  have hn' : (∑ i, deriv (fun t => c t i) 0 • SupportedSourceMetric.term A β Z i S) =
      (-(1 / Real.sqrt (ownerScale β))) •
        synthesis (F A β x S) (fun i => R A β x S i * z A β x S i * y i) := by
    simpa only [c, OwnerCurves.weights_deriv, SupportedSourceMetric.term, balancedKraus, mul_comm] using hn
  have hl := legal_upper_bound A hA hne k hk x hx hS hfixed w y hlegal
    (X : Matrix (n ⊕ n) (n ⊕ n) ℂ) X.property
  dsimp only at hl
  change direct A β c Z S / 2 + (1 - β) / β * budget A β c Z S +
    scalarForce A β (fun i => deriv (fun t => c t i) 0) Z (∑ i, h i • signedLift (A i)) S X -
    β / 2 * SylvesterMetric.energy (P A β x S) _
      (frameMismatch A β (weights β x) (fun i => deriv (fun t => c t i) 0) Z S X) ≤ _
  rw [hf', frameMismatch, hn']
  exact (sub_le_sub_right (add_le_add_right hb' _) _).trans hl


/-- Every full density variation obeys the actual normalized legal-frame bound. -/
theorem normalized_objective_second_le
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef) (hne : ∀ i, A i ≠ 0)
    (k : ℕ) (hk : 1 ≤ k) (x : ι → ℝ) (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1)
    (H : Matrix (n ⊕ n) (n ⊕ n) ℂ) (θ : ℝ) (hθ : 0 < θ)
    (S X : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ))
    (hS : (S : Matrix (n ⊕ n) (n ⊕ n) ℂ).PosDef)
    (hfixed : conjugate signMatrix (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) = S)
    (w y : ι → ℝ)
    (hlegal : (1 - (TwoFrames.channel (E A ((1 : ℝ) / 2 ^ k) x S)
        (F A ((1 : ℝ) / 2 ^ k) x S))ᵀ) *ᵥ w =
      ((TwoFrames.spinChannel (SupportedSpin.involution A) (E A ((1 : ℝ) / 2 ^ k) x S)
        (F A ((1 : ℝ) / 2 ^ k) x S))ᵀ -
        (TwoFrames.channel (E A ((1 : ℝ) / 2 ^ k) x S)
          (F A ((1 : ℝ) / 2 ^ k) x S))ᵀ * Matrix.diagonal (z A ((1 : ℝ) / 2 ^ k) x S)) *ᵥ y) :
    let β := (1 : ℝ) / 2 ^ k
    let h := coefficientDirection β x y
    iteratedDeriv 2 (fun t : ℝ => hermitianObjective
      (H + t • (∑ i, h i • signedLift (A i))) A β (OwnerCurves.weights β x h t) θ (S + t • X)) 0 / 2 ≤
      legalUpper ((1 / β) • P A β x S) (SupportedSpin.involution A)
        (E A β x S) (R A β x S)
        (fun i => r A β x S i ^ 2 + (2 / ownerScale β) * z A β x S i ^ 2)
        (z A β x S) (ownerScale β) w y := by
  dsimp only
  let β := (1 : ℝ) / 2 ^ k
  let h := coefficientDirection β x y
  let c := OwnerCurves.weights β x h
  have hc : ∀ i, 0 < c 0 i := fun i => by
    simpa only [c, OwnerCurves.weights_zero] using owner_pos (by positivity : 0 < β) (hx i)
  have hcs : ContDiffAt ℝ 2 c 0 := (OwnerCurves.weights_smooth β x h hx).of_le
    (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have hb := PointwiseResponse.objective_second_le A hA hne k hk c hcs hc
    H (∑ i, h i • signedLift (A i)) θ hθ S X hS
  have hn := reduced_response_le A hA hne k hk x hx S X hS hfixed w y hlegal
  dsimp only at hb hn
  apply le_trans hb
  simpa only [c, OwnerCurves.weights_zero, SupportedSourceMetric.balanced,
    SupportedFrames.P, SupportedFrames.weights] using hn

private theorem sSup_div_two_le {E : Type*} [Nonempty E] (f : E → ℝ) (b : ℝ)
    (h : ∀ X, f X / 2 ≤ b) : sSup (Set.range f) / 2 ≤ b := by
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
  apply csSup_le (Set.range_nonempty f)
  rintro a ⟨X, rfl⟩
  exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).1 (h X)

/-- The actual optimized potential obeys the normalized bound on the full density tangent. -/
theorem normalized_potential_second_le
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef) (hne : ∀ i, A i ≠ 0)
    (k : ℕ) (hk : 1 ≤ k) (x : ι → ℝ) (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1)
    (H : Matrix (n ⊕ n) (n ⊕ n) ℂ) (θ : ℝ) (hθ : 0 < θ)
    (S : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ))
    (hS : (S : Matrix (n ⊕ n) (n ⊕ n) ℂ).PosDef)
    (ht : realTrace (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) = 1)
    (hmax : ∀ T ∈ densitySet, objective H A ((1 : ℝ) / 2 ^ k) (weights ((1 : ℝ) / 2 ^ k) x) θ T ≤
      objective H A ((1 : ℝ) / 2 ^ k) (weights ((1 : ℝ) / 2 ^ k) x) θ S)
    (hfixed : conjugate signMatrix (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) = S)
    (w y : ι → ℝ)
    (hlegal : (1 - (TwoFrames.channel (E A ((1 : ℝ) / 2 ^ k) x S)
        (F A ((1 : ℝ) / 2 ^ k) x S))ᵀ) *ᵥ w =
      ((TwoFrames.spinChannel (SupportedSpin.involution A) (E A ((1 : ℝ) / 2 ^ k) x S)
        (F A ((1 : ℝ) / 2 ^ k) x S))ᵀ -
        (TwoFrames.channel (E A ((1 : ℝ) / 2 ^ k) x S)
          (F A ((1 : ℝ) / 2 ^ k) x S))ᵀ * Matrix.diagonal (z A ((1 : ℝ) / 2 ^ k) x S)) *ᵥ y) :
    let β := (1 : ℝ) / 2 ^ k
    let h := coefficientDirection β x y
    iteratedDeriv 2 (fun t : ℝ => potential
      (H + t • (∑ i, h i • signedLift (A i))) A β (OwnerCurves.weights β x h t) θ) 0 / 2 ≤
      legalUpper ((1 / β) • P A β x S) (SupportedSpin.involution A)
        (E A β x S) (R A β x S)
        (fun i => r A β x S i ^ 2 + (2 / ownerScale β) * z A β x S i ^ 2)
        (z A β x S) (ownerScale β) w y := by
  dsimp only
  let β := (1 : ℝ) / 2 ^ k
  let h := coefficientDirection β x y
  let c := OwnerCurves.weights β x h
  let K := ∑ i, h i • signedLift (A i)
  have hc : ∀ i, 0 < c 0 i := fun i => by
    simpa only [c, OwnerCurves.weights_zero] using owner_pos (by positivity : 0 < β) (hx i)
  have hcs : ContDiffAt ℝ ∞ c 0 := OwnerCurves.weights_smooth β x h hx
  have hmax' : ∀ T ∈ densitySet, objective ((fun t : ℝ => H + t • K) 0) A β (c 0) θ T ≤
      objective ((fun t : ℝ => H + t • K) 0) A β (c 0) θ S := by
    simpa only [zero_smul, add_zero, c, OwnerCurves.weights_zero, SupportedFrames.weights] using hmax
  have hs := potential_second_eq_density_response A hA k hk θ hθ (fun t : ℝ => H + t • K) c
    (by fun_prop) hcs hc S ⟨hS.posSemidef, ht⟩ hmax'
  change iteratedDeriv 2 (fun t : ℝ => potential (H + t • K) A β (c t) θ) 0 / 2 ≤ _
  rw [hs]
  apply sSup_div_two_le
  intro X
  rw [ObjectiveResponse.chart_hessian_eq_affine_second A hA k hk c hcs hc H K θ S X hS]
  exact normalized_objective_second_le A hA hne k hk x hx H θ hθ S X hS hfixed w y hlegal

end HigherRankKS.NormalizedHessian
