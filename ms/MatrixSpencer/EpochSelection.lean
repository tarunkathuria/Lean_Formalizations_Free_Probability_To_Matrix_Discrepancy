import MatrixSpencer.EpochState
import MatrixSpencer.FiniteSelection

/-!
# Selecting an actual successful finite epoch endpoint

The finite moment hypotheses concern the actual certificate, paid covariance
trace, and stored tangent of states satisfying the proved epoch invariants.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix
noncomputable section
namespace MatrixSpencer

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n] [Nonempty n]
local instance epochSelectionCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance epochSelectionSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance

/-- The actual anchored owner certificate of a concrete epoch state. -/
def epochCertificate (cfg : EpochConfig ι n) (s : EpochState ι) : ℝ :=
  ownerCertificate cfg.anchor cfg.matrices 1 (cfg.center s.point) s.covariance

/-- The compensated scalar energy used by the actual finite tree. -/
def epochEnergySuper (cfg : EpochConfig ι n) (s : EpochState ι) : ℝ :=
  epochCertificate cfg s + (epochTracePriceScale / Real.sqrt (Fintype.card ι : ℝ)) * s.paid -
    (epochResponseConstant * Real.sqrt (Fintype.card ι : ℝ) +
      Real.sqrt (Fintype.card ι : ℝ) / (200 * epochTimeLimit)) * s.time - 2 * s.rounding

/-- The second-moment compensator of the stored scalar tangent. -/
def epochTangentAdjusted (s : EpochState ι) : ℝ :=
  s.tangent ^ 2 - (Fintype.card ι : ℝ) * s.time

/-- Success is time completion or the actual frozen-coordinate threshold. -/
def EpochState.Successful (s : EpochState ι) : Prop :=
  s.time = epochTimeLimit ∨ (Fintype.card ι : ℝ) / 64 ≤ (frozenCoordinates s.point).card

omit [DecidableEq ι] [Nonempty n] in
theorem epoch_count_sqrt_ge_one (cfg : EpochConfig ι n) :
    (1 : ℝ) ≤ Real.sqrt (Fintype.card ι : ℝ) := by
  have hk : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast (show 1 ≤ Fintype.card ι by have := cfg.count_large; omega)
  simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hk

theorem epochCertificate_nonneg (cfg : EpochConfig ι n) {s : EpochState ι}
    (hs : s.Invariant cfg) : 0 ≤ epochCertificate cfg s :=
  ownerCertificate_nonneg cfg.anchor (cfg.center s.point) cfg.matrices cfg.hermitian hs.covariance_pos 1

theorem EpochState.Invariant.dust_le_count {cfg : EpochConfig ι n} {s : EpochState ι}
    (hs : s.Invariant cfg) : s.dust ≤ (Fintype.card ι : ℝ) / 8192 := by
  have h := hs.dust_budget
  have hr : (0 : ℝ) ≤ s.covariance.rank := Nat.cast_nonneg _
  norm_num [epochDustThreshold] at h
  linarith

theorem EpochState.Invariant.rounding_le_small {cfg : EpochConfig ι n} {s : EpochState ι}
    (hs : s.Invariant cfg) : s.rounding ≤ (1 / 1000 : ℝ) := by
  have hc : ((frozenCoordinates s.point).card : ℝ) ≤ Fintype.card ι := by
    exact_mod_cast (Finset.card_le_univ (frozenCoordinates s.point))
  have h := mul_le_mul_of_nonneg_left hc cfg.epsilon_pos.le
  have hb := cfg.epsilon_small
  nlinarith [hs.rounding_budget]

/-- A selected small paid cost excludes the cleaning-failure terminal case. -/
theorem EpochState.Invariant.successful_of_paid_lt {cfg : EpochConfig ι n} {s : EpochState ι}
    (hs : s.Invariant cfg) (hterminal : s.Terminal)
    (hp : s.paid < (Fintype.card ι : ℝ) / 128) : s.Successful := by
  have hd := hs.dust_le_count
  have hk : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  rcases hterminal with hf | hf | ht
  · exfalso
    linarith
  · exact Or.inr hf
  · exact Or.inl (le_antisymm hs.time_le ht)

/-- The selected certificate and tangent control the actual retained-owner potential. -/
theorem EpochState.Invariant.selected_retained_growth_le {cfg : EpochConfig ι n} {s : EpochState ι}
    (hs : s.Invariant cfg)
    (he : epochCertificate cfg s ≤ 12 * Real.sqrt (Fintype.card ι : ℝ))
    (hm : |s.tangent| ≤ 6 * Real.sqrt (Fintype.card ι : ℝ)) :
    ownerPotential (cfg.center s.point) cfg.matrices s.covariance 1 -
      ownerPotential cfg.anchor cfg.matrices 1 1 ≤ 19 * Real.sqrt (Fintype.card ι : ℝ) := by
  have hp := ownerCertificate_terminal_tangent_error_le cfg.anchor (cfg.center s.point)
    cfg.matrices cfg.hermitian 1 (Cstart := 1) (Cend := s.covariance)
    Matrix.PosSemidef.one s.tangent s.rounding hs.tangent_error
  change _ ≤ epochCertificate cfg s + |s.tangent| + s.rounding at hp
  have hr := hs.rounding_le_small
  have hk := epoch_count_sqrt_ge_one cfg
  linarith

/-- The same selected endpoint can reset its owner covariance to identity within
22 sqrt(k), including all accumulated rounding costs. -/
theorem EpochState.Invariant.selected_reset_growth_le {cfg : EpochConfig ι n} {s : EpochState ι}
    (hs : s.Invariant cfg)
    (he : epochCertificate cfg s ≤ 12 * Real.sqrt (Fintype.card ι : ℝ))
    (hm : |s.tangent| ≤ 6 * Real.sqrt (Fintype.card ι : ℝ)) :
    ownerPotential (cfg.center s.point) cfg.matrices 1 1 -
      ownerPotential cfg.anchor cfg.matrices 1 1 ≤ 22 * Real.sqrt (Fintype.card ι : ℝ) := by
  have hret := hs.selected_retained_growth_le he hm
  have hu := ownerPotential_le_base_add (cfg.center s.point : Matrix n n ℂ)
    cfg.matrices cfg.hermitian cfg.contractions (C := 1) Matrix.PosSemidef.one le_rfl 1
  have hl := baseDensityPotential_le_owner (cfg.center s.point : Matrix n n ℂ)
    cfg.matrices cfg.hermitian hs.covariance_pos 1
  linarith [Real.sqrt_nonneg (Fintype.card ι : ℝ)]

/-- All requirements on a selected actual endpoint, with the invariant retained. -/
structure EpochGoodEndpoint (cfg : EpochConfig ι n) (s : EpochState ι) : Prop where
  invariant : s.Invariant cfg
  successful : s.Successful
  paid_small : s.paid < (Fintype.card ι : ℝ) / 128
  certificate_small : epochCertificate cfg s < 12 * Real.sqrt (Fintype.card ι : ℝ)
  tangent_small : |s.tangent| < 6 * Real.sqrt (Fintype.card ι : ℝ)
  retained_growth : ownerPotential (cfg.center s.point) cfg.matrices s.covariance 1 -
    ownerPotential cfg.anchor cfg.matrices 1 1 ≤ 19 * Real.sqrt (Fintype.card ι : ℝ)
  reset_growth : ownerPotential (cfg.center s.point) cfg.matrices 1 1 -
    ownerPotential cfg.anchor cfg.matrices 1 1 ≤ 22 * Real.sqrt (Fintype.card ι : ℝ)

omit [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n] [Nonempty n] in
/-- The three concrete bad-event probabilities have a strict total mass gap. -/
theorem epoch_selection_mass_gap {k : ℝ} (hk : 0 < k) :
    ((301 / 100 : ℝ) * Real.sqrt k) / (12 * Real.sqrt k) +
      ((301 / 100 : ℝ) * k / epochTracePriceScale) / (k / 128) +
      k / (6 * Real.sqrt k) ^ 2 < 1 := by
  have hs := Real.sqrt_pos.mpr hk
  rw [mul_pow, Real.sq_sqrt hk.le]
  have h1 : ((301 / 100 : ℝ) * Real.sqrt k) / (12 * Real.sqrt k) = 301 / 1200 := by
    field_simp
    ring
  have h2 : ((301 / 100 : ℝ) * k / epochTracePriceScale) / (k / 128) = 301 / 3200 := by
    norm_num [epochTracePriceScale]
    field_simp
    ring
  have h3 : k / (6 ^ 2 * k) = (1 / 36 : ℝ) := by
    field_simp
    norm_num
  rw [h1, h2, h3]
  norm_num

variable {σ : Type*} [Fintype σ]

/-- Moment budgets select a positive-weight actual successful terminal endpoint.
The construction of the finite ensemble and its moments is a separate obligation. -/
theorem exists_good_epoch_endpoint_of_moments (cfg : EpochConfig ι n)
    (s : σ → EpochState ι) (w : σ → ℝ) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (hinv : ∀ i, (s i).Invariant cfg) (hterm : ∀ i, (s i).Terminal)
    (henergy : (∑ i, w i * epochCertificate cfg (s i)) ≤ (301 / 100 : ℝ) * Real.sqrt (Fintype.card ι : ℝ))
    (hpaid : (∑ i, w i * (s i).paid) ≤ (301 / 100 : ℝ) * (Fintype.card ι : ℝ) / epochTracePriceScale)
    (htangent : (∑ i, w i * (s i).tangent ^ 2) ≤ (Fintype.card ι : ℝ)) :
    ∃ i, 0 < w i ∧ EpochGoodEndpoint cfg (s i) := by
  classical
  have hk : (0 : ℝ) < Fintype.card ι := by exact_mod_cast (show 0 < Fintype.card ι by have := cfg.count_large; omega)
  have hroot := Real.sqrt_pos.mpr hk
  obtain ⟨i, _, hwi, he, hp, hm⟩ := FiniteSelection.good_endpoint_of_moments Finset.univ
    w (fun i => epochCertificate cfg (s i)) (fun i => (s i).paid) (fun i => (s i).tangent)
    hw hw1 (fun i _ => epochCertificate_nonneg cfg (hinv i)) (fun i _ => (hinv i).paid_nonneg)
    (by positivity : 0 < 12 * Real.sqrt (Fintype.card ι : ℝ)) (by positivity : 0 < (Fintype.card ι : ℝ) / 128)
    (by positivity : 0 < 6 * Real.sqrt (Fintype.card ι : ℝ)) henergy hpaid htangent
    (epoch_selection_mass_gap hk)
  exact ⟨i, hwi, hinv i, (hinv i).successful_of_paid_lt (hterm i) hp, hp, he, hm,
    (hinv i).selected_retained_growth_le he.le hm.le, (hinv i).selected_reset_growth_le he.le hm.le⟩

/-- The actual time and rounding compensators consume at most 1.01 sqrt(k). -/
theorem EpochState.Invariant.energy_compensation_le {cfg : EpochConfig ι n} {s : EpochState ι}
    (hs : s.Invariant cfg) :
    epochCertificate cfg s + (epochTracePriceScale / Real.sqrt (Fintype.card ι : ℝ)) * s.paid ≤
      epochEnergySuper cfg s + (101 / 100 : ℝ) * Real.sqrt (Fintype.card ι : ℝ) := by
  have hr := hs.rounding_le_small
  have hk := epoch_count_sqrt_ge_one cfg
  let rate := epochResponseConstant * Real.sqrt (Fintype.card ι : ℝ) +
    Real.sqrt (Fintype.card ι : ℝ) / (200 * epochTimeLimit)
  have hrate : 0 ≤ rate := by dsimp [rate, epochResponseConstant, epochTimeLimit]; positivity
  have ht := mul_le_mul_of_nonneg_left hs.time_le hrate
  have hb : rate * epochTimeLimit + 2 / 1000 ≤
      (101 / 100 : ℝ) * Real.sqrt (Fintype.card ι : ℝ) := by
    dsimp only [rate]
    norm_num [epochResponseConstant, epochTimeLimit]
    linarith
  change _ ≤ epochCertificate cfg s +
    (epochTracePriceScale / Real.sqrt (Fintype.card ι : ℝ)) * s.paid - rate * s.time -
    2 * s.rounding + (101 / 100 : ℝ) * Real.sqrt (Fintype.card ι : ℝ)
  linarith

/-- The finite compensated energy inequality gives the combined actual
certificate-plus-paid budget. -/
theorem epoch_combined_moment_of_super (cfg : EpochConfig ι n) (s : σ → EpochState ι)
    (w : σ → ℝ) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (hinv : ∀ i, (s i).Invariant cfg)
    (henergy : (∑ i, w i * epochEnergySuper cfg (s i)) ≤ 2 * Real.sqrt (Fintype.card ι : ℝ)) :
    (∑ i, w i * (epochCertificate cfg (s i) +
      (epochTracePriceScale / Real.sqrt (Fintype.card ι : ℝ)) * (s i).paid)) ≤
        (301 / 100 : ℝ) * Real.sqrt (Fintype.card ι : ℝ) := by
  calc
    _ ≤ ∑ i, w i * (epochEnergySuper cfg (s i) + (101 / 100 : ℝ) * Real.sqrt (Fintype.card ι : ℝ)) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hinv i).energy_compensation_le (hw i))
    _ = (∑ i, w i * epochEnergySuper cfg (s i)) + (101 / 100 : ℝ) * Real.sqrt (Fintype.card ι : ℝ) := by
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hw1, one_mul]
    _ ≤ _ := by linarith

/-- Nonnegativity splits the actual combined budget into certificate and paid-trace moments. -/
theorem epoch_separate_moments_of_combined (cfg : EpochConfig ι n) (s : σ → EpochState ι)
    (w : σ → ℝ) (hw : ∀ i, 0 ≤ w i) (hinv : ∀ i, (s i).Invariant cfg)
    (hcombined : (∑ i, w i * (epochCertificate cfg (s i) +
      (epochTracePriceScale / Real.sqrt (Fintype.card ι : ℝ)) * (s i).paid)) ≤
        (301 / 100 : ℝ) * Real.sqrt (Fintype.card ι : ℝ)) :
    (∑ i, w i * epochCertificate cfg (s i)) ≤ (301 / 100 : ℝ) * Real.sqrt (Fintype.card ι : ℝ) ∧
      (∑ i, w i * (s i).paid) ≤ (301 / 100 : ℝ) * (Fintype.card ι : ℝ) / epochTracePriceScale := by
  have hk := epoch_count_sqrt_ge_one cfg
  have hs : 0 < Real.sqrt (Fintype.card ι : ℝ) := by linarith
  have hprice : 0 ≤ epochTracePriceScale / Real.sqrt (Fintype.card ι : ℝ) := by
    exact div_nonneg (by norm_num [epochTracePriceScale]) hs.le
  constructor
  · apply le_trans _ hcombined
    apply Finset.sum_le_sum
    intro i _
    apply mul_le_mul_of_nonneg_left _ (hw i)
    exact le_add_of_nonneg_right (mul_nonneg hprice (hinv i).paid_nonneg)
  · have hp : (epochTracePriceScale / Real.sqrt (Fintype.card ι : ℝ)) *
        (∑ i, w i * (s i).paid) ≤ (301 / 100 : ℝ) * Real.sqrt (Fintype.card ι : ℝ) := by
      calc
        _ = ∑ i, w i * ((epochTracePriceScale / Real.sqrt (Fintype.card ι : ℝ)) * (s i).paid) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ ≤ _ := (Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_left (epochCertificate_nonneg cfg (hinv i))) (hw i))).trans hcombined
    have hm := mul_le_mul_of_nonneg_right hp hs.le
    have he : (epochTracePriceScale / Real.sqrt (Fintype.card ι : ℝ)) *
        (∑ i, w i * (s i).paid) * Real.sqrt (Fintype.card ι : ℝ) =
        (∑ i, w i * (s i).paid) * epochTracePriceScale := by field_simp
    rw [he] at hm
    have hsq := Real.sq_sqrt (Nat.cast_nonneg (Fintype.card ι) : (0 : ℝ) ≤ Fintype.card ι)
    apply (le_div_iff₀ (by norm_num [epochTracePriceScale] : 0 < epochTracePriceScale)).mpr
    nlinarith

/-- The actual adjusted tangent moment and time cap give the scalar second-moment budget. -/
theorem epoch_tangent_moment_of_adjusted (cfg : EpochConfig ι n) (s : σ → EpochState ι)
    (w : σ → ℝ) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (hinv : ∀ i, (s i).Invariant cfg)
    (htangent : (∑ i, w i * epochTangentAdjusted (s i)) ≤ 0) :
    (∑ i, w i * (s i).tangent ^ 2) ≤ (Fintype.card ι : ℝ) := by
  have hk : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  calc
    _ ≤ ∑ i, w i * (epochTangentAdjusted (s i) + (Fintype.card ι : ℝ) * epochTimeLimit) := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (hw i)
      have h := mul_le_mul_of_nonneg_left (hinv i).time_le hk
      unfold epochTangentAdjusted
      linarith
    _ = (∑ i, w i * epochTangentAdjusted (s i)) + (Fintype.card ι : ℝ) * epochTimeLimit := by
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hw1, one_mul]
    _ ≤ _ := by norm_num [epochTimeLimit]; linarith

/-- The two compensated finite-tree inequalities suffice for actual good endpoint selection. -/
theorem exists_good_epoch_endpoint_of_supermartingale (cfg : EpochConfig ι n)
    (s : σ → EpochState ι) (w : σ → ℝ) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (hinv : ∀ i, (s i).Invariant cfg) (hterm : ∀ i, (s i).Terminal)
    (henergy : (∑ i, w i * epochEnergySuper cfg (s i)) ≤ 2 * Real.sqrt (Fintype.card ι : ℝ))
    (htangent : (∑ i, w i * epochTangentAdjusted (s i)) ≤ 0) :
    ∃ i, 0 < w i ∧ EpochGoodEndpoint cfg (s i) := by
  have hc := epoch_combined_moment_of_super cfg s w hw hw1 hinv henergy
  obtain ⟨he, hp⟩ := epoch_separate_moments_of_combined cfg s w hw hinv hc
  exact exists_good_epoch_endpoint_of_moments cfg s w hw hw1 hinv hterm he hp
    (epoch_tangent_moment_of_adjusted cfg s w hw hw1 hinv htangent)

end MatrixSpencer
