import MatrixSpencer.DyadicEpochLocalMoments
import MatrixSpencer.FiniteSelection

/-!
# Selecting a dyadic epoch endpoint from explicit finite moments

The finite moment hypotheses concern the actual certificate, paid covariance
trace, and stored tangent of states satisfying the proved epoch invariants.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix
noncomputable section
namespace MatrixSpencer

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n] [Nonempty n]
local instance dyadicEpochSelectionCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance dyadicEpochSelectionSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance

/-- The actual anchored owner certificate of a concrete epoch state. -/
def dyadicEpochCertificate (cfg : DyadicEpochConfig ι n) (s : DyadicEpochState ι) : ℝ :=
  dyadicOwnerCertificate cfg.anchor cfg.matrices cfg.depth cfg.weight (cfg.center s.point) s.covariance

/-- The compensated scalar energy used by the actual finite tree. -/
def dyadicEpochEnergySuper (cfg : DyadicEpochConfig ι n) (s : DyadicEpochState ι) : ℝ :=
  dyadicEpochCertificate cfg s + (epochTracePriceScale / Real.sqrt (Fintype.card ι : ℝ)) * s.paid -
    cfg.energyRate * s.time - 2 * s.rounding

/-- The second-moment compensator of the stored scalar tangent. -/
def dyadicEpochTangentAdjusted (s : DyadicEpochState ι) : ℝ :=
  s.tangent ^ 2 - (Fintype.card ι : ℝ) * s.time

/-- Success is time completion or the actual frozen-coordinate threshold. -/
def DyadicEpochState.Successful (cfg : DyadicEpochConfig ι n) (s : DyadicEpochState ι) : Prop :=
  s.time = cfg.duration ∨ (Fintype.card ι : ℝ) / 64 ≤ (frozenCoordinates s.point).card

omit [DecidableEq ι] [Nonempty n] in
theorem dyadic_epoch_count_sqrt_ge_one (cfg : DyadicEpochConfig ι n) :
    (1 : ℝ) ≤ Real.sqrt (Fintype.card ι : ℝ) := by
  have hk : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast (show 1 ≤ Fintype.card ι by have := cfg.count_large; omega)
  simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hk

theorem dyadicEpochCertificate_nonneg (cfg : DyadicEpochConfig ι n) {s : DyadicEpochState ι}
    (hs : s.Invariant cfg) : 0 ≤ dyadicEpochCertificate cfg s :=
  dyadicOwnerCertificate_nonneg cfg.anchor (cfg.center s.point) cfg.matrices cfg.hermitian hs.covariance_pos cfg.depth cfg.weight

theorem DyadicEpochState.Invariant.dust_le_count {cfg : DyadicEpochConfig ι n} {s : DyadicEpochState ι}
    (hs : s.Invariant cfg) : s.dust ≤ (Fintype.card ι : ℝ) / 8192 := by
  have h := hs.dust_budget
  have hr : (0 : ℝ) ≤ s.covariance.rank := Nat.cast_nonneg _
  norm_num [epochDustThreshold] at h
  linarith

theorem DyadicEpochState.Invariant.rounding_le_small {cfg : DyadicEpochConfig ι n} {s : DyadicEpochState ι}
    (hs : s.Invariant cfg) : s.rounding ≤ (1 / 1000 : ℝ) := by
  have hc : ((frozenCoordinates s.point).card : ℝ) ≤ Fintype.card ι := by
    exact_mod_cast (Finset.card_le_univ (frozenCoordinates s.point))
  have h := mul_le_mul_of_nonneg_left hc cfg.epsilon_pos.le
  have hb := cfg.epsilon_small
  nlinarith [hs.rounding_budget]

/-- A selected small paid cost excludes the cleaning-failure terminal case. -/
theorem DyadicEpochState.Invariant.successful_of_paid_lt {cfg : DyadicEpochConfig ι n} {s : DyadicEpochState ι}
    (hs : s.Invariant cfg) (hterminal : s.Terminal cfg)
    (hp : s.paid < (Fintype.card ι : ℝ) / 128) : s.Successful cfg := by
  have hd := hs.dust_le_count
  have hk : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  rcases hterminal with hf | hf | ht
  · exfalso
    linarith
  · exact Or.inr hf
  · exact Or.inl (le_antisymm hs.time_le ht)

/-- The selected certificate and tangent control the actual retained-owner potential. -/
theorem DyadicEpochState.Invariant.selected_retained_growth_le {cfg : DyadicEpochConfig ι n} {s : DyadicEpochState ι}
    (hs : s.Invariant cfg)
    (he : dyadicEpochCertificate cfg s ≤ 12 * Real.sqrt (Fintype.card ι : ℝ))
    (hm : |s.tangent| ≤ 6 * Real.sqrt (Fintype.card ι : ℝ)) :
    cfg.potential (cfg.center s.point) s.covariance -
      cfg.potential cfg.anchor 1 ≤ 19 * Real.sqrt (Fintype.card ι : ℝ) := by
  have hp := dyadicOwnerCertificate_terminal_tangent_error_le cfg.anchor (cfg.center s.point)
    cfg.matrices cfg.hermitian cfg.depth cfg.weight (Cstart := 1) (Cend := s.covariance)
    Matrix.PosSemidef.one s.tangent s.rounding hs.tangent_error
  change _ ≤ dyadicEpochCertificate cfg s + |s.tangent| + s.rounding at hp
  have hr := hs.rounding_le_small
  have hk := dyadic_epoch_count_sqrt_ge_one cfg
  unfold DyadicEpochConfig.potential
  linarith

/-- The same selected endpoint can reset its owner covariance to identity within
22 sqrt(k), including all accumulated rounding costs. -/
theorem DyadicEpochState.Invariant.selected_reset_growth_le {cfg : DyadicEpochConfig ι n} {s : DyadicEpochState ι}
    (hs : s.Invariant cfg)
    (he : dyadicEpochCertificate cfg s ≤ 12 * Real.sqrt (Fintype.card ι : ℝ))
    (hm : |s.tangent| ≤ 6 * Real.sqrt (Fintype.card ι : ℝ)) :
    cfg.potential (cfg.center s.point) 1 -
      cfg.potential cfg.anchor 1 ≤ 22 * Real.sqrt (Fintype.card ι : ℝ) := by
  have hret := hs.selected_retained_growth_le he hm
  have hu := regularizedOwnerPotential_le_base_add (cfg.center s.point : Matrix n n ℂ)
    cfg.matrices cfg.hermitian cfg.contractions (C := 1) Matrix.PosSemidef.one le_rfl
    (dyadicTsallisRegularizer cfg.depth cfg.weight)
    (continuousOn_density_dyadicTsallisRegularizer cfg.depth cfg.weight)
  have hl := regularizedBasePotential_le_owner (cfg.center s.point : Matrix n n ℂ)
    cfg.matrices cfg.hermitian hs.covariance_pos
    (dyadicTsallisRegularizer cfg.depth cfg.weight)
    (continuousOn_density_dyadicTsallisRegularizer cfg.depth cfg.weight)
  change _ ≤ _ at hret
  unfold DyadicEpochConfig.potential at hret ⊢
  linarith [Real.sqrt_nonneg (Fintype.card ι : ℝ)]

/-- All requirements on a selected actual endpoint, with the invariant retained. -/
structure DyadicEpochGoodEndpoint (cfg : DyadicEpochConfig ι n) (s : DyadicEpochState ι) : Prop where
  invariant : s.Invariant cfg
  successful : s.Successful cfg
  paid_small : s.paid < (Fintype.card ι : ℝ) / 128
  certificate_small : dyadicEpochCertificate cfg s < 12 * Real.sqrt (Fintype.card ι : ℝ)
  tangent_small : |s.tangent| < 6 * Real.sqrt (Fintype.card ι : ℝ)
  retained_growth : cfg.potential (cfg.center s.point) s.covariance -
    cfg.potential cfg.anchor 1 ≤ 19 * Real.sqrt (Fintype.card ι : ℝ)
  reset_growth : cfg.potential (cfg.center s.point) 1 -
    cfg.potential cfg.anchor 1 ≤ 22 * Real.sqrt (Fintype.card ι : ℝ)

omit [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n] [Nonempty n] in
/-- The three concrete bad-event probabilities have a strict total mass gap. -/
theorem dyadic_epoch_selection_mass_gap {k : ℝ} (hk : 0 < k) :
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
theorem exists_good_dyadic_epoch_endpoint_of_moments (cfg : DyadicEpochConfig ι n)
    (s : σ → DyadicEpochState ι) (w : σ → ℝ) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (hinv : ∀ i, (s i).Invariant cfg) (hterm : ∀ i, (s i).Terminal cfg)
    (henergy : (∑ i, w i * dyadicEpochCertificate cfg (s i)) ≤ (301 / 100 : ℝ) * Real.sqrt (Fintype.card ι : ℝ))
    (hpaid : (∑ i, w i * (s i).paid) ≤ (301 / 100 : ℝ) * (Fintype.card ι : ℝ) / epochTracePriceScale)
    (htangent : (∑ i, w i * (s i).tangent ^ 2) ≤ (Fintype.card ι : ℝ)) :
    ∃ i, 0 < w i ∧ DyadicEpochGoodEndpoint cfg (s i) := by
  classical
  have hk : (0 : ℝ) < Fintype.card ι := by exact_mod_cast (show 0 < Fintype.card ι by have := cfg.count_large; omega)
  have hroot := Real.sqrt_pos.mpr hk
  obtain ⟨i, _, hwi, he, hp, hm⟩ := FiniteSelection.good_endpoint_of_moments Finset.univ
    w (fun i => dyadicEpochCertificate cfg (s i)) (fun i => (s i).paid) (fun i => (s i).tangent)
    hw hw1 (fun i _ => dyadicEpochCertificate_nonneg cfg (hinv i)) (fun i _ => (hinv i).paid_nonneg)
    (by positivity : 0 < 12 * Real.sqrt (Fintype.card ι : ℝ)) (by positivity : 0 < (Fintype.card ι : ℝ) / 128)
    (by positivity : 0 < 6 * Real.sqrt (Fintype.card ι : ℝ)) henergy hpaid htangent
    (dyadic_epoch_selection_mass_gap hk)
  exact ⟨i, hwi, hinv i, (hinv i).successful_of_paid_lt (hterm i) hp, hp, he, hm,
    (hinv i).selected_retained_growth_le he.le hm.le, (hinv i).selected_reset_growth_le he.le hm.le⟩

/-- The actual time and rounding compensators consume at most 1.01 sqrt(k). -/
theorem DyadicEpochState.Invariant.energy_compensation_le {cfg : DyadicEpochConfig ι n} {s : DyadicEpochState ι}
    (hs : s.Invariant cfg) :
    dyadicEpochCertificate cfg s + (epochTracePriceScale / Real.sqrt (Fintype.card ι : ℝ)) * s.paid ≤
      dyadicEpochEnergySuper cfg s + (101 / 100 : ℝ) * Real.sqrt (Fintype.card ι : ℝ) := by
  exact RectangularEpochParameters.value_le_account_add cfg.response_large
    (dyadic_epoch_count_sqrt_ge_one cfg) hs.time_le hs.rounding_le_small

/-- The finite compensated energy inequality gives the combined actual
certificate-plus-paid budget. -/
theorem dyadic_epoch_combined_moment_of_super (cfg : DyadicEpochConfig ι n) (s : σ → DyadicEpochState ι)
    (w : σ → ℝ) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (hinv : ∀ i, (s i).Invariant cfg)
    (henergy : (∑ i, w i * dyadicEpochEnergySuper cfg (s i)) ≤ 2 * Real.sqrt (Fintype.card ι : ℝ)) :
    (∑ i, w i * (dyadicEpochCertificate cfg (s i) +
      (epochTracePriceScale / Real.sqrt (Fintype.card ι : ℝ)) * (s i).paid)) ≤
        (301 / 100 : ℝ) * Real.sqrt (Fintype.card ι : ℝ) := by
  calc
    _ ≤ ∑ i, w i * (dyadicEpochEnergySuper cfg (s i) + (101 / 100 : ℝ) * Real.sqrt (Fintype.card ι : ℝ)) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hinv i).energy_compensation_le (hw i))
    _ = (∑ i, w i * dyadicEpochEnergySuper cfg (s i)) + (101 / 100 : ℝ) * Real.sqrt (Fintype.card ι : ℝ) := by
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hw1, one_mul]
    _ ≤ _ := by linarith

/-- Nonnegativity splits the actual combined budget into certificate and paid-trace moments. -/
theorem dyadic_epoch_separate_moments_of_combined (cfg : DyadicEpochConfig ι n) (s : σ → DyadicEpochState ι)
    (w : σ → ℝ) (hw : ∀ i, 0 ≤ w i) (hinv : ∀ i, (s i).Invariant cfg)
    (hcombined : (∑ i, w i * (dyadicEpochCertificate cfg (s i) +
      (epochTracePriceScale / Real.sqrt (Fintype.card ι : ℝ)) * (s i).paid)) ≤
        (301 / 100 : ℝ) * Real.sqrt (Fintype.card ι : ℝ)) :
    (∑ i, w i * dyadicEpochCertificate cfg (s i)) ≤ (301 / 100 : ℝ) * Real.sqrt (Fintype.card ι : ℝ) ∧
      (∑ i, w i * (s i).paid) ≤ (301 / 100 : ℝ) * (Fintype.card ι : ℝ) / epochTracePriceScale := by
  have hk := dyadic_epoch_count_sqrt_ge_one cfg
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
          (le_add_of_nonneg_left (dyadicEpochCertificate_nonneg cfg (hinv i))) (hw i))).trans hcombined
    have hm := mul_le_mul_of_nonneg_right hp hs.le
    have he : (epochTracePriceScale / Real.sqrt (Fintype.card ι : ℝ)) *
        (∑ i, w i * (s i).paid) * Real.sqrt (Fintype.card ι : ℝ) =
        (∑ i, w i * (s i).paid) * epochTracePriceScale := by field_simp
    rw [he] at hm
    have hsq := Real.sq_sqrt (Nat.cast_nonneg (Fintype.card ι) : (0 : ℝ) ≤ Fintype.card ι)
    apply (le_div_iff₀ (by norm_num [epochTracePriceScale] : 0 < epochTracePriceScale)).mpr
    nlinarith

/-- The actual adjusted tangent moment and time cap give the scalar second-moment budget. -/
theorem dyadic_epoch_tangent_moment_of_adjusted (cfg : DyadicEpochConfig ι n) (s : σ → DyadicEpochState ι)
    (w : σ → ℝ) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (hinv : ∀ i, (s i).Invariant cfg)
    (htangent : (∑ i, w i * dyadicEpochTangentAdjusted (s i)) ≤ 0) :
    (∑ i, w i * (s i).tangent ^ 2) ≤ (Fintype.card ι : ℝ) := by
  exact RectangularEpochParameters.tangent_moment_of_account cfg.response_large
    (Nat.cast_nonneg _) w (fun i => (s i).tangent) (fun i => (s i).time)
    hw hw1 (fun i => (hinv i).time_le) htangent

/-- The two compensated finite-tree inequalities suffice for actual good endpoint selection. -/
theorem exists_good_dyadic_epoch_endpoint_of_supermartingale (cfg : DyadicEpochConfig ι n)
    (s : σ → DyadicEpochState ι) (w : σ → ℝ) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (hinv : ∀ i, (s i).Invariant cfg) (hterm : ∀ i, (s i).Terminal cfg)
    (henergy : (∑ i, w i * dyadicEpochEnergySuper cfg (s i)) ≤ 2 * Real.sqrt (Fintype.card ι : ℝ))
    (htangent : (∑ i, w i * dyadicEpochTangentAdjusted (s i)) ≤ 0) :
    ∃ i, 0 < w i ∧ DyadicEpochGoodEndpoint cfg (s i) := by
  have hc := dyadic_epoch_combined_moment_of_super cfg s w hw hw1 hinv henergy
  obtain ⟨he, hp⟩ := dyadic_epoch_separate_moments_of_combined cfg s w hw hinv hc
  exact exists_good_dyadic_epoch_endpoint_of_moments cfg s w hw hw1 hinv hterm he hp
    (dyadic_epoch_tangent_moment_of_adjusted cfg s w hw hw1 hinv htangent)

end MatrixSpencer
