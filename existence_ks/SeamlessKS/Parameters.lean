import SeamlessKS.Input
import SeamlessKS.TrialProbability
import Mathlib.Algebra.Order.Floor.Semiring



open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace SeamlessKS.Parameters
open MatrixSpencer
open SeamlessKS.Input

variable {N d : ℕ}

def rho (N : ℕ) : ℝ := 1/(100*(N : ℝ)^2)
def outwardStep (N : ℕ) : ℝ := rho N / 16
def zeta (N : ℕ) : ℝ := outwardStep N / 10
def beta (v : Fin N → Fin d → ℂ) : ℝ := delta v / (100*(N : ℝ))
def densityFloor (v : Fin N → Fin d → ℂ) : ℝ := (theta v / 40)^2
def complexRadius (v : Fin N → Fin d → ℂ) : ℝ :=
  min (min (min 1 (densityFloor v)) (rho N)) (zeta N) / 10000
def objectiveBound (d : ℕ) : ℝ := 10000*(2*(d : ℝ)+1)^2
def jointDerivativeBound (v : Fin N → Fin d → ℂ) : ℝ :=
  objectiveBound d * (10 / complexRadius v)^4
def coercivity (v : Fin N → Fin d → ℂ) : ℝ := theta v / 2
def derivativeBudget (v : Fin N → Fin d → ℂ) : ℝ :=
  1 + (jointDerivativeBound v + 3*(jointDerivativeBound v)^2/coercivity v) *
    (1+jointDerivativeBound v/coercivity v)^4

def queryStep (v : Fin N → Fin d → ℂ) : ℝ :=
  min (rho N/16) (Real.sqrt (beta v/(128*(N : ℝ)*derivativeBudget v)))
def movementStep (v : Fin N → Fin d → ℂ) : ℝ :=
  min (rho N/16) (Real.sqrt (beta v/(4*derivativeBudget v)))
def hessianAccuracy (v : Fin N → Fin d → ℂ) : ℝ :=
  beta v * queryStep v^2/(128*(N : ℝ))
def localAccuracy (v : Fin N → Fin d → ℂ) : ℝ := beta v * movementStep v^2/8
def horizon (v : Fin N → Fin d → ℂ) : ℕ :=
  ⌈16*(N : ℝ)/movementStep v^2⌉₊

theorem rho_pos {N : ℕ} (hN : 0 < N) : 0 < rho N := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  unfold rho
  positivity

theorem outwardStep_pos {N : ℕ} (hN : 0 < N) : 0 < outwardStep N :=
  div_pos (rho_pos hN) (by norm_num)

theorem zeta_pos {N : ℕ} (hN : 0 < N) : 0 < zeta N :=
  div_pos (outwardStep_pos hN) (by norm_num)

theorem zeta_eq (N : ℕ) : zeta N = outwardStep N / 10 := rfl

theorem rho_le_one_div_labels {N : ℕ} (hN : 0 < N) : rho N ≤ 1/(N : ℝ) := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  unfold rho
  apply (div_le_div_iff₀ (by positivity : (0:ℝ) < 100*(N:ℝ)^2) hn).mpr
  nlinarith

theorem rho_le_delta (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑ i, KSRankOne.atom (v i)) = 1) : rho N ≤ delta v := by
  have h1 := rho_le_one_div_labels (labels_pos v hd hp)
  have h2 := one_div_labels_le_epsilon v hd hp
  have he : epsilon v ≤ delta v := by
    have hs := delta_sq v
    have hn := delta_nonneg v
    have hu := delta_le_one v hp
    nlinarith
  exact h1.trans (h2.trans he)

theorem rho_le_one (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑ i, KSRankOne.atom (v i)) = 1) : rho N ≤ 1 :=
  (rho_le_delta v hd hp).trans (delta_le_one v hp)

theorem beta_pos (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑ i, KSRankOne.atom (v i)) = 1) : 0 < beta v := by
  have hn : (0 : ℝ) < N := by exact_mod_cast labels_pos v hd hp
  exact div_pos (delta_pos v hd hp) (by positivity)

theorem beta_entropy_bound (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑ i, KSRankOne.atom (v i)) = 1) (x : Fin N → ℝ)
    (hx : ∀ i, |x i| ≤ 1) : beta v * Progress.entropy x ≤ delta v := by
  have hn : (0 : ℝ) < N := by exact_mod_cast labels_pos v hd hp
  have he := mul_le_mul_of_nonneg_left (TrialProbability.entropy_le_two_labels x hx)
    (beta_pos v hd hp).le
  have hid : beta v * (2*(N : ℝ)) = delta v/50 := by
    unfold beta
    field_simp
    ring
  rw [hid] at he
  have hδ := delta_nonneg v
  linarith

/-- The new initial potential, rounding margin, and entropy are exactly
within the probability module's initial ledger allowance. -/
theorem initial_ledger_bound (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑ i, KSRankOne.atom (v i)) = 1) :
    KSDebitPotential.potential 0 0 v (fun _ => Source.weight 64 (zeta N) 0) (theta v) +
      rho N + beta v * Progress.entropy (0 : Fin N → ℝ) ≤ 36*delta v := by
  have hf := smooth_initial_potential_le v hd hp (zeta_pos (labels_pos v hd hp)).le
  have hr := rho_le_delta v hd hp
  have he := beta_entropy_bound v hd hp 0 (by intro i; norm_num)
  linarith

theorem densityFloor_pos (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑ i, KSRankOne.atom (v i)) = 1) : 0 < densityFloor v := by
  unfold densityFloor
  exact sq_pos_of_pos (div_pos (theta_pos v hd hp) (by norm_num))

theorem complexRadius_pos (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑ i, KSRankOne.atom (v i)) = 1) : 0 < complexRadius v := by
  have hmu := densityFloor_pos v hd hp
  have hr := rho_pos (labels_pos v hd hp)
  have hz := zeta_pos (labels_pos v hd hp)
  unfold complexRadius
  positivity

theorem objectiveBound_pos (d : ℕ) : 0 < objectiveBound d := by
  unfold objectiveBound
  have hd : (0:ℝ) ≤ d := Nat.cast_nonneg d
  positivity

theorem jointDerivativeBound_pos (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑ i, KSRankOne.atom (v i)) = 1) : 0 < jointDerivativeBound v := by
  have hV := objectiveBound_pos d
  have hR := complexRadius_pos v hd hp
  unfold jointDerivativeBound
  positivity

theorem coercivity_pos (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑ i, KSRankOne.atom (v i)) = 1) : 0 < coercivity v :=
  div_pos (theta_pos v hd hp) (by norm_num)

theorem derivativeBudget_gt_one (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑ i, KSRankOne.atom (v i)) = 1) : 1 < derivativeBudget v := by
  have hX := jointDerivativeBound_pos v hd hp
  have hg := coercivity_pos v hd hp
  unfold derivativeBudget
  have hh : 0 < (jointDerivativeBound v + 3*(jointDerivativeBound v)^2/coercivity v) *
      (1+jointDerivativeBound v/coercivity v)^4 := by positivity
  linarith

theorem derivativeBudget_pos (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑ i, KSRankOne.atom (v i)) = 1) : 0 < derivativeBudget v :=
  zero_lt_one.trans (derivativeBudget_gt_one v hd hp)

theorem queryStep_pos (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑ i, KSRankOne.atom (v i)) = 1) : 0 < queryStep v := by
  have hn : (0:ℝ) < N := by exact_mod_cast labels_pos v hd hp
  have hr := rho_pos (labels_pos v hd hp)
  have hb := beta_pos v hd hp
  have hM := derivativeBudget_pos v hd hp
  unfold queryStep
  positivity

theorem movementStep_pos (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑ i, KSRankOne.atom (v i)) = 1) : 0 < movementStep v := by
  have hr := rho_pos (labels_pos v hd hp)
  have hb := beta_pos v hd hp
  have hM := derivativeBudget_pos v hd hp
  unfold movementStep
  positivity

theorem movementStep_le_outwardStep (v : Fin N → Fin d → ℂ) :
    movementStep v ≤ outwardStep N := min_le_left _ _

theorem queryStep_le_outwardStep (v : Fin N → Fin d → ℂ) :
    queryStep v ≤ outwardStep N := min_le_left _ _

theorem hessianAccuracy_pos (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑ i, KSRankOne.atom (v i)) = 1) : 0 < hessianAccuracy v := by
  have hn : (0:ℝ) < N := by exact_mod_cast labels_pos v hd hp
  have hb := beta_pos v hd hp
  have ht := queryStep_pos v hd hp
  unfold hessianAccuracy
  positivity

theorem localAccuracy_pos (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑ i, KSRankOne.atom (v i)) = 1) : 0 < localAccuracy v := by
  have hb := beta_pos v hd hp
  have hh := movementStep_pos v hd hp
  unfold localAccuracy
  positivity

theorem queryStep_sq_bound (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑ i, KSRankOne.atom (v i)) = 1) :
    queryStep v^2 ≤ beta v/(128*(N:ℝ)*derivativeBudget v) := by
  have hn : (0:ℝ) < N := by exact_mod_cast labels_pos v hd hp
  have hb := beta_pos v hd hp
  have hM := derivativeBudget_pos v hd hp
  calc
    _ ≤ (Real.sqrt (beta v/(128*(N:ℝ)*derivativeBudget v)))^2 :=
      pow_le_pow_left₀ (queryStep_pos v hd hp).le (min_le_right _ _) 2
    _ = _ := Real.sq_sqrt (by positivity)

theorem movementStep_sq_bound (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑ i, KSRankOne.atom (v i)) = 1) :
    movementStep v^2 ≤ beta v/(4*derivativeBudget v) := by
  have hb := beta_pos v hd hp
  have hM := derivativeBudget_pos v hd hp
  calc
    _ ≤ (Real.sqrt (beta v/(4*derivativeBudget v)))^2 :=
      pow_le_pow_left₀ (movementStep_pos v hd hp).le (min_le_right _ _) 2
    _ = _ := Real.sq_sqrt (by positivity)

theorem horizon_budget (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑ i, KSRankOne.atom (v i)) = 1) :
    16*(N : ℝ) ≤ movementStep v^2*(horizon v : ℝ) := by
  have hh : 0 < movementStep v^2 := sq_pos_of_pos (movementStep_pos v hd hp)
  have hceil := Nat.le_ceil (16*(N:ℝ)/movementStep v^2)
  exact (div_le_iff₀ hh).mp hceil |>.trans_eq (mul_comm _ _)

theorem horizon_pos (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑ i, KSRankOne.atom (v i)) = 1) : 0 < horizon v := by
  have hn : (0:ℝ) < N := by exact_mod_cast labels_pos v hd hp
  have hh := horizon_budget v hd hp
  by_contra hz
  have hz0 : horizon v = 0 := Nat.eq_zero_of_not_pos hz
  rw [hz0, Nat.cast_zero, mul_zero] at hh
  linarith

theorem entropy_horizon_budget (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑ i, KSRankOne.atom (v i)) = 1) (x : Fin N → ℝ)
    (hx : ∀ i, |x i| ≤ 1) :
    8*Progress.entropy x ≤ movementStep v^2*(horizon v : ℝ) :=
  TrialProbability.horizon_from_labels x hx (horizon v) (horizon_budget v hd hp)


/-! Explicit polynomial majorants. They are kept as factored expressions,
rather than expanded into enormous monomials; every coefficient is natural. -/
def radiusInverseCap (N : ℕ) : ℝ := 10000*(1+22500*(N:ℝ)^2)
def jointDerivativeCap (N d : ℕ) : ℝ := objectiveBound d*(10*radiusInverseCap N)^4
def derivativeCap (N d : ℕ) : ℝ :=
  1+(jointDerivativeCap N d+3*(jointDerivativeCap N d)^2*(4*(N:ℝ))) *
    (1+jointDerivativeCap N d*(4*(N:ℝ)))^4

theorem sqrt_le_self_of_one_le {x : ℝ} (hx : 1 ≤ x) : Real.sqrt x ≤ x := by
  exact Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩

theorem delta_inv_le_labels (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑ i, KSRankOne.atom (v i)) = 1) : (delta v)⁻¹ ≤ (N:ℝ) :=
  (delta_inv_le_sqrt_labels v hd hp).trans
    (sqrt_le_self_of_one_le (by exact_mod_cast labels_pos v hd hp))

theorem theta_inv_le_two_labels (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑ i, KSRankOne.atom (v i)) = 1) : (theta v)⁻¹ ≤ 2*(N:ℝ) := by
  have hn : (1:ℝ) ≤ N := by exact_mod_cast labels_pos v hd hp
  exact (theta_inv_le_sqrt_two_labels v hd hp).trans (sqrt_le_self_of_one_le (by linarith))

theorem beta_inv_le (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑ i, KSRankOne.atom (v i)) = 1) : (beta v)⁻¹ ≤ 100*(N:ℝ)^2 := by
  have hh := mul_le_mul_of_nonneg_left (delta_inv_le_labels v hd hp)
    (show (0:ℝ) ≤ 100*(N:ℝ) by positivity)
  unfold beta
  rw [inv_div]
  simpa only [div_eq_mul_inv, pow_two, mul_assoc] using hh

theorem densityFloor_inv_le (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑ i, KSRankOne.atom (v i)) = 1) :
    (densityFloor v)⁻¹ ≤ 6400*(N:ℝ)^2 := by
  have hi := theta_inv_le_two_labels v hd hp
  have hn : 0 ≤ (theta v)⁻¹ := inv_nonneg.mpr (theta_pos v hd hp).le
  have hh := pow_le_pow_left₀ hn hi 2
  have hm := mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ) ≤ 1600)
  calc
    (densityFloor v)⁻¹ = 1600*((theta v)⁻¹)^2 := by
      simp only [densityFloor, inv_pow, div_eq_mul_inv, mul_pow]
      norm_num
    _ ≤ 1600*(2*(N:ℝ))^2 := hm
    _ = 6400*(N:ℝ)^2 := by ring

theorem rho_inv (N : ℕ) : (rho N)⁻¹ = 100*(N:ℝ)^2 := by
  simp [rho]

theorem zeta_inv (N : ℕ) : (zeta N)⁻¹ = 16000*(N:ℝ)^2 := by
  unfold zeta outwardStep
  rw [inv_div, div_div_eq_mul_div, div_eq_mul_inv, rho_inv]
  ring

theorem min_inv_le_sum {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (min a b)⁻¹ ≤ a⁻¹+b⁻¹ := by
  rcases le_total a b with h|h
  · rw [min_eq_left h]
    exact le_add_of_nonneg_right (inv_nonneg.mpr hb.le)
  · rw [min_eq_right h]
    exact le_add_of_nonneg_left (inv_nonneg.mpr ha.le)

theorem complexRadius_inv_le (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑ i, KSRankOne.atom (v i)) = 1) :
    (complexRadius v)⁻¹ ≤ radiusInverseCap N := by
  have hm := densityFloor_pos v hd hp
  have hr := rho_pos (labels_pos v hd hp)
  have hz := zeta_pos (labels_pos v hd hp)
  have h1 := min_inv_le_sum (by norm_num : (0:ℝ)<1) hm
  have h2 := min_inv_le_sum (show 0 < min 1 (densityFloor v) by positivity) hr
  have h3 := min_inv_le_sum (show 0 < min (min 1 (densityFloor v)) (rho N) by positivity) hz
  have hmu := densityFloor_inv_le v hd hp
  rw [rho_inv] at h2
  rw [zeta_inv] at h3
  norm_num only [inv_one] at h1
  have hall : (min (min (min 1 (densityFloor v)) (rho N)) (zeta N))⁻¹ ≤
      1+22500*(N:ℝ)^2 := by linarith
  have hh := mul_le_mul_of_nonneg_left hall (by norm_num : (0:ℝ) ≤ 10000)
  unfold complexRadius
  rw [inv_div]
  simpa only [radiusInverseCap, div_eq_mul_inv] using hh

theorem coercivity_inv_le (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑ i, KSRankOne.atom (v i)) = 1) :
    (coercivity v)⁻¹ ≤ 4*(N:ℝ) := by
  have hh := mul_le_mul_of_nonneg_left (theta_inv_le_two_labels v hd hp)
    (by norm_num : (0:ℝ) ≤ 2)
  unfold coercivity
  rw [inv_div]
  simpa only [div_eq_mul_inv, ← mul_assoc,
    show (2:ℝ)*2=4 by norm_num] using hh

theorem jointDerivativeBound_le (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑ i, KSRankOne.atom (v i)) = 1) :
    jointDerivativeBound v ≤ jointDerivativeCap N d := by
  have h10 := mul_le_mul_of_nonneg_left (complexRadius_inv_le v hd hp)
    (by norm_num : (0:ℝ) ≤ 10)
  have hnonneg : 0 ≤ 10*(complexRadius v)⁻¹ := by
    have hp := complexRadius_pos v hd hp
    positivity
  have hh := pow_le_pow_left₀ hnonneg h10 4
  have hv := mul_le_mul_of_nonneg_left hh (objectiveBound_pos d).le
  simpa only [jointDerivativeBound, jointDerivativeCap, div_eq_mul_inv] using hv

theorem derivativeBudget_le (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑ i, KSRankOne.atom (v i)) = 1) :
    derivativeBudget v ≤ derivativeCap N d := by
  have hX := (jointDerivativeBound_pos v hd hp).le
  have hXcap := jointDerivativeBound_le v hd hp
  have hg := (coercivity_pos v hd hp).le
  have hgcap := coercivity_inv_le v hd hp
  have hcap0 : 0 ≤ jointDerivativeCap N d := hX.trans hXcap
  have hn : (0:ℝ) ≤ 4*(N:ℝ) := by positivity
  have hquot : jointDerivativeBound v/coercivity v ≤ jointDerivativeCap N d*(4*(N:ℝ)) := by
    rw [div_eq_mul_inv]
    exact mul_le_mul hXcap hgcap (inv_nonneg.mpr hg) hcap0
  have hsq := pow_le_pow_left₀ hX hXcap 2
  have hsquot : (jointDerivativeBound v)^2/coercivity v ≤
      (jointDerivativeCap N d)^2*(4*(N:ℝ)) := by
    rw [div_eq_mul_inv]
    exact mul_le_mul hsq hgcap (inv_nonneg.mpr hg) (sq_nonneg _)
  have hfirst : jointDerivativeBound v+3*(jointDerivativeBound v)^2/coercivity v ≤
      jointDerivativeCap N d+3*(jointDerivativeCap N d)^2*(4*(N:ℝ)) := by
    calc
      _ = jointDerivativeBound v+3*((jointDerivativeBound v)^2/coercivity v) := by ring
      _ ≤ jointDerivativeCap N d+3*((jointDerivativeCap N d)^2*(4*(N:ℝ))) :=
        add_le_add hXcap (mul_le_mul_of_nonneg_left hsquot (by norm_num))
      _ = _ := by ring
  have hbase : 0 ≤ 1+jointDerivativeBound v/coercivity v := by positivity
  have hpow := pow_le_pow_left₀ hbase (add_le_add_left hquot 1) 4
  have hfirst0 : 0 ≤ jointDerivativeCap N d+3*(jointDerivativeCap N d)^2*(4*(N:ℝ)) := by positivity
  have hmul := mul_le_mul hfirst hpow (pow_nonneg hbase 4) hfirst0
  dsimp only [derivativeBudget, derivativeCap]
  linarith



theorem local_error_budget (v : Fin N → Fin d → ℂ) :
    4*localAccuracy v = beta v*movementStep v^2/2 := by
  unfold localAccuracy
  ring

/-- A conservative entrywise Hessian allowance; the actual Taylor term
has the smaller coefficient `1/12`. -/
theorem hessian_entry_budget (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑ i, KSRankOne.atom (v i)) = 1) :
    derivativeBudget v*queryStep v^2+4*hessianAccuracy v/queryStep v^2 ≤
      beta v/(16*(N:ℝ)) := by
  have hn : (0:ℝ) < N := by exact_mod_cast labels_pos v hd hp
  have hb := beta_pos v hd hp
  have hM := derivativeBudget_pos v hd hp
  have ht := queryStep_pos v hd hp
  have hsq := (le_div_iff₀ (by positivity : 0 < 128*(N:ℝ)*derivativeBudget v)).mp
    (queryStep_sq_bound v hd hp)
  have hnoise : 4*hessianAccuracy v/queryStep v^2 = beta v/(32*(N:ℝ)) := by
    unfold hessianAccuracy
    field_simp
    ring
  rw [hnoise]
  apply (le_div_iff₀ (by positivity : 0 < 16*(N:ℝ))).mpr
  have hid : beta v/(32*(N:ℝ))*(16*(N:ℝ)) = beta v/2 := by field_simp; norm_num
  nlinarith

theorem movement_error_budget (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑ i, KSRankOne.atom (v i)) = 1) :
    movementStep v^2*(beta v/2)+derivativeBudget v*movementStep v^4/24 ≤
      beta v*movementStep v^2 := by
  have hb := beta_pos v hd hp
  have hM := derivativeBudget_pos v hd hp
  have hs := (le_div_iff₀ (by positivity : 0 < 4*derivativeBudget v)).mp
    (movementStep_sq_bound v hd hp)
  have hm := mul_le_mul_of_nonneg_right hs (sq_nonneg (movementStep v))
  nlinarith [sq_nonneg (movementStep v)]

def queryInverseSquareCap (N d : ℕ) : ℝ :=
  256*(100*(N:ℝ)^2)^2 + 128*(N:ℝ)*derivativeCap N d*(100*(N:ℝ)^2)
def movementInverseSquareCap (N d : ℕ) : ℝ :=
  256*(100*(N:ℝ)^2)^2 + 4*derivativeCap N d*(100*(N:ℝ)^2)
def hessianAccuracyInverseCap (N d : ℕ) : ℝ :=
  128*(N:ℝ)*(100*(N:ℝ)^2)*queryInverseSquareCap N d
def localAccuracyInverseCap (N d : ℕ) : ℝ :=
  8*(100*(N:ℝ)^2)*movementInverseSquareCap N d
def horizonCap (N d : ℕ) : ℝ := 16*(N:ℝ)*movementInverseSquareCap N d+1

theorem derivativeCap_nonneg (N d : ℕ) : 0 ≤ derivativeCap N d := by
  unfold derivativeCap jointDerivativeCap objectiveBound radiusInverseCap
  positivity

theorem min_inv_square_le_sum (a b : ℝ) :
    ((min a b)^2)⁻¹ ≤ (a^2)⁻¹+(b^2)⁻¹ := by
  rcases le_total a b with h|h
  · rw [min_eq_left h]
    exact le_add_of_nonneg_right (inv_nonneg.mpr (sq_nonneg b))
  · rw [min_eq_right h]
    exact le_add_of_nonneg_left (inv_nonneg.mpr (sq_nonneg a))

theorem step_inverse_square_le (a : ℝ) {b C M : ℝ}
    (hb : 0 < b) (hC : 0 < C) (hM : 0 < M) :
    ((min a (Real.sqrt (b/(C*M))))^2)⁻¹ ≤ (a^2)⁻¹+C*M*b⁻¹ := by
  have hh := min_inv_square_le_sum a (Real.sqrt (b/(C*M)))
  rw [Real.sq_sqrt (by positivity), inv_div, div_eq_mul_inv] at hh
  exact hh

theorem outwardStep_inv (N : ℕ) : (outwardStep N)⁻¹ = 1600*(N:ℝ)^2 := by
  unfold outwardStep
  rw [inv_div, div_eq_mul_inv, rho_inv]
  ring

theorem outwardStep_inv_square (N : ℕ) :
    (outwardStep N^2)⁻¹ = 256*(100*(N:ℝ)^2)^2 := by
  rw [← inv_pow, outwardStep_inv]
  ring

theorem queryStep_inverse_square_le (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑ i, KSRankOne.atom (v i)) = 1) :
    (queryStep v^2)⁻¹ ≤ queryInverseSquareCap N d := by
  have hn : (0:ℝ) < N := by exact_mod_cast labels_pos v hd hp
  have hh := step_inverse_square_le (outwardStep N) (beta_pos v hd hp)
    (show 0 < 128*(N:ℝ) by positivity) (derivativeBudget_pos v hd hp)
  change (queryStep v^2)⁻¹ ≤ _ at hh
  rw [outwardStep_inv_square] at hh
  have hprod := mul_le_mul (derivativeBudget_le v hd hp) (beta_inv_le v hd hp)
    (inv_nonneg.mpr (beta_pos v hd hp).le) (derivativeCap_nonneg N d)
  have hm := mul_le_mul_of_nonneg_left hprod (show 0 ≤ 128*(N:ℝ) by positivity)
  dsimp only [queryInverseSquareCap]
  nlinarith

theorem movementStep_inverse_square_le (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑ i, KSRankOne.atom (v i)) = 1) :
    (movementStep v^2)⁻¹ ≤ movementInverseSquareCap N d := by
  have hh := step_inverse_square_le (outwardStep N) (beta_pos v hd hp)
    (show (0:ℝ) < 4 by norm_num) (derivativeBudget_pos v hd hp)
  change (movementStep v^2)⁻¹ ≤ _ at hh
  rw [outwardStep_inv_square] at hh
  have hprod := mul_le_mul (derivativeBudget_le v hd hp) (beta_inv_le v hd hp)
    (inv_nonneg.mpr (beta_pos v hd hp).le) (derivativeCap_nonneg N d)
  have hm := mul_le_mul_of_nonneg_left hprod (show (0:ℝ) ≤ 4 by norm_num)
  dsimp only [movementInverseSquareCap]
  nlinarith

theorem hessianAccuracy_inverse_le (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑ i, KSRankOne.atom (v i)) = 1) :
    (hessianAccuracy v)⁻¹ ≤ hessianAccuracyInverseCap N d := by
  have ht := queryStep_inverse_square_le v hd hp
  have hb := beta_inv_le v hd hp
  have hprod := mul_le_mul hb ht (inv_nonneg.mpr (sq_nonneg (queryStep v)))
    (show 0 ≤ 100*(N:ℝ)^2 by positivity)
  have hm := mul_le_mul_of_nonneg_left hprod (show 0 ≤ 128*(N:ℝ) by positivity)
  calc
    (hessianAccuracy v)⁻¹ = 128*(N:ℝ)*((beta v)⁻¹*(queryStep v^2)⁻¹) := by
      unfold hessianAccuracy
      rw [inv_div, div_eq_mul_inv, mul_inv_rev]
      ring
    _ ≤ 128*(N:ℝ)*(100*(N:ℝ)^2*queryInverseSquareCap N d) := hm
    _ = hessianAccuracyInverseCap N d := by unfold hessianAccuracyInverseCap; ring

theorem localAccuracy_inverse_le (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑ i, KSRankOne.atom (v i)) = 1) :
    (localAccuracy v)⁻¹ ≤ localAccuracyInverseCap N d := by
  have ht := movementStep_inverse_square_le v hd hp
  have hb := beta_inv_le v hd hp
  have hprod := mul_le_mul hb ht (inv_nonneg.mpr (sq_nonneg (movementStep v)))
    (show 0 ≤ 100*(N:ℝ)^2 by positivity)
  have hm := mul_le_mul_of_nonneg_left hprod (show (0:ℝ) ≤ 8 by norm_num)
  calc
    (localAccuracy v)⁻¹ = 8*((beta v)⁻¹*(movementStep v^2)⁻¹) := by
      unfold localAccuracy
      rw [inv_div, div_eq_mul_inv, mul_inv_rev]
      ring
    _ ≤ 8*(100*(N:ℝ)^2*movementInverseSquareCap N d) := hm
    _ = localAccuracyInverseCap N d := by unfold localAccuracyInverseCap; ring

theorem horizon_le_polynomial (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑ i, KSRankOne.atom (v i)) = 1) :
    (horizon v : ℝ) ≤ horizonCap N d := by
  have hh := movementStep_inverse_square_le v hd hp
  have hm := mul_le_mul_of_nonneg_left hh (show 0 ≤ 16*(N:ℝ) by positivity)
  have hc := Nat.ceil_lt_add_one (show 0 ≤ 16*(N:ℝ)/movementStep v^2 by positivity)
  change (horizon v : ℝ) < 16*(N:ℝ)/movementStep v^2+1 at hc
  rw [div_eq_mul_inv] at hc
  dsimp only [horizonCap]
  linarith

end SeamlessKS.Parameters
