import MatrixSpencer.KSEighthWalkQuality

/-! Explicit input-scaled parameters and finite cutoff for the eighth walk. -/

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSEighthInputParameters
open KSEighthWalkRun KSEighthPreparationCost
variable {N d : ℕ}

def delta (ε : ℝ) := Real.sqrt ε
def tau (N : ℕ) (ε : ℝ) := delta ε/(100*((N : ℝ)+1))
def rho (v : Fin N → Fin d → ℂ) (ε : ℝ) := tau N ε/(atomCap v+1)
def kappa (N : ℕ) (ε : ℝ) := delta ε/((N : ℝ)+1)
def theta (d : ℕ) (ε : ℝ) := ksRegularizerScale ε (Fin d)

theorem delta_pos {ε : ℝ} (hε : 0 < ε) : 0 < delta ε := Real.sqrt_pos.mpr hε

theorem tau_pos (N : ℕ) {ε : ℝ} (hε : 0 < ε) : 0 < tau N ε := by
  have h := delta_pos hε
  unfold tau
  positivity

theorem rho_pos (v : Fin N → Fin d → ℂ) {ε : ℝ} (hε : 0 < ε) : 0 < rho v ε := by
  have h := tau_pos N hε
  have ha := atomCap_pos v
  unfold rho
  positivity

theorem kappa_pos (N : ℕ) {ε : ℝ} (hε : 0 < ε) : 0 < kappa N ε := by
  have h := delta_pos hε
  unfold kappa
  positivity

theorem theta_pos (d : ℕ) {ε : ℝ} (hε : 0 < ε) (hd : 0 < d) : 0 < theta d ε := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  exact ksRegularizerScale_pos hε

def controller (v : Fin N → Fin d → ℂ) {ε : ℝ} (hε : 0 < ε) (hd : 0 < d) : Controller N :=
  KSEighthNumericalController.controller v (rho_pos v hε) (theta_pos d hε hd) (kappa_pos N hε) hd (τ := tau N ε)

def cutoff (v : Fin N → Fin d → ℂ) {ε : ℝ} (hε : 0 < ε) (hd : 0 < d) : ℕ :=
  max 1 ⌈(N : ℝ)/(4*(controller v hε hd).stepSize^2)⌉₊

theorem cutoff_pos (v : Fin N → Fin d → ℂ) {ε : ℝ} (hε : 0 < ε) (hd : 0 < d) :
    0 < cutoff v hε hd := lt_of_lt_of_le (by decide : 0 < (1 : ℕ)) (le_max_left _ _)

theorem cutoff_bound (v : Fin N → Fin d → ℂ) {ε : ℝ} (hε : 0 < ε) (hd : 0 < d) :
    (N : ℝ) ≤ 4*(controller v hε hd).stepSize^2*(cutoff v hε hd : ℝ) := by
  have ht := (controller v hε hd).step_pos
  have hc := Nat.le_ceil ((N : ℝ)/(4*(controller v hε hd).stepSize^2))
  have hm : (⌈(N : ℝ)/(4*(controller v hε hd).stepSize^2)⌉₊ : ℝ) ≤ (cutoff v hε hd : ℝ) :=
    Nat.cast_le.mpr (le_max_right _ _)
  have he := (div_le_iff₀ (by positivity : 0 < 4*(controller v hε hd).stepSize^2)).mp (hc.trans hm)
  nlinarith

theorem cutoff_probability_le (v : Fin N → Fin d → ℂ) {ε : ℝ} (hε : 0 < ε) (hd : 0 < d) :
    let C := controller v hε hd
    cutoffProbability C (cutoff v hε hd) (initialState C) ≤ 1/8 := by
  dsimp only
  apply (cutoffProbability_le _ _ (cutoff_pos v hε hd) _).trans
  have ht := (controller v hε hd).step_pos
  have hT : (0 : ℝ) < cutoff v hε hd := Nat.cast_pos.mpr (cutoff_pos v hε hd)
  rw [div_le_iff₀ (by positivity : 0 < (controller v hε hd).stepSize^2/2*(cutoff v hε hd : ℝ))]
  nlinarith [cutoff_bound v hε hd]

theorem tau_budget (N : ℕ) {ε : ℝ} (hε : 0 < ε) : tau N ε*N ≤ delta ε/100 := by
  have hδ := delta_pos hε
  unfold tau
  rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 100)]
  nlinarith

theorem kappa_budget (N : ℕ) {ε : ℝ} (hε : 0 < ε) : kappa N ε*N ≤ delta ε := by
  have hδ := delta_pos hε
  unfold kappa
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0 : ℝ) < N+1)]
  nlinarith

theorem charge_budget (v : Fin N → Fin d → ℂ) {ε : ℝ} (hε : 0 < ε) :
    charge v (rho v ε) (tau N ε)*N ≤ delta ε/50 := by
  have hτ := tau_pos N hε
  have ha := atomCap_pos v
  have hpart : rho v ε*atomCap v ≤ tau N ε := by
    unfold rho
    rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith : 0 < atomCap v+1)]
    nlinarith
  have h := mul_le_mul_of_nonneg_right (show charge v (rho v ε) (tau N ε) ≤ 2*tau N ε by
    unfold charge; linarith) (Nat.cast_nonneg (α := ℝ) N)
  nlinarith [tau_budget N hε]

theorem total_budget (v : Fin N → Fin d → ℂ) {ε : ℝ} (hε : 0 < ε) :
    charge v (rho v ε) (tau N ε)*N + kappa N ε*N/16 ≤ delta ε := by
  have hδ := delta_pos hε
  have hc := charge_budget v hε
  have hk := kappa_budget N hε
  linarith

/-- The actual finite walk has expected center norm at most `19 sqrt ε`. -/
theorem expected_norm_le (v : Fin N → Fin d → ℂ) {ε : ℝ} (hε : 0 < ε) (hd : 0 < d)
    (hparseval : (∑ i, KSRankOne.atom (v i)) = 1)
    (hsize : ∀ i, ‖KSRankOne.atom (v i)‖ ≤ ε) (T : ℕ) :
    let C := controller v hε hd
    (run C T (initialState C)).expectation
      (fun q => ‖KSPotentialModels.center (fun i => KSRankOne.atom (v i)) q.coeff‖) ≤ 19*delta ε := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  have he := KSEighthWalkQuality.expected_norm_le v (rho_pos v hε) (tau_pos N hε)
    (theta_pos d hε hd) (kappa_pos N hε) hd T
  have hi := KSFinalAssembly.eighth_initial_bound v hparseval hε hsize
  have hb := total_budget v hε
  dsimp only
  change _ ≤ 19*Real.sqrt ε
  change _ ≤ _ + _ + _ at he
  dsimp only [theta, delta] at he hb
  exact he.trans (by linarith)

end MatrixSpencer.KSEighthInputParameters
