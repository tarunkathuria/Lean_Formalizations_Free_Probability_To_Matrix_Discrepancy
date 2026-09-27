import MatrixSpencer.EpochCoordinateStep

/-!
# Finite fuel from actual phase progress

Operational time is charged to the Euclidean squared norm of the cube vector.
Early successful epochs are charged to newly frozen actual coordinates.
-/

open scoped BigOperators
noncomputable section
namespace MatrixSpencer

/-- Two nonnegative finite ledgers bound the number of events if every event
spends at least one of two positive thresholds. -/
theorem two_ledger_event_count_le (t d : ℕ → ℝ) (N : ℕ)
    {τ D T F : ℝ} (hτ : 0 < τ) (hD : 0 < D)
    (ht : ∀ j < N, 0 ≤ t j) (hd : ∀ j < N, 0 ≤ d j)
    (hsuccess : ∀ j < N, τ ≤ t j ∨ D ≤ d j)
    (hT : (∑ j ∈ Finset.range N, t j) ≤ T)
    (hF : (∑ j ∈ Finset.range N, d j) ≤ F) :
    (N : ℝ) ≤ T / τ + F / D := by
  have hone : ∀ j ∈ Finset.range N, (1 : ℝ) ≤ t j / τ + d j / D := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    rcases hsuccess j hj' with h | h
    · have h1 : (1 : ℝ) ≤ t j / τ := (le_div_iff₀ hτ).mpr (by simpa using h)
      linarith [div_nonneg (hd j hj') hD.le]
    · have h1 : (1 : ℝ) ≤ d j / D := (le_div_iff₀ hD).mpr (by simpa using h)
      linarith [div_nonneg (ht j hj') hτ.le]
  calc
    (N : ℝ) = ∑ _j ∈ Finset.range N, (1 : ℝ) := by simp
    _ ≤ ∑ j ∈ Finset.range N, (t j / τ + d j / D) := Finset.sum_le_sum hone
    _ = (∑ j ∈ Finset.range N, t j) / τ + (∑ j ∈ Finset.range N, d j) / D := by
      rw [Finset.sum_add_distrib, Finset.sum_div, Finset.sum_div]
    _ ≤ _ := add_le_add (div_le_div_of_nonneg_right hT hτ.le)
      (div_le_div_of_nonneg_right hF hD.le)

/-- Any lower bound on finite energy gains telescopes without a limit argument. -/
theorem finite_energy_gain_ledger (e t : ℕ → ℝ) (N : ℕ) (c : ℝ)
    (hgain : ∀ j < N, e j + c * t j ≤ e (j + 1)) :
    c * (∑ j ∈ Finset.range N, t j) ≤ e N - e 0 := by
  have h := FiniteProcessMoments.telescope_le (fun j => -e j)
    (fun j => c * t j) (fun _ => 0) N (fun j hj => by have hh := hgain j hj; dsimp; linarith)
  simp only [Finset.sum_const_zero, add_zero, ← Finset.mul_sum] at h
  linarith

variable {ι : Type*} [Fintype ι]

/-- The actual Euclidean squared norm of a cube vector is at most its number of coordinates. -/
theorem cube_euclidean_norm_sq_le_card {x : EuclideanSpace ℝ ι} (hx : ∀ i, |x i| ≤ 1) :
    ‖x‖ ^ 2 ≤ (Fintype.card ι : ℝ) := by
  rw [EuclideanSpace.norm_sq_eq]
  calc
    _ ≤ ∑ _i : ι, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      have h := hx i
      simp only [Real.norm_eq_abs]
      nlinarith [abs_nonneg (x i)]
    _ = _ := by simp

/-- An already frozen sign stays in the actual finite set of frozen coordinates. -/
theorem frozenCoordinates_subset_of_preserved {x y : EuclideanSpace ℝ ι}
    (h : ∀ i ∈ frozenCoordinates x, y i = x i) : frozenCoordinates x ⊆ frozenCoordinates y := by
  classical
  intro i hi
  rw [mem_frozenCoordinates, h i hi]
  exact (mem_frozenCoordinates x i).mp hi

/-- The actual frozen-coordinate count is bounded by the original label count. -/
theorem frozenCoordinates_card_le (x : EuclideanSpace ℝ ι) :
    (frozenCoordinates x).card ≤ Fintype.card ι := Finset.card_le_univ _

/-- Operational time at gain rate k/32 has total at most 32 inside the cube. -/
theorem phase_epoch_operational_time_le (x : ℕ → EuclideanSpace ℝ ι) (t : ℕ → ℝ) (N : ℕ)
    (hk : 0 < Fintype.card ι) (hx : ∀ i, |x N i| ≤ 1)
    (hgain : ∀ j < N, ‖x j‖ ^ 2 + ((Fintype.card ι : ℝ) / 32) * t j ≤ ‖x (j + 1)‖ ^ 2) :
    (∑ j ∈ Finset.range N, t j) ≤ 32 := by
  have he := finite_energy_gain_ledger (fun j => ‖x j‖ ^ 2) t N
    ((Fintype.card ι : ℝ) / 32) hgain
  have hn := cube_euclidean_norm_sq_le_card hx
  have hk' : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hk
  nlinarith [sq_nonneg ‖x 0‖]

/-- Frozen-coordinate increases telescope to at most the original label count. -/
theorem phase_epoch_frozen_ledger (x : ℕ → EuclideanSpace ℝ ι) (N : ℕ) :
    (∑ j ∈ Finset.range N,
      (((frozenCoordinates (x (j + 1))).card : ℝ) - (frozenCoordinates (x j)).card)) ≤
      (Fintype.card ι : ℝ) := by
  have he := FiniteProcessMoments.telescope_eq
    (fun j => ((frozenCoordinates (x j)).card : ℝ))
    (fun j => ((frozenCoordinates (x (j + 1))).card : ℝ) - (frozenCoordinates (x j)).card)
    N (fun j _ => by ring)
  have hb : ((frozenCoordinates (x N)).card : ℝ) ≤ Fintype.card ι := by
    exact_mod_cast frozenCoordinates_card_le (x N)
  have h0 : (0 : ℝ) ≤ (frozenCoordinates (x 0)).card := Nat.cast_nonneg _
  linarith

/-- The actual cube and frozen-count ledgers bound the number of successful epochs.
A time-full epoch may overshoot τ; the stated bound only requires t ≥ τ. -/
theorem phase_successful_epoch_count_le (x : ℕ → EuclideanSpace ℝ ι) (t : ℕ → ℝ) (N : ℕ)
    (hk : 0 < Fintype.card ι) {τ β : ℝ} (hτ : 0 < τ) (hβ : 0 < β)
    (hx : ∀ i, |x N i| ≤ 1) (ht : ∀ j < N, 0 ≤ t j)
    (hfrozen : ∀ j < N, frozenCoordinates (x j) ⊆ frozenCoordinates (x (j + 1)))
    (hgain : ∀ j < N, ‖x j‖ ^ 2 + ((Fintype.card ι : ℝ) / 32) * t j ≤ ‖x (j + 1)‖ ^ 2)
    (hsuccess : ∀ j < N, τ ≤ t j ∨ β * (Fintype.card ι : ℝ) / 2 ≤
      ((frozenCoordinates (x (j + 1))).card : ℝ) - (frozenCoordinates (x j)).card) :
    (N : ℝ) ≤ 32 / τ + 2 / β := by
  have hk' : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hk
  have h := two_ledger_event_count_le t
    (fun j => ((frozenCoordinates (x (j + 1))).card : ℝ) - (frozenCoordinates (x j)).card)
    N hτ (by positivity : 0 < β * (Fintype.card ι : ℝ) / 2) ht
    (fun j hj => sub_nonneg.mpr (by exact_mod_cast Finset.card_le_card (hfrozen j hj)))
    hsuccess (phase_epoch_operational_time_le x t N hk hx hgain) (phase_epoch_frozen_ledger x N)
  have he : (Fintype.card ι : ℝ) / (β * (Fintype.card ι : ℝ) / 2) = 2 / β := by
    field_simp
  rwa [he] at h

/-- If every nonterminal epoch has the stated actual progress, a sequence longer
than the finite ledger bound contains a terminal state. -/
theorem phase_epoch_terminal_before_bound (x : ℕ → EuclideanSpace ℝ ι) (t : ℕ → ℝ)
    (terminal : ℕ → Prop) (N : ℕ) (hk : 0 < Fintype.card ι)
    {τ β : ℝ} (hτ : 0 < τ) (hβ : 0 < β) (hN : 32 / τ + 2 / β < (N : ℝ))
    (hx : ∀ i, |x N i| ≤ 1) (ht : ∀ j < N, 0 ≤ t j)
    (hfrozen : ∀ j < N, frozenCoordinates (x j) ⊆ frozenCoordinates (x (j + 1)))
    (hgain : ∀ j < N, ‖x j‖ ^ 2 + ((Fintype.card ι : ℝ) / 32) * t j ≤ ‖x (j + 1)‖ ^ 2)
    (hsuccess : ∀ j < N, ¬terminal j → τ ≤ t j ∨ β * (Fintype.card ι : ℝ) / 2 ≤
      ((frozenCoordinates (x (j + 1))).card : ℝ) - (frozenCoordinates (x j)).card) :
    ∃ j < N, terminal j := by
  by_contra hn
  push_neg at hn
  have hb := phase_successful_epoch_count_le x t N hk hτ hβ hx ht hfrozen hgain
    (fun j hj => hsuccess j hj (hn j hj))
  linarith

/-- Applied to the actual half-phase stopping rule, the finite ledgers force
at least half the original coordinates to become signs. -/
theorem phase_half_frozen_before_bound (x : ℕ → EuclideanSpace ℝ ι) (t : ℕ → ℝ)
    (N : ℕ) (hk : 0 < Fintype.card ι) {τ β : ℝ} (hτ : 0 < τ) (hβ : 0 < β)
    (hN : 32 / τ + 2 / β < (N : ℝ))
    (hx : ∀ i, |x N i| ≤ 1) (ht : ∀ j < N, 0 ≤ t j)
    (hfrozen : ∀ j < N, frozenCoordinates (x j) ⊆ frozenCoordinates (x (j + 1)))
    (hgain : ∀ j < N, ‖x j‖ ^ 2 + ((Fintype.card ι : ℝ) / 32) * t j ≤ ‖x (j + 1)‖ ^ 2)
    (hsuccess : ∀ j < N, 2 * (frozenCoordinates (x j)).card < Fintype.card ι →
      τ ≤ t j ∨ β * (Fintype.card ι : ℝ) / 2 ≤
        ((frozenCoordinates (x (j + 1))).card : ℝ) - (frozenCoordinates (x j)).card) :
    ∃ j < N, Fintype.card ι ≤ 2 * (frozenCoordinates (x j)).card := by
  exact phase_epoch_terminal_before_bound x t
    (fun j => Fintype.card ι ≤ 2 * (frozenCoordinates (x j)).card) N hk hτ hβ hN
    hx ht hfrozen hgain (fun j hj hn => hsuccess j hj (Nat.lt_of_not_ge hn))

end MatrixSpencer
