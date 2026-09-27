import MatrixSpencer.RectangularParameters

/-!
# Dyadic tuning specified by integer comparisons

The depth is the first positive integer `m` for which `D ≤ N * 2^(2^m)`.
Its defining test uses multiplication and repeated squaring, rather than an
exact real logarithm. The logarithms below occur only in the proof of the
aspect-ratio estimate. The definition specifies the first successful test;
a separate counted-loop implementation is still needed for total runtime.
-/
namespace MatrixSpencer.RectangularRidgeTuning

def Good (N D m : ℕ) : Prop := 1 ≤ m ∧ D ≤ N * 2 ^ (2 ^ m)
instance (N D m : ℕ) : Decidable (Good N D m) := inferInstanceAs (Decidable (_ ∧ _))

private theorem self_le_two_pow (k : ℕ) : k ≤ 2 ^ k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [pow_succ]
    have hp : 0 < 2 ^ k := by positivity
    omega

theorem exists_good {N : ℕ} (hN : 1 ≤ N) (D : ℕ) : ∃ m, Good N D m := by
  refine ⟨D+1, by omega, ?_⟩
  have h1 := self_le_two_pow (D+1)
  have h2 := self_le_two_pow (2^(D+1))
  have h3 : 2^(2^(D+1)) ≤ N * 2^(2^(D+1)) := by
    calc
      _ = 1 * 2^(2^(D+1)) := (one_mul _).symm
      _ ≤ _ := Nat.mul_le_mul_right _ hN
  omega

noncomputable def depth (N D : ℕ) (hN : 1 ≤ N) : ℕ := Nat.find (exists_good hN D)
noncomputable def order (N D : ℕ) (hN : 1 ≤ N) : ℕ := 2 ^ depth N D hN

theorem depth_good (N D : ℕ) (hN : 1 ≤ N) : Good N D (depth N D hN) :=
  Nat.find_spec (exists_good hN D)

theorem depth_positive (N D : ℕ) (hN : 1 ≤ N) : 1 ≤ depth N D hN :=
  (depth_good N D hN).1

theorem depth_le (N D : ℕ) (hN : 1 ≤ N) : depth N D hN ≤ D+1 := by
  apply Nat.find_min'
  refine ⟨by omega, ?_⟩
  have h1 := self_le_two_pow (D+1)
  have h2 := self_le_two_pow (2^(D+1))
  have h3 : 2^(2^(D+1)) ≤ N * 2^(2^(D+1)) := by
    calc
      _ = 1 * 2^(2^(D+1)) := (one_mul _).symm
      _ ≤ _ := Nat.mul_le_mul_right _ hN
  omega

theorem order_two_le (N D : ℕ) (hN : 1 ≤ N) : 2 ≤ order N D hN := by
  have h := Nat.pow_le_pow_right (by norm_num : 1 ≤ (2 : ℕ)) (depth_positive N D hN)
  simpa [order] using h

theorem failed_previous {N D : ℕ} (hN : 1 ≤ N) (hm : 2 ≤ depth N D hN) :
    N * 2 ^ (2 ^ (depth N D hN - 1)) < D := by
  have h := Nat.find_min (exists_good hN D)
    (show depth N D hN - 1 < depth N D hN by omega)
  have hn : ¬ D ≤ N * 2 ^ (2 ^ (depth N D hN - 1)) := by
    intro hh
    exact h ⟨by omega, hh⟩
  omega

theorem logarithmic_bounds {N D : ℕ} (hN : 1 ≤ N) (hND : N ≤ D) :
    Real.log ((D : ℝ) / N) ≤ order N D hN ∧
    (order N D hN : ℝ) ≤ 4 * (1 + Real.log ((D : ℝ) / N)) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hd : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hr : (0 : ℝ) < (D : ℝ) / N := div_pos hd hn
  have hr1 : (1 : ℝ) ≤ (D : ℝ) / N := by
    apply (le_div_iff₀ hn).mpr
    simpa using (Nat.cast_le.mpr hND : (N : ℝ) ≤ D)
  have hlog : 0 ≤ Real.log ((D : ℝ) / N) := Real.log_nonneg hr1
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2lo : (1/2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hl2hi : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hp : 0 ≤ (order N D hN : ℝ) := Nat.cast_nonneg _
  constructor
  · have hb : (D : ℝ) / N ≤ (2 : ℝ) ^ order N D hN := by
      apply (div_le_iff₀ hn).mpr
      have h := (depth_good N D hN).2
      have hh : (D : ℝ) ≤ (N : ℝ) * (2 : ℝ) ^ order N D hN := by exact_mod_cast h
      nlinarith
    have hh := Real.log_le_log hr hb
    rw [Real.log_pow] at hh
    exact hh.trans (by nlinarith)
  · by_cases hm : depth N D hN = 1
    · simp only [order, hm, pow_one, Nat.cast_ofNat]
      linarith
    · have hm2 : 2 ≤ depth N D hN := by have := depth_positive N D hN; omega
      have hb : (2 : ℝ) ^ (2 ^ (depth N D hN - 1)) < (D : ℝ) / N := by
        apply (lt_div_iff₀ hn).mpr
        have hh : (N : ℝ) * (2 : ℝ) ^ (2 ^ (depth N D hN - 1)) < D := by
          exact_mod_cast failed_previous hN hm2
        nlinarith
      have hh := Real.log_lt_log (by positivity : (0 : ℝ) <
        (2 : ℝ) ^ (2 ^ (depth N D hN - 1))) hb
      rw [Real.log_pow] at hh
      have he : order N D hN = 2 ^ (depth N D hN - 1) * 2 := by
        unfold order
        conv_lhs => rw [show depth N D hN = (depth N D hN - 1)+1 by omega]
        rw [pow_succ]
      have he' : (order N D hN : ℝ) = (2 ^ (depth N D hN - 1) : ℕ) * (2 : ℝ) := by
        exact_mod_cast he
      have hp' : (0 : ℝ) ≤ (2 ^ (depth N D hN - 1) : ℕ) := Nat.cast_nonneg _
      nlinarith

theorem optimized_budget_le {N D : ℕ} (hN : 1 ≤ N) (hND : N ≤ D) :
    let p : ℝ := order N D hN
    Real.sqrt (N : ℝ) + RectangularParameters.strength D N (1/p) *
      (D : ℝ) ^ (1/p) / (1 - 1/p) +
      (4096 : ℝ) ^ (1/p) * (N : ℝ) ^ (1 - 1/p) /
        (RectangularParameters.strength D N (1/p) * (1/p)) ≤
      81 * Real.sqrt ((N : ℝ) * (1 + Real.log ((D : ℝ) / N))) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hd : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hr1 : (1 : ℝ) ≤ (D : ℝ) / N := by
    apply (le_div_iff₀ hn).mpr
    simpa using (Nat.cast_le.mpr hND : (N : ℝ) ≤ D)
  have he : RectangularParameters.aspect D N = (D : ℝ) / N := max_eq_right hr1
  have hp : (2 : ℝ) ≤ order N D hN := by exact_mod_cast order_two_le N D hN
  have hb := logarithmic_bounds hN hND
  have hh := RectangularParameters.optimized_budget_le_of_reciprocal hd hn hp
    (by simpa [he] using hb.1) (by simpa [he] using hb.2)
  simpa [he] using hh

structure State where
  level : ℕ
  power : ℕ
  threshold : ℕ
  deriving DecidableEq

def initial : State := ⟨1, 2, 4⟩
def advance (s : State) : State := ⟨s.level + 1, 2 * s.power, s.threshold * s.threshold⟩
def WellFormed (s : State) : Prop :=
  1 ≤ s.level ∧ s.power = 2 ^ s.level ∧ s.threshold = 2 ^ s.power

/-- A bounded comparison loop. Each failed test uses one level increment,
one doubling and one squaring; neither exponentiation nor logarithms occur
in the loop body. -/
def scan (N D : ℕ) : ℕ → State → Option State
  | 0, _ => none
  | fuel + 1, s => if D ≤ N * s.threshold then some s else scan N D fuel (advance s)

theorem initial_wellFormed : WellFormed initial := by norm_num [WellFormed, initial]

theorem advance_wellFormed {s : State} (hs : WellFormed s) : WellFormed (advance s) := by
  rcases hs with ⟨hlevel, hpower, hthreshold⟩
  refine ⟨by simpa [advance] using Nat.succ_le_succ hlevel, ?_, ?_⟩
  · change 2 * s.power = 2 ^ (s.level+1)
    rw [hpower, pow_succ, Nat.mul_comm]
  · change s.threshold * s.threshold = 2 ^ (2 * s.power)
    rw [hthreshold, ← pow_add]
    congr 1
    omega

theorem scan_success {N D : ℕ} (hN : 1 ≤ N) (fuel : ℕ) (s : State)
    (hs : WellFormed s) (hle : s.level ≤ depth N D hN)
    (hbudget : depth N D hN < s.level + fuel) :
    ∃ t, scan N D fuel s = some t ∧ WellFormed t ∧ t.level = depth N D hN := by
  induction fuel generalizing s with
  | zero => omega
  | succ fuel ih =>
    rw [scan]
    split_ifs with htest
    · refine ⟨s, rfl, hs, ?_⟩
      have hg : Good N D s.level := by
        refine ⟨hs.1, ?_⟩
        simpa only [hs.2.2, hs.2.1] using htest
      have hh : depth N D hN ≤ s.level := Nat.find_min' (exists_good hN D) hg
      omega
    · apply ih (advance s) (advance_wellFormed hs)
      · have hlt : s.level < depth N D hN := by
          by_contra hn
          have he : s.level = depth N D hN := by omega
          apply htest
          have hg := (depth_good N D hN).2
          simpa only [hs.2.2, hs.2.1, he] using hg
        change s.level + 1 ≤ depth N D hN
        omega
      · change depth N D hN < s.level + 1 + fuel
        omega

/-- At most D+1 tests return the desired dyadic tuning. -/
theorem scan_initial_success {N D : ℕ} (hN : 1 ≤ N) :
    ∃ t, scan N D (D+1) initial = some t ∧
      WellFormed t ∧ t.level = depth N D hN := by
  apply scan_success hN (D+1) initial initial_wellFormed (depth_positive N D hN)
  have h := depth_le N D hN
  change depth N D hN < 1 + (D+1)
  omega

/-- Arithmetic/comparison cost of exactly this scan (one multiplication and
comparison per test; one increment, doubling and squaring per failed test).
Input/output copying is accounted for separately by an enclosing algorithm. -/
def scanCost (N D : ℕ) : ℕ → State → ℕ
  | 0, _ => 0
  | fuel + 1, s => if D ≤ N * s.threshold then 2 else 5 + scanCost N D fuel (advance s)

theorem scanCost_le (N D fuel : ℕ) (s : State) : scanCost N D fuel s ≤ 5 * fuel := by
  induction fuel generalizing s with
  | zero => simp [scanCost]
  | succ fuel ih =>
    rw [scanCost]
    split_ifs
    · omega
    · have h := ih (advance s)
      omega

end MatrixSpencer.RectangularRidgeTuning
