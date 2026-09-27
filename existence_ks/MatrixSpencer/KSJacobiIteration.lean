import MatrixSpencer.KSJacobiStep
import Mathlib.Data.List.FinRange
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# A finite Jacobi run with an explicitly scanned maximum pivot

The candidate list is built from `List.finRange`, and the maximum is selected
by real comparisons in a recursive finite scan. No maximizing index is chosen
by an existence theorem. This file concerns exact real arithmetic.
-/

open Matrix
open scoped BigOperators
noncomputable section
namespace MatrixSpencer.KSJacobiIteration

section Scan
variable {α : Type*}

def maxScan (score : α → ℝ) : List α → Option α
  | [] => none
  | p :: ps => match maxScan score ps with
    | none => some p
    | some q => if score q ≤ score p then some p else some q

theorem maxScan_none_iff (score : α → ℝ) (ps : List α) :
    maxScan score ps = none ↔ ps = [] := by
  cases ps with
  | nil => simp [maxScan]
  | cons p ps =>
    simp only [maxScan, List.cons_ne_nil, iff_false]
    cases maxScan score ps with
    | none => simp
    | some q => dsimp; split_ifs <;> simp

theorem maxScan_mem (score : α → ℝ) (ps : List α) {q : α}
    (hq : maxScan score ps = some q) : q ∈ ps := by
  induction ps generalizing q with
  | nil => simp [maxScan] at hq
  | cons p ps ih =>
    simp only [maxScan] at hq
    cases ht : maxScan score ps with
    | none =>
      simp only [ht, Option.some.injEq] at hq
      exact hq ▸ List.mem_cons_self
    | some r =>
      simp only [ht] at hq
      split_ifs at hq with hle
      · simp only [Option.some.injEq] at hq
        exact hq ▸ List.mem_cons_self
      · simp only [Option.some.injEq] at hq
        exact List.mem_cons_of_mem p (hq ▸ ih ht)

theorem maxScan_maximal (score : α → ℝ) (ps : List α) {q : α}
    (hq : maxScan score ps = some q) {p : α} (hp : p ∈ ps) : score p ≤ score q := by
  induction ps generalizing q with
  | nil => simp at hp
  | cons a ps ih =>
    simp only [maxScan] at hq
    cases ht : maxScan score ps with
    | none =>
      have hnil := (maxScan_none_iff score ps).mp ht
      subst ps
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      simp only [ht, Option.some.injEq] at hq
      subst p
      subst q
      exact le_rfl
    | some r =>
      simp only [ht] at hq
      rcases List.mem_cons.mp hp with hpa | hps
      · subst p
        split_ifs at hq with hle
        · have heq : a = q := Option.some.inj hq
          subst q
          exact le_rfl
        · have heq : r = q := Option.some.inj hq
          subst q
          exact (lt_of_not_ge hle).le
      · have hpr := ih ht hps
        split_ifs at hq with hle
        · have heq : a = q := Option.some.inj hq
          subst q
          exact hpr.trans hle
        · have heq : r = q := Option.some.inj hq
          subst q
          exact hpr

end Scan

variable {d : ℕ}

def candidates (d : ℕ) : List (Fin d × Fin d) :=
  ((List.finRange d).flatMap (fun i => (List.finRange d).map (fun j => (i, j)))).filter
    (fun p => p.1 ≠ p.2)

theorem mem_candidates (p : Fin d × Fin d) : p ∈ candidates d ↔ p.1 ≠ p.2 := by
  simp [candidates, List.mem_flatMap, List.mem_map]

def pivotScore (K : Matrix (Fin d) (Fin d) ℝ) (p : Fin d × Fin d) : ℝ := K p.1 p.2 ^ 2

def pivot (K : Matrix (Fin d) (Fin d) ℝ) : Option (Fin d × Fin d) :=
  maxScan (pivotScore K) (candidates d)

theorem pivot_distinct (K : Matrix (Fin d) (Fin d) ℝ) {p : Fin d × Fin d}
    (hp : pivot K = some p) : p.1 ≠ p.2 :=
  (mem_candidates p).mp (maxScan_mem (pivotScore K) (candidates d) hp)

theorem pivot_maximal (K : Matrix (Fin d) (Fin d) ℝ) {p : Fin d × Fin d}
    (hp : pivot K = some p) (i j : Fin d) (hij : i ≠ j) : K i j ^ 2 ≤ K p.1 p.2 ^ 2 :=
  maxScan_maximal (pivotScore K) (candidates d) hp ((mem_candidates (i, j)).mpr hij)

theorem no_pivot_energy_zero (K : Matrix (Fin d) (Fin d) ℝ) (hp : pivot K = none) :
    KSJacobiStep.offDiagonalEnergy K = 0 := by
  have hc := (maxScan_none_iff (pivotScore K) (candidates d)).mp hp
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  by_cases hij : i = j
  · simp [hij]
  · have hm := (mem_candidates (i, j)).mpr hij
    rw [hc] at hm
    contradiction

/-- The scanned pivot dominates the off-diagonal average (using the safe count `d²`). -/
theorem energy_le_dimension_mul_pivot (K : Matrix (Fin d) (Fin d) ℝ)
    {p : Fin d × Fin d} (hp : pivot K = some p) :
    KSJacobiStep.offDiagonalEnergy K ≤ (d : ℝ) ^ 2 * K p.1 p.2 ^ 2 := by
  calc
    _ ≤ ∑ _i : Fin d, ∑ _j : Fin d, K p.1 p.2 ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      by_cases hij : i = j
      · simp only [if_pos hij]
        positivity
      · simp only [if_neg hij]
        exact pivot_maximal K hp i j hij
    _ = _ := by simp; ring

def selectedRotation (K : Matrix (Fin d) (Fin d) ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  match pivot K with
  | none => 1
  | some p => KSJacobiStep.rotation K p.1 p.2

def advance (K : Matrix (Fin d) (Fin d) ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  (selectedRotation K)ᵀ * K * selectedRotation K

theorem advance_of_none (K : Matrix (Fin d) (Fin d) ℝ) (hp : pivot K = none) :
    advance K = K := by simp [advance, selectedRotation, hp]

theorem advance_of_some (K : Matrix (Fin d) (Fin d) ℝ) {p : Fin d × Fin d}
    (hp : pivot K = some p) : advance K = KSJacobiStep.step K p.1 p.2 := by
  simp only [advance, selectedRotation, hp, KSJacobiStep.step]

theorem advance_symmetric (K : Matrix (Fin d) (Fin d) ℝ) (hK : K.IsSymm) :
    (advance K).IsSymm := by
  cases hp : pivot K with
  | none => simpa only [advance_of_none K hp] using hK
  | some p => rw [advance_of_some K hp]; exact KSJacobiStep.step_symmetric K hK p.1 p.2

def denominator (d : ℕ) : ℝ := (d : ℝ) ^ 2 + 1

def contraction (d : ℕ) : ℝ := 1 - 1 / denominator d

theorem denominator_one_le (d : ℕ) : 1 ≤ denominator d := by
  dsimp [denominator]
  nlinarith [sq_nonneg (d : ℝ)]

theorem denominator_pos (d : ℕ) : 0 < denominator d := lt_of_lt_of_le zero_lt_one (denominator_one_le d)

theorem contraction_nonneg (d : ℕ) : 0 ≤ contraction d := by
  unfold contraction
  exact sub_nonneg.mpr ((div_le_one (denominator_pos d)).mpr (denominator_one_le d))

/-- The `d²+1` denominator includes dimensions zero and one without exceptional division. -/
theorem advance_energy_contract (K : Matrix (Fin d) (Fin d) ℝ) (hK : K.IsSymm) :
    KSJacobiStep.offDiagonalEnergy (advance K) ≤
      contraction d * KSJacobiStep.offDiagonalEnergy K := by
  cases hp : pivot K with
  | none => rw [advance_of_none K hp, no_pivot_energy_zero K hp]; simp
  | some p =>
    rw [advance_of_some K hp, KSJacobiStep.step_offDiagonalEnergy K hK p.1 p.2
      (pivot_distinct K hp)]
    have hbound := energy_le_dimension_mul_pivot K hp
    have hd := denominator_pos d
    have hstrong : KSJacobiStep.offDiagonalEnergy K ≤
        denominator d * (2 * K p.1 p.2 ^ 2) := by
      dsimp [denominator]
      nlinarith [sq_nonneg (K p.1 p.2), sq_nonneg (d : ℝ)]
    have hdiv : KSJacobiStep.offDiagonalEnergy K / denominator d ≤ 2 * K p.1 p.2 ^ 2 :=
      (div_le_iff₀ hd).mpr (by nlinarith [hstrong])
    calc
      _ ≤ KSJacobiStep.offDiagonalEnergy K - KSJacobiStep.offDiagonalEnergy K / denominator d :=
        sub_le_sub_left hdiv _
      _ = _ := by unfold contraction; ring

def run (K : Matrix (Fin d) (Fin d) ℝ) : ℕ → Matrix (Fin d) (Fin d) ℝ
  | 0 => K
  | n + 1 => advance (run K n)

theorem run_symmetric (K : Matrix (Fin d) (Fin d) ℝ) (hK : K.IsSymm) (n : ℕ) :
    (run K n).IsSymm := by
  induction n with
  | zero => exact hK
  | succ n ih => exact advance_symmetric _ ih

/-- Geometric decay for the actual recursively updated matrices. -/
theorem run_energy_geometric (K : Matrix (Fin d) (Fin d) ℝ) (hK : K.IsSymm) (n : ℕ) :
    KSJacobiStep.offDiagonalEnergy (run K n) ≤
      contraction d ^ n * KSJacobiStep.offDiagonalEnergy K := by
  induction n with
  | zero => simp [run]
  | succ n ih =>
    calc
      _ ≤ contraction d * KSJacobiStep.offDiagonalEnergy (run K n) :=
        advance_energy_contract _ (run_symmetric K hK n)
      _ ≤ contraction d * (contraction d ^ n * KSJacobiStep.offDiagonalEnergy K) :=
        mul_le_mul_of_nonneg_left ih (contraction_nonneg d)
      _ = _ := by rw [pow_succ]; ring

/-- An elementary rational envelope for the geometric decay. -/
theorem contraction_pow_le_reciprocal (d n : ℕ) :
    contraction d ^ n ≤ denominator d / (denominator d + (n : ℝ)) := by
  have hd := denominator_pos d
  induction n with
  | zero => simp [hd.ne']
  | succ n ih =>
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hdn : 0 < denominator d + (n : ℝ) := by positivity
    have hdn' : 0 < denominator d + ((n : ℝ) + 1) := by positivity
    rw [pow_succ', Nat.cast_add, Nat.cast_one]
    calc
      _ ≤ contraction d * (denominator d / (denominator d + (n : ℝ))) :=
        mul_le_mul_of_nonneg_left ih (contraction_nonneg d)
      _ = (denominator d - 1) / (denominator d + (n : ℝ)) := by
        unfold contraction
        field_simp
      _ ≤ _ := (div_le_div_iff₀ hdn hdn').mpr (by nlinarith)

theorem run_energy_reciprocal (K : Matrix (Fin d) (Fin d) ℝ) (hK : K.IsSymm) (n : ℕ) :
    KSJacobiStep.offDiagonalEnergy (run K n) ≤
      denominator d * KSJacobiStep.offDiagonalEnergy K / (denominator d + (n : ℝ)) := by
  calc
    _ ≤ contraction d ^ n * KSJacobiStep.offDiagonalEnergy K := run_energy_geometric K hK n
    _ ≤ (denominator d / (denominator d + (n : ℝ))) * KSJacobiStep.offDiagonalEnergy K :=
      mul_le_mul_of_nonneg_right (contraction_pow_le_reciprocal d n)
        (KSJacobiStep.offDiagonalEnergy_nonneg K)
    _ = _ := by ring

/-- A conservative explicit arithmetic bound on the number of rotations.
Its dependence is polynomial in initial squared norm and inverse tolerance;
the sharper logarithmic count is not needed for this finite-run guarantee. -/
def iterationCount (K : Matrix (Fin d) (Fin d) ℝ) (τ : ℝ) : ℕ :=
  ⌈denominator d * KSJacobiStep.offDiagonalEnergy K / τ ^ 2⌉₊

theorem run_energy_accuracy (K : Matrix (Fin d) (Fin d) ℝ) (hK : K.IsSymm)
    {τ : ℝ} (hτ : 0 < τ) :
    KSJacobiStep.offDiagonalEnergy (run K (iterationCount K τ)) ≤ τ ^ 2 := by
  have hn : denominator d * KSJacobiStep.offDiagonalEnergy K / τ ^ 2 ≤
      (iterationCount K τ : ℝ) := Nat.le_ceil _
  have hτsq : 0 < τ ^ 2 := sq_pos_of_pos hτ
  have hn' := (div_le_iff₀ hτsq).mp hn
  have hd := denominator_pos d
  have hden : 0 < denominator d + (iterationCount K τ : ℝ) := by positivity
  refine (run_energy_reciprocal K hK (iterationCount K τ)).trans ?_
  apply (div_le_iff₀ hden).mpr
  nlinarith

/-- The actual run attains the specified off-diagonal Frobenius tolerance. -/
theorem run_offDiagonalFrobenius_accuracy (K : Matrix (Fin d) (Fin d) ℝ) (hK : K.IsSymm)
    {τ : ℝ} (hτ : 0 < τ) :
    Real.sqrt (KSJacobiStep.offDiagonalEnergy (run K (iterationCount K τ))) ≤ τ := by
  exact (Real.sqrt_le_iff).mpr ⟨hτ.le, run_energy_accuracy K hK hτ⟩

theorem selectedRotation_transpose_mul (K : Matrix (Fin d) (Fin d) ℝ) :
    (selectedRotation K)ᵀ * selectedRotation K = 1 := by
  cases hp : pivot K with
  | none => simp [selectedRotation, hp]
  | some p =>
    simp only [selectedRotation, hp]
    exact KSJacobiStep.rotation_transpose_mul_self K p.1 p.2 (pivot_distinct K hp)

theorem selectedRotation_mul_transpose (K : Matrix (Fin d) (Fin d) ℝ) :
    selectedRotation K * (selectedRotation K)ᵀ = 1 :=
  Matrix.mul_eq_one_comm.mp (selectedRotation_transpose_mul K)

/-- The explicitly accumulated product of the rotations actually used by the run. -/
def accumulatedBasis (K : Matrix (Fin d) (Fin d) ℝ) : ℕ → Matrix (Fin d) (Fin d) ℝ
  | 0 => 1
  | n + 1 => accumulatedBasis K n * selectedRotation (run K n)

theorem accumulatedBasis_transpose_mul (K : Matrix (Fin d) (Fin d) ℝ) (n : ℕ) :
    (accumulatedBasis K n)ᵀ * accumulatedBasis K n = 1 := by
  induction n with
  | zero => simp [accumulatedBasis]
  | succ n ih =>
    simp only [accumulatedBasis, Matrix.transpose_mul]
    calc
      _ = (selectedRotation (run K n))ᵀ *
          ((accumulatedBasis K n)ᵀ * accumulatedBasis K n) * selectedRotation (run K n) := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [ih, Matrix.mul_one, selectedRotation_transpose_mul]

theorem accumulatedBasis_mul_transpose (K : Matrix (Fin d) (Fin d) ℝ) (n : ℕ) :
    accumulatedBasis K n * (accumulatedBasis K n)ᵀ = 1 :=
  Matrix.mul_eq_one_comm.mp (accumulatedBasis_transpose_mul K n)

/-- The final matrix and its computed basis retain the exact input conjugation. -/
theorem run_eq_conjugation (K : Matrix (Fin d) (Fin d) ℝ) (n : ℕ) :
    run K n = (accumulatedBasis K n)ᵀ * K * accumulatedBasis K n := by
  induction n with
  | zero => simp [run, accumulatedBasis]
  | succ n ih =>
    simp only [run, advance, accumulatedBasis, Matrix.transpose_mul, ih, Matrix.mul_assoc]

end MatrixSpencer.KSJacobiIteration
