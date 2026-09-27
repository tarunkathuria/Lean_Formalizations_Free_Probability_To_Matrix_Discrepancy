import MatrixSpencer.KSFullManuscriptAlgorithm
import MatrixSpencer.KSFullManuscriptProgramSize
import MatrixSpencer.KSEighthManuscriptPreprocess


open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSFullManuscriptExplicit
variable {N d : ℕ}

theorem labels_pos (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑i, KSRankOne.atom (v i)) = 1) : 0 < N :=
  (KSEighthManuscriptPreprocess.count_pos v hd hp).trans_le (KSEighthManuscriptPreprocess.count_le v)

theorem original_size (v : Fin N → Fin d → ℂ) (i : Fin N) :
    ‖KSRankOne.atom (v i)‖ ≤ KSEighthManuscriptPreprocess.epsilon v := by
  rw [← KSEighthManuscriptPreprocess.size_eq_norm]
  exact KSEighthManuscriptPreprocess.size_le_epsilon v i

abbrev PositiveDraws (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑i, KSRankOne.atom (v i)) = 1) (r : ℕ) :=
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  KSFullManuscriptAlgorithm.Draws v (labels_pos v hd hp)
    (KSEighthManuscriptPreprocess.epsilon_pos v hd hp) hd r

def positiveOutput (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑i, KSRankOne.atom (v i)) = 1) (r : ℕ) (z : PositiveDraws v hd hp r) : Option (Fin N → ℝ) := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  exact KSFullManuscriptAlgorithm.output v (labels_pos v hd hp)
    (KSEighthManuscriptPreprocess.epsilon_pos v hd hp) hd r z

def positiveWeight (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑i, KSRankOne.atom (v i)) = 1) (r : ℕ) (z : PositiveDraws v hd hp r) : ℝ := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  exact KSFullManuscriptAlgorithm.drawWeight v (labels_pos v hd hp)
    (KSEighthManuscriptPreprocess.epsilon_pos v hd hp) hd r z

theorem positive_output_sound (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑i, KSRankOne.atom (v i)) = 1) (r : ℕ) (z : PositiveDraws v hd hp r)
    (σ : Fin N → ℝ) (hout : positiveOutput v hd hp r z = some σ) :
    (∀i, IsSign (σ i)) ∧ ‖∑i, σ i • KSRankOne.atom (v i)‖ ≤
      9*(16*Real.sqrt 2+5)*Real.sqrt (KSEighthManuscriptPreprocess.epsilon v) := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  exact KSFullManuscriptAlgorithm.output_sound v (labels_pos v hd hp)
    (KSEighthManuscriptPreprocess.epsilon_pos v hd hp) hd r z σ hout

theorem positive_output_probability_ge (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑i, KSRankOne.atom (v i)) = 1) (r : ℕ) :
    1-((15 : ℝ)/56)^r ≤ ∑z : PositiveDraws v hd hp r,
      positiveWeight v hd hp r z * (if (positiveOutput v hd hp r z).isSome then 1 else 0) := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  exact KSFullManuscriptAlgorithm.output_event_probability_ge v (labels_pos v hd hp)
    (KSEighthManuscriptPreprocess.epsilon_pos v hd hp) hd hp (original_size v) r

/-- Dimension-zero inputs require no random sample. -/
def Draws : {d : ℕ} → (v : Fin N → Fin d → ℂ) → ((∑i, KSRankOne.atom (v i)) = 1) → ℕ → Type
  | 0, _, _, _ => PUnit
  | d+1, v, hp, r => PositiveDraws v (Nat.succ_pos d) hp r

instance drawsFintype : {d : ℕ} → (v : Fin N → Fin d → ℂ) →
    (hp : (∑i, KSRankOne.atom (v i)) = 1) → (r : ℕ) → Fintype (Draws v hp r)
  | 0, _, _, _ => inferInstanceAs (Fintype PUnit)
  | d+1, v, hp, r => inferInstanceAs (Fintype (PositiveDraws v (Nat.succ_pos d) hp r))

/-- The actual finite output on the complete original label set. -/
def output : {d : ℕ} → (v : Fin N → Fin d → ℂ) → (hp : (∑i, KSRankOne.atom (v i)) = 1) →
    (r : ℕ) → Draws v hp r → Option (Fin N → ℝ)
  | 0, _, _, _, _ => some (fun _ => 1)
  | d+1, v, hp, r, z => positiveOutput v (Nat.succ_pos d) hp r z

def drawWeight : {d : ℕ} → (v : Fin N → Fin d → ℂ) → (hp : (∑i, KSRankOne.atom (v i)) = 1) →
    (r : ℕ) → Draws v hp r → ℝ
  | 0, _, _, _, _ => 1
  | d+1, v, hp, r, z => positiveWeight v (Nat.succ_pos d) hp r z

theorem drawWeight_nonneg (v : Fin N → Fin d → ℂ) (hp : (∑i, KSRankOne.atom (v i)) = 1)
    (r : ℕ) (z : Draws v hp r) : 0 ≤ drawWeight v hp r z := by
  cases d with
  | zero => exact zero_le_one
  | succ d =>
    letI : Nonempty (Fin (d+1)) := ⟨⟨0,Nat.succ_pos d⟩⟩
    exact KSFullManuscriptAlgorithm.drawWeight_nonneg _ _ _ _ r z

theorem drawWeight_sum (v : Fin N → Fin d → ℂ) (hp : (∑i, KSRankOne.atom (v i)) = 1)
    (r : ℕ) : (∑z : Draws v hp r, drawWeight v hp r z) = 1 := by
  cases d with
  | zero => simp [Draws,drawWeight]
  | succ d =>
    letI : Nonempty (Fin (d+1)) := ⟨⟨0,Nat.succ_pos d⟩⟩
    exact KSFullManuscriptAlgorithm.drawWeight_sum _ _ _ _ r

/-- Quality with respect to the computed arithmetic maximum. -/
theorem output_sound_actual_cap (v : Fin N → Fin d → ℂ) (hp : (∑i, KSRankOne.atom (v i)) = 1)
    (r : ℕ) (z : Draws v hp r) (σ : Fin N → ℝ) (hout : output v hp r z = some σ) :
    (∀i, IsSign (σ i)) ∧ ‖∑i, σ i • KSRankOne.atom (v i)‖ ≤
      9*(16*Real.sqrt 2+5)*Real.sqrt (KSEighthManuscriptPreprocess.epsilon v) := by
  cases d with
  | zero =>
    have he : (fun _ : Fin N => (1 : ℝ)) = σ := Option.some.inj hout
    subst σ
    refine ⟨fun _ => Or.inl rfl, ?_⟩
    have hz : (∑i, (1 : ℝ) • KSRankOne.atom (v i)) = 0 := Subsingleton.elim _ _
    rw [hz,norm_zero]
    positivity
  | succ d => exact positive_output_sound v (Nat.succ_pos d) hp r z σ hout

/-- Every output is a full original signing with O(sqrt epsilon) discrepancy. -/
theorem output_sound (v : Fin N → Fin d → ℂ) (hp : (∑i, KSRankOne.atom (v i)) = 1)
    {ε : ℝ} (hε : 0 ≤ ε) (hsize : ∀i, ‖KSRankOne.atom (v i)‖ ≤ ε)
    (r : ℕ) (z : Draws v hp r) (σ : Fin N → ℝ) (hout : output v hp r z = some σ) :
    (∀i, IsSign (σ i)) ∧ ‖∑i, σ i • KSRankOne.atom (v i)‖ ≤ 9*(16*Real.sqrt 2+5)*Real.sqrt ε := by
  obtain ⟨hs,hn⟩ := output_sound_actual_cap v hp r z σ hout
  exact ⟨hs,hn.trans (mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt (KSEighthManuscriptPreprocess.epsilon_le v hε hsize)) (by positivity))⟩

/-- Actual independent finite output-event probability, in every dimension. -/
theorem output_event_probability_ge (v : Fin N → Fin d → ℂ) (hp : (∑i, KSRankOne.atom (v i)) = 1)
    (r : ℕ) : 1-((15 : ℝ)/56)^r ≤ ∑z : Draws v hp r,
      drawWeight v hp r z * (if (output v hp r z).isSome then 1 else 0) := by
  cases d with
  | zero =>
    simp only [Draws,output,drawWeight,Option.isSome_some,↓reduceIte,mul_one]
    simp only [Finset.univ_unique,Finset.sum_singleton]
    have hh : 0 ≤ ((15 : ℝ)/56)^r := by positivity
    linarith
  | succ d => exact positive_output_probability_ge v (Nat.succ_pos d) hp r

/-- Existence follows from the actual positive output probability. -/
theorem exists_full_signing (v : Fin N → Fin d → ℂ) (hp : (∑i, KSRankOne.atom (v i)) = 1)
    {ε : ℝ} (hε : 0 ≤ ε) (hsize : ∀i, ‖KSRankOne.atom (v i)‖ ≤ ε) :
    ∃σ : Fin N → ℝ, (∀i, IsSign (σ i)) ∧
      ‖∑i, σ i • KSRankOne.atom (v i)‖ ≤ 9*(16*Real.sqrt 2+5)*Real.sqrt ε := by
  classical
  have hp1 := output_event_probability_ge v hp 1
  by_contra! hn
  have hz : ∀z : Draws v hp 1, output v hp 1 z = none := by
    intro z
    cases ho : output v hp 1 z with
    | none => rfl
    | some σ =>
        have hs := output_sound v hp hε hsize 1 z σ ho
        exact False.elim ((not_lt_of_ge hs.2) (hn σ hs.1))
  simp [hz] at hp1
  norm_num at hp1

end MatrixSpencer.KSFullManuscriptExplicit
