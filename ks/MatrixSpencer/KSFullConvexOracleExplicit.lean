import MatrixSpencer.KSFullConvexOracleAlgorithm
import MatrixSpencer.KSFullManuscriptProgramSize
import MatrixSpencer.KSEighthManuscriptPreprocess

/-!
# Original-input full-cube signing with the permitted convex solver

The defined computation uses the actual maximum atom size and retains every
original label. Zero physical dimension returns the all-positive signing.
For positive dimension the convex-program solver contract is the sole
supplied correctness assumption; all walk accuracy, derivatives, drift,
finite completion and actual output probabilities are proved internally.

-/
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSFullConvexOracleExplicit
variable {N d : ℕ}

theorem labels_pos (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑i, KSRankOne.atom (v i)) = 1) : 0 < N :=
  (KSEighthManuscriptPreprocess.count_pos v hd hp).trans_le (KSEighthManuscriptPreprocess.count_le v)

theorem original_size (v : Fin N → Fin d → ℂ) (i : Fin N) :
    ‖KSRankOne.atom (v i)‖ ≤ KSEighthManuscriptPreprocess.epsilon v := by
  rw [← KSEighthManuscriptPreprocess.size_eq_norm]
  exact KSEighthManuscriptPreprocess.size_le_epsilon v i

abbrev PositiveDraws (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑i, KSRankOne.atom (v i)) = 1) (r : ℕ) :=
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  KSFullConvexOracleAlgorithm.Draws O v (labels_pos v hd hp)
    (KSEighthManuscriptPreprocess.epsilon_pos v hd hp) hd r

def positiveOutput (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑i, KSRankOne.atom (v i)) = 1) (r : ℕ) (z : PositiveDraws O v hd hp r) : Option (Fin N → ℝ) := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  exact KSFullConvexOracleAlgorithm.output O v (labels_pos v hd hp)
    (KSEighthManuscriptPreprocess.epsilon_pos v hd hp) hd r z

def positiveWeight (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑i, KSRankOne.atom (v i)) = 1) (r : ℕ) (z : PositiveDraws O v hd hp r) : ℝ := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  exact KSFullConvexOracleAlgorithm.drawWeight O v (labels_pos v hd hp)
    (KSEighthManuscriptPreprocess.epsilon_pos v hd hp) hd r z

theorem positive_output_sound (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑i, KSRankOne.atom (v i)) = 1) (r : ℕ) (z : PositiveDraws O v hd hp r)
    (σ : Fin N → ℝ) (hout : positiveOutput O v hd hp r z = some σ) :
    (∀i, IsSign (σ i)) ∧ ‖∑i, σ i • KSRankOne.atom (v i)‖ ≤
      9*(16*Real.sqrt 2+5)*Real.sqrt (KSEighthManuscriptPreprocess.epsilon v) := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  exact KSFullConvexOracleAlgorithm.output_sound O v (labels_pos v hd hp)
    (KSEighthManuscriptPreprocess.epsilon_pos v hd hp) hd r z σ hout

theorem positive_output_probability_ge (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑i, KSRankOne.atom (v i)) = 1) (r : ℕ) :
    1-((15 : ℝ)/56)^r ≤ ∑z : PositiveDraws O v hd hp r,
      positiveWeight O v hd hp r z * (if (positiveOutput O v hd hp r z).isSome then 1 else 0) := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  exact KSFullConvexOracleAlgorithm.output_event_probability_ge O v (labels_pos v hd hp)
    (KSEighthManuscriptPreprocess.epsilon_pos v hd hp) hd hp (original_size v) r

/-- Dimension-zero inputs require no random sample. -/
def Draws (O : KSConvexValueOracle.Solver) : {d : ℕ} → (v : Fin N → Fin d → ℂ) → ((∑i, KSRankOne.atom (v i)) = 1) → ℕ → Type
  | 0, _, _, _ => PUnit
  | d+1, v, hp, r => PositiveDraws O v (Nat.succ_pos d) hp r

instance drawsFintype (O : KSConvexValueOracle.Solver) : {d : ℕ} → (v : Fin N → Fin d → ℂ) →
    (hp : (∑i, KSRankOne.atom (v i)) = 1) → (r : ℕ) → Fintype (Draws O v hp r)
  | 0, _, _, _ => inferInstanceAs (Fintype PUnit)
  | d+1, v, hp, r => inferInstanceAs (Fintype (PositiveDraws O v (Nat.succ_pos d) hp r))

/-- The actual finite output O on the complete original label set. -/
def output (O : KSConvexValueOracle.Solver) : {d : ℕ} → (v : Fin N → Fin d → ℂ) → (hp : (∑i, KSRankOne.atom (v i)) = 1) →
    (r : ℕ) → Draws O v hp r → Option (Fin N → ℝ)
  | 0, _, _, _, _ => some (fun _ => 1)
  | d+1, v, hp, r, z => positiveOutput O v (Nat.succ_pos d) hp r z

def drawWeight (O : KSConvexValueOracle.Solver) : {d : ℕ} → (v : Fin N → Fin d → ℂ) → (hp : (∑i, KSRankOne.atom (v i)) = 1) →
    (r : ℕ) → Draws O v hp r → ℝ
  | 0, _, _, _, _ => 1
  | d+1, v, hp, r, z => positiveWeight O v (Nat.succ_pos d) hp r z

theorem drawWeight_nonneg (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ) (hp : (∑i, KSRankOne.atom (v i)) = 1)
    (r : ℕ) (z : Draws O v hp r) : 0 ≤ drawWeight O v hp r z := by
  cases d with
  | zero => exact zero_le_one
  | succ d =>
    letI : Nonempty (Fin (d+1)) := ⟨⟨0,Nat.succ_pos d⟩⟩
    exact KSFullConvexOracleAlgorithm.drawWeight_nonneg O _ _ _ _ r z

theorem drawWeight_sum (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ) (hp : (∑i, KSRankOne.atom (v i)) = 1)
    (r : ℕ) : (∑z : Draws O v hp r, drawWeight O v hp r z) = 1 := by
  cases d with
  | zero => simp [Draws,drawWeight]
  | succ d =>
    letI : Nonempty (Fin (d+1)) := ⟨⟨0,Nat.succ_pos d⟩⟩
    exact KSFullConvexOracleAlgorithm.drawWeight_sum O _ _ _ _ r

/-- Quality with respect to the computed arithmetic maximum. -/
theorem output_sound_actual_cap (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ) (hp : (∑i, KSRankOne.atom (v i)) = 1)
    (r : ℕ) (z : Draws O v hp r) (σ : Fin N → ℝ) (hout : output O v hp r z = some σ) :
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
  | succ d => exact positive_output_sound O v (Nat.succ_pos d) hp r z σ hout

/-- Every output O is a full original signing with O(sqrt epsilon) discrepancy. -/
theorem output_sound (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ) (hp : (∑i, KSRankOne.atom (v i)) = 1)
    {ε : ℝ} (hε : 0 ≤ ε) (hsize : ∀i, ‖KSRankOne.atom (v i)‖ ≤ ε)
    (r : ℕ) (z : Draws O v hp r) (σ : Fin N → ℝ) (hout : output O v hp r z = some σ) :
    (∀i, IsSign (σ i)) ∧ ‖∑i, σ i • KSRankOne.atom (v i)‖ ≤ 9*(16*Real.sqrt 2+5)*Real.sqrt ε := by
  obtain ⟨hs,hn⟩ := output_sound_actual_cap O v hp r z σ hout
  exact ⟨hs,hn.trans (mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt (KSEighthManuscriptPreprocess.epsilon_le v hε hsize)) (by positivity))⟩

/-- Actual independent finite output O-event probability, in every dimension. -/
theorem output_event_probability_ge (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ) (hp : (∑i, KSRankOne.atom (v i)) = 1)
    (r : ℕ) : 1-((15 : ℝ)/56)^r ≤ ∑z : Draws O v hp r,
      drawWeight O v hp r z * (if (output O v hp r z).isSome then 1 else 0) := by
  cases d with
  | zero =>
    simp only [Draws,output,drawWeight,Option.isSome_some,↓reduceIte,mul_one]
    simp only [Finset.univ_unique,Finset.sum_singleton]
    have hh : 0 ≤ ((15 : ℝ)/56)^r := by positivity
    linarith
  | succ d => exact positive_output_probability_ge O v (Nat.succ_pos d) hp r

/-- Existence follows from the actual positive output O probability. -/
theorem exists_full_signing (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ) (hp : (∑i, KSRankOne.atom (v i)) = 1)
    {ε : ℝ} (hε : 0 ≤ ε) (hsize : ∀i, ‖KSRankOne.atom (v i)‖ ≤ ε) :
    ∃σ : Fin N → ℝ, (∀i, IsSign (σ i)) ∧
      ‖∑i, σ i • KSRankOne.atom (v i)‖ ≤ 9*(16*Real.sqrt 2+5)*Real.sqrt ε := by
  classical
  have hp1 := output_event_probability_ge O v hp 1
  by_contra! hn
  have hz : ∀z : Draws O v hp 1, output O v hp 1 z = none := by
    intro z
    cases ho : output O v hp 1 z with
    | none => rfl
    | some σ =>
        have hs := output_sound O v hp hε hsize 1 z σ ho
        exact False.elim ((not_lt_of_ge hs.2) (hn σ hs.1))
  simp [hz] at hp1
  norm_num at hp1

end MatrixSpencer.KSFullConvexOracleExplicit
