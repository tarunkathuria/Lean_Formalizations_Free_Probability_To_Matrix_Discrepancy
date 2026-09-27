import MatrixSpencer.KSEighthManuscriptAlgorithm
import MatrixSpencer.KSEighthManuscriptPreprocess

/-!
# Primitive-input manuscript512√ε algorithm

The input is the original Parseval rank-one family. The algorithm computes
its actual maximum trace, removes zero atoms by an ordered finite scan, runs
the actual high-trace covariance/LDL-column walk and finite numerical
acceptance test, then restores every omitted label with sign+1. Independent
retries return the first accepted signing or an explicit `none`. Dimension
zero has the deterministic all-positive output. The Parseval proof is a
domain certificate used only in proofs of positive dimensions and scales.

All success and quality conclusions below are unconditional apart from the
primitive Parseval and atom-size hypotheses. They do not assert an operation
count or an extracted machine implementation.
-/

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSEighthManuscriptExplicit
variable {N d : ℕ}

abbrev PositiveDraws (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑i, KSRankOne.atom (v i)) = 1) (r : ℕ) :=
  KSEighthManuscriptAlgorithm.Draws (KSEighthManuscriptPreprocess.family v) (KSEighthManuscriptPreprocess.count_pos v hd hp) (KSEighthManuscriptPreprocess.epsilon_pos v hd hp) hd r

def positiveOutput (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑i, KSRankOne.atom (v i)) = 1) (r : ℕ) (z : PositiveDraws v hd hp r) : Option (Fin N → ℝ) :=
  (KSEighthManuscriptAlgorithm.output (KSEighthManuscriptPreprocess.family v) (KSEighthManuscriptPreprocess.count_pos v hd hp) (KSEighthManuscriptPreprocess.epsilon_pos v hd hp) hd r z).map (KSEighthManuscriptPreprocess.restore v)

def positiveWeight (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑i, KSRankOne.atom (v i)) = 1) (r : ℕ) (z : PositiveDraws v hd hp r) : ℝ :=
  KSEighthManuscriptAlgorithm.drawWeight (KSEighthManuscriptPreprocess.family v) (KSEighthManuscriptPreprocess.count_pos v hd hp) (KSEighthManuscriptPreprocess.epsilon_pos v hd hp) hd r z

theorem positive_output_sound (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑i, KSRankOne.atom (v i)) = 1) (r : ℕ) (z : PositiveDraws v hd hp r)
    (σ : Fin N → ℝ) (hout : positiveOutput v hd hp r z = some σ) :
    (∀i, IsSign (σ i)) ∧ ‖∑i, σ i • KSRankOne.atom (v i)‖ ≤ 512*Real.sqrt (KSEighthManuscriptPreprocess.epsilon v) := by
  obtain ⟨τ,ht,hσ⟩ := Option.map_eq_some_iff.mp hout
  subst σ
  have hs := KSEighthManuscriptAlgorithm.output_sound (KSEighthManuscriptPreprocess.family v) (KSEighthManuscriptPreprocess.count_pos v hd hp) (KSEighthManuscriptPreprocess.epsilon_pos v hd hp) hd r z τ ht
  exact ⟨KSEighthManuscriptPreprocess.restore_signs v hs.1, by rw [KSEighthManuscriptPreprocess.restore_sum]; exact hs.2⟩

theorem positive_output_probability_ge (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑i, KSRankOne.atom (v i)) = 1) (r : ℕ) :
    1-((1 : ℝ)/2)^r ≤ ∑z : PositiveDraws v hd hp r,
      positiveWeight v hd hp r z * (if (positiveOutput v hd hp r z).isSome then 1 else 0) := by
  simpa only [positiveOutput,positiveWeight,Option.isSome_map] using
    KSEighthManuscriptAlgorithm.output_event_probability_ge (KSEighthManuscriptPreprocess.family v) (KSEighthManuscriptPreprocess.count_pos v hd hp) (KSEighthManuscriptPreprocess.epsilon_pos v hd hp)
      (KSEighthManuscriptPreprocess.epsilon_le_one v hd hp) hd (KSEighthManuscriptPreprocess.family_parseval v hp) (KSEighthManuscriptPreprocess.family_size v) r

/-- Finite draws after actual zero removal; dimension zero needs no random draw. -/
def Draws : {d : ℕ} → (v : Fin N → Fin d → ℂ) → ((∑i, KSRankOne.atom (v i)) = 1) → ℕ → Type
  | 0, _, _, _ => PUnit
  | d+1, v, hp, r => PositiveDraws v (Nat.succ_pos d) hp r

instance drawsFintype : {d : ℕ} → (v : Fin N → Fin d → ℂ) →
    (hp : (∑i, KSRankOne.atom (v i)) = 1) → (r : ℕ) → Fintype (Draws v hp r)
  | 0, _, _, _ => inferInstanceAs (Fintype PUnit)
  | d+1, v, hp, r => inferInstanceAs (Fintype (PositiveDraws v (Nat.succ_pos d) hp r))

/-- Actual output, restoring every original zero label with+1. -/
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
  | succ d => exact KSEighthManuscriptAlgorithm.drawWeight_nonneg _ _ _ _ r z

theorem drawWeight_sum (v : Fin N → Fin d → ℂ) (hp : (∑i, KSRankOne.atom (v i)) = 1)
    (r : ℕ) : (∑z : Draws v hp r, drawWeight v hp r z) = 1 := by
  cases d with
  | zero => simp [Draws,drawWeight]
  | succ d => exact KSEighthManuscriptAlgorithm.drawWeight_sum _ _ _ _ r

/-- Input-only quality, with the algorithm's actual arithmetic maximum. -/
theorem output_sound_actual_cap (v : Fin N → Fin d → ℂ) (hp : (∑i, KSRankOne.atom (v i)) = 1)
    (r : ℕ) (z : Draws v hp r) (σ : Fin N → ℝ) (hout : output v hp r z = some σ) :
    (∀i, IsSign (σ i)) ∧ ‖∑i, σ i • KSRankOne.atom (v i)‖ ≤ 512*Real.sqrt (KSEighthManuscriptPreprocess.epsilon v) := by
  cases d with
  | zero =>
    have he : (fun _ : Fin N => (1 : ℝ)) = σ := Option.some.inj hout
    subst σ
    refine ⟨fun _ => Or.inl rfl, ?_⟩
    have hz : (∑i, (1 : ℝ) • KSRankOne.atom (v i)) = 0 := Subsingleton.elim _ _
    rw [hz,norm_zero]
    positivity
  | succ d => exact positive_output_sound v (Nat.succ_pos d) hp r z σ hout

/-- Every original label is signed and every output meets the manuscript512√ε bound. -/
theorem output_sound (v : Fin N → Fin d → ℂ) (hp : (∑i, KSRankOne.atom (v i)) = 1)
    {ε : ℝ} (hε : 0 ≤ ε) (hsize : ∀i, ‖KSRankOne.atom (v i)‖ ≤ ε)
    (r : ℕ) (z : Draws v hp r) (σ : Fin N → ℝ) (hout : output v hp r z = some σ) :
    (∀i, IsSign (σ i)) ∧ ‖∑i, σ i • KSRankOne.atom (v i)‖ ≤ 512*Real.sqrt ε := by
  obtain ⟨hs,hn⟩ := output_sound_actual_cap v hp r z σ hout
  exact ⟨hs,hn.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (KSEighthManuscriptPreprocess.epsilon_le v hε hsize)) (by norm_num))⟩

/-- Literal success-event weight for all dimensions and original label counts. -/
theorem output_event_probability_ge (v : Fin N → Fin d → ℂ) (hp : (∑i, KSRankOne.atom (v i)) = 1)
    (r : ℕ) : 1-((1 : ℝ)/2)^r ≤ ∑z : Draws v hp r,
      drawWeight v hp r z * (if (output v hp r z).isSome then 1 else 0) := by
  cases d with
  | zero =>
    simp only [Draws,output,drawWeight,Option.isSome_some,↓reduceIte,mul_one]
    simp only [Finset.univ_unique,Finset.sum_singleton]
    have hh : 0 ≤ ((1 : ℝ)/2)^r := by positivity
    linarith
  | succ d => exact positive_output_probability_ge v (Nat.succ_pos d) hp r

end MatrixSpencer.KSEighthManuscriptExplicit
