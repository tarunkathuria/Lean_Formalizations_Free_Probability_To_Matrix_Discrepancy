import MatrixSpencer.KSEighthInputParameters
import MatrixSpencer.KSComplexNorm

/-! Finite, numerical acceptance and its actual eighth-walk probability. -/

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSEighthAcceptance
open KSEighthWalkRun KSEighthInputParameters
attribute [local instance] Classical.propDecidable
variable {N d : ℕ}

def matrix (v : Fin N → Fin d → ℂ) (x : Fin N → ℝ) : Matrix (Fin d) (Fin d) ℂ :=
  KSPotentialModels.center (fun i => KSRankOne.atom (v i)) x

theorem matrix_hermitian (v : Fin N → Fin d → ℂ) (x : Fin N → ℝ) : (matrix v x).IsHermitian :=
  KSPotentialModels.center_isHermitian _ (fun i => KSRankOne.atom_isHermitian (v i)) x

/-- The output test uses the actual finite Jacobi upper norm report. -/
def accepts (v : Fin N → Fin d → ℂ) (ε : ℝ) (C : Controller N) (s : State C) : Bool :=
  (List.finRange N).all (fun i => decide (s.coeff i = -(1/8 : ℝ)) || decide (s.coeff i = (1/8 : ℝ))) &&
    KSComplexNorm.accepts (matrix v s.coeff) (delta ε) (256*delta ε)

theorem accepts_iff (v : Fin N → Fin d → ℂ) (ε : ℝ) (C : Controller N) (s : State C) :
    accepts v ε C s = true ↔ terminal s ∧ KSComplexNorm.report (matrix v s.coeff) (delta ε) ≤ 256*delta ε := by
  simp [accepts, List.all_eq_true, terminal, ksVertex, KSComplexNorm.accepts]

theorem accepts_sound (v : Fin N → Fin d → ℂ) {ε : ℝ} (hε : 0 < ε)
    (C : Controller N) (s : State C) (ha : accepts v ε C s = true) :
    terminal s ∧ ‖matrix v s.coeff‖ ≤ 256*delta ε := by
  obtain ⟨ht,hn⟩ := (accepts_iff v ε C s).mp ha
  exact ⟨ht, KSComplexNorm.accepted_norm_le _ (matrix_hermitian v _) (delta_pos hε) hn⟩

theorem good_accepted (v : Fin N → Fin d → ℂ) {ε : ℝ} (hε : 0 < ε)
    (C : Controller N) (s : State C) (ht : terminal s) (hn : ‖matrix v s.coeff‖ ≤ 255*delta ε) :
    accepts v ε C s = true := by
  apply (accepts_iff v ε C s).mpr
  exact ⟨ht, KSComplexNorm.good_norm_accepted _ (matrix_hermitian v _) (delta_pos hε) hn (by ring_nf; exact le_rfl)⟩

def probability (v : Fin N → Fin d → ℂ) (ε : ℝ) (C : Controller N) (T : ℕ) (s : State C) : ℝ :=
  (run C T s).expectation (fun q => if accepts v ε C q then 1 else 0)

/-- A finite union/Markov bound on the actual coin leaves. -/
theorem one_le_probability_add (v : Fin N → Fin d → ℂ) {ε : ℝ} (hε : 0 < ε)
    (C : Controller N) (T : ℕ) (s : State C) :
    1 ≤ probability v ε C T s + cutoffProbability C T s +
      (run C T s).expectation (fun q => ‖matrix v q.coeff‖)/(255*delta ε) := by
  have hδ := delta_pos hε
  have hden : 0 < 255*delta ε := by positivity
  have hp (q : State C) : (1 : ℝ) ≤ (if accepts v ε C q then 1 else 0) +
      KSStoppedProgress.activeIndicator terminal q + ‖matrix v q.coeff‖/(255*delta ε) := by
    have hn : 0 ≤ ‖matrix v q.coeff‖/(255*delta ε) := div_nonneg (norm_nonneg _) hden.le
    by_cases ht : terminal q
    · by_cases ha : accepts v ε C q = true
      · simp only [ha, ↓reduceIte, KSStoppedProgress.activeIndicator, ht, add_zero]
        linarith
      · have hbad : 255*delta ε < ‖matrix v q.coeff‖ := by
          by_contra hb
          exact ha (good_accepted v hε C q ht (le_of_not_gt hb))
        have hd := (one_le_div hden).mpr hbad.le
        simp only [ha, Bool.false_eq_true, ↓reduceIte, KSStoppedProgress.activeIndicator, ht, zero_add]
        exact hd
    · simp only [KSStoppedProgress.activeIndicator, ht, ↓reduceIte]
      split_ifs <;> linarith
  calc
    1 = ∑ l : (run C T s).Leaves, (run C T s).leafWeight l * 1 := by
      simp only [mul_one, (run C T s).leafWeight_sum]
    _ ≤ ∑ l : (run C T s).Leaves, (run C T s).leafWeight l *
        ((if accepts v ε C ((run C T s).leafState l) then 1 else 0) +
          KSStoppedProgress.activeIndicator terminal ((run C T s).leafState l) +
          ‖matrix v ((run C T s).leafState l).coeff‖/(255*delta ε)) :=
      Finset.sum_le_sum (fun l _ => mul_le_mul_of_nonneg_left (hp _)
        ((run C T s).leafWeight_pos l).le)
    _ = _ := by
      simp only [mul_add, Finset.sum_add_distrib, ← mul_div_assoc, ← Finset.sum_div,
        probability, cutoffProbability, KSFiniteCoinRun.activeProbability, KSFiniteCoinRun.expectation,
        FiniteBranchingTermination.Tree.expectation, run]

/-- At least three quarters of actual finite eighth-walk trials are accepted. -/
theorem probability_ge (v : Fin N → Fin d → ℂ) {ε : ℝ} (hε : 0 < ε) (hd : 0 < d)
    (hparseval : (∑ i, KSRankOne.atom (v i)) = 1)
    (hsize : ∀ i, ‖KSRankOne.atom (v i)‖ ≤ ε) :
    let C := controller v hε hd
    (3 : ℝ)/4 ≤ probability v ε C (cutoff v hε hd) (initialState C) := by
  have hδ := delta_pos hε
  have hmean := KSEighthInputParameters.expected_norm_le v hε hd hparseval hsize (cutoff v hε hd)
  have hcut := cutoff_probability_le v hε hd
  have hu := one_le_probability_add v hε (controller v hε hd) (cutoff v hε hd) (initialState (controller v hε hd))
  have hdiv := div_le_div_of_nonneg_right hmean (by positivity : 0 ≤ 255*delta ε)
  have he : 19*delta ε/(255*delta ε) = (19 : ℝ)/255 := by field_simp [hδ.ne']
  rw [he] at hdiv
  dsimp only at hcut hmean ⊢
  change _ ≤ _ at hu
  dsimp only [matrix] at hu
  linarith

/-- Rescaling the returned eighth vertex produces genuine original-label signs. -/
theorem accepted_signing_sound (v : Fin N → Fin d → ℂ) {ε : ℝ} (hε : 0 < ε)
    (C : Controller N) (s : State C) (ha : accepts v ε C s = true) :
    (∀ i, IsSign (signing s i)) ∧ ‖∑ i, signing s i • KSRankOne.atom (v i)‖ ≤ 2048*Real.sqrt ε := by
  obtain ⟨ht,hn⟩ := accepts_sound v hε C s ha
  refine ⟨terminal_full_signing s ht, ?_⟩
  have he : (∑ i, signing s i • KSRankOne.atom (v i)) = (8 : ℝ) • matrix v s.coeff := by
    simp only [signing, matrix, KSPotentialModels.center, Finset.smul_sum, smul_smul]
  rw [he, norm_smul, Real.norm_eq_abs]
  norm_num
  dsimp only [delta] at hn
  linarith

end MatrixSpencer.KSEighthAcceptance
