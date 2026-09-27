import MatrixSpencer.KSEighthManuscriptQuality



open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSEighthManuscriptAcceptance
open KSEighthManuscriptRun KSEighthManuscriptParameters
attribute [local instance] Classical.propDecidable
variable {N d : ℕ}

def potential (v : Fin N → Fin d → ℂ) (θ : ℝ) (x : Fin N → ℝ) : ℝ :=
  KSPotentialModels.eighthPotential (fun i => KSRankOne.atom (v i)) θ x

def accepts (v : Fin N → Fin d → ℂ) (δ θ : ℝ) (hd : 0 < d)
    (C : Controller N) (s : State C) : Bool :=
  (List.finRange N).all (fun i => decide (s.coeff i = -(1/8 : ℝ)) || decide (s.coeff i = (1/8 : ℝ))) &&
    decide (KSEighthNumericalValue.stateReport v θ hd (δ/4) s.coeff ≤ 63*δ)

theorem accepts_iff (v : Fin N → Fin d → ℂ) (δ θ : ℝ) (hd : 0 < d)
    (C : Controller N) (s : State C) :
    accepts v δ θ hd C s = true ↔ KSEighthWalkRun.terminal s ∧
      KSEighthNumericalValue.stateReport v θ hd (δ/4) s.coeff ≤ 63*δ := by
  simp [accepts,List.all_eq_true,KSEighthWalkRun.terminal,ksVertex]

theorem potential_nonneg (v : Fin N → Fin d → ℂ) {θ : ℝ} (hθ : 0 < θ) (hd : 0 < d)
    (C : Controller N) (s : State C) : 0 ≤ potential v θ s.coeff := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  exact (norm_nonneg _).trans (KSFinalAssembly.norm_le_eighthPotential _
    (fun i => KSRankOne.atom_isHermitian (v i)) hθ.le s.cube)

theorem accepts_sound (v : Fin N → Fin d → ℂ) {δ θ : ℝ} (hδ : 0 < δ) (hθ : 0 < θ)
    (hd : 0 < d) (C : Controller N) (s : State C) (ha : accepts v δ θ hd C s = true) :
    KSEighthWalkRun.terminal s ∧ potential v θ s.coeff ≤ 64*δ := by
  obtain ⟨ht,hr⟩ := (accepts_iff v δ θ hd C s).mp ha
  have he := KSEighthNumericalValue.stateReport_accuracy v hθ (by positivity : 0 < δ/4) hd s.cube
  exact ⟨ht,by dsimp only [potential]; linarith [(abs_le.mp he).1]⟩

theorem good_accepted (v : Fin N → Fin d → ℂ) {δ θ : ℝ} (hδ : 0 < δ) (hθ : 0 < θ)
    (hd : 0 < d) (C : Controller N) (s : State C) (ht : KSEighthWalkRun.terminal s)
    (hf : potential v θ s.coeff ≤ 62*δ) : accepts v δ θ hd C s = true := by
  apply (accepts_iff v δ θ hd C s).mpr
  have he := KSEighthNumericalValue.stateReport_accuracy v hθ (by positivity : 0 < δ/4) hd s.cube
  exact ⟨ht,by dsimp only [potential] at hf; linarith [(abs_le.mp he).2]⟩

/-- This finite Bool test is the only acceptance gate; no exact matrix norm is queried. -/
def output (v : Fin N → Fin d → ℂ) (δ θ : ℝ) (hd : 0 < d)
    (C : Controller N) (s : State C) : Option (Fin N → ℝ) :=
  if accepts v δ θ hd C s then some (KSEighthWalkRun.signing s) else none

theorem output_isSome (v : Fin N → Fin d → ℂ) (δ θ : ℝ) (hd : 0 < d)
    (C : Controller N) (s : State C) : (output v δ θ hd C s).isSome = accepts v δ θ hd C s := by
  simp only [output]
  split <;> simp_all

theorem output_sound (v : Fin N → Fin d → ℂ) {δ θ : ℝ} (hδ : 0 < δ) (hθ : 0 < θ)
    (hd : 0 < d) (C : Controller N) (s : State C) (σ : Fin N → ℝ)
    (hout : output v δ θ hd C s = some σ) :
    (∀i, IsSign (σ i)) ∧ ‖∑i, σ i • KSRankOne.atom (v i)‖ ≤ 512*δ := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  unfold output at hout
  split at hout
  next ha =>
    obtain rfl := Option.some.inj hout
    obtain ⟨ht,hf⟩ := accepts_sound v hδ hθ hd C s ha
    refine ⟨KSEighthWalkRun.terminal_full_signing s ht, ?_⟩
    have hn := KSFinalAssembly.norm_le_eighthPotential (fun i => KSRankOne.atom (v i))
      (fun i => KSRankOne.atom_isHermitian (v i)) hθ.le s.cube
    have he : (∑i, KSEighthWalkRun.signing s i • KSRankOne.atom (v i)) =
        (8 : ℝ) • KSPotentialModels.center (fun i => KSRankOne.atom (v i)) s.coeff := by
      simp only [KSEighthWalkRun.signing,KSPotentialModels.center,Finset.smul_sum,smul_smul]
    rw [he,norm_smul,Real.norm_eq_abs]
    norm_num
    dsimp only [potential] at hf
    linarith
  next h => simp at hout

def probability (v : Fin N → Fin d → ℂ) (δ θ : ℝ) (hd : 0 < d)
    (C : Controller N) (T : ℕ) (s : State C) : ℝ :=
  (run C T s).expectation (fun q => if accepts v δ θ hd C q then 1 else 0)

/-- A literal finite-weight union/Markov estimate, including nonterminal cutoff leaves. -/
theorem one_le_probability_add (v : Fin N → Fin d → ℂ) {δ θ : ℝ} (hδ : 0 < δ) (hθ : 0 < θ)
    (hd : 0 < d) (C : Controller N) (T : ℕ) (s : State C) :
    1 ≤ probability v δ θ hd C T s + cutoffProbability C T s +
      (run C T s).expectation (fun q => potential v θ q.coeff)/(62*δ) := by
  have hden : 0 < 62*δ := by positivity
  have hp (q : State C) : (1 : ℝ) ≤ (if accepts v δ θ hd C q then 1 else 0) +
      KSStoppedProgress.activeIndicator KSEighthWalkRun.terminal q + potential v θ q.coeff/(62*δ) := by
    have hn := div_nonneg (potential_nonneg v hθ hd C q) hden.le
    by_cases ht : KSEighthWalkRun.terminal q
    · by_cases ha : accepts v δ θ hd C q = true
      · simp only [ha,↓reduceIte,KSStoppedProgress.activeIndicator,ht,add_zero]
        linarith
      · have hbad : 62*δ < potential v θ q.coeff := by
          by_contra hb
          exact ha (good_accepted v hδ hθ hd C q ht (le_of_not_gt hb))
        have hh := (one_le_div hden).mpr hbad.le
        simp only [ha,Bool.false_eq_true,↓reduceIte,KSStoppedProgress.activeIndicator,ht,zero_add]
        exact hh
    · simp only [KSStoppedProgress.activeIndicator,ht,↓reduceIte]
      split_ifs <;> linarith
  calc
    1 = ∑l : (run C T s).Leaves, (run C T s).leafWeight l * 1 := by
      simp only [mul_one,(run C T s).leafWeight_sum]
    _ ≤ ∑l : (run C T s).Leaves, (run C T s).leafWeight l *
        ((if accepts v δ θ hd C ((run C T s).leafState l) then 1 else 0) +
          KSStoppedProgress.activeIndicator KSEighthWalkRun.terminal ((run C T s).leafState l) +
          potential v θ ((run C T s).leafState l).coeff/(62*δ)) :=
      Finset.sum_le_sum (fun l _ => mul_le_mul_of_nonneg_left (hp _) ((run C T s).leafWeight_pos l).le)
    _ = _ := by
      simp only [mul_add,Finset.sum_add_distrib,←mul_div_assoc,←Finset.sum_div,
        probability,cutoffProbability,KSEighthManuscriptBranchingRun.activeProbability,
        KSEighthManuscriptBranchingRun.expectation,FiniteBranchingTermination.Tree.expectation,run]


theorem probability_ge_half (v : Fin N → Fin d → ℂ) {ε : ℝ}
    (hN : 0 < N) (hε : 0 < ε) (hε1 : ε ≤ 1) (hd : 0 < d)
    (hparseval : (∑i, KSRankOne.atom (v i)) = 1)
    (hsize : ∀i, ‖KSRankOne.atom (v i)‖ ≤ ε) :
    let hδ := Real.sqrt_pos.mpr hε
    let hθ := @ksRegularizerScale_pos (Fin d) _ _ ⟨⟨0,hd⟩⟩ ε hε
    let C := controller v hN hδ hθ hd
    (1 : ℝ)/2 ≤ probability v (Real.sqrt ε) (ksRegularizerScale ε (Fin d)) hd C
      (KSEighthManuscriptBudgets.cutoff v (Real.sqrt ε) (ksRegularizerScale ε (Fin d))) (initialState C) := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  have hδ := Real.sqrt_pos.mpr hε
  have hθ : 0 < ksRegularizerScale ε (Fin d) := ksRegularizerScale_pos hε
  let C := controller v hN hδ hθ hd
  let T := KSEighthManuscriptBudgets.cutoff v (Real.sqrt ε) (ksRegularizerScale ε (Fin d))
  have hmean := KSEighthManuscriptQuality.expected_potential_le_nineteen v hN hε hε1 hd hparseval hsize T
  have hcut := KSEighthManuscriptBudgets.cutoff_probability v hN hδ hθ hd (initialState C)
  have hu := one_le_probability_add v hδ hθ hd C T (initialState C)
  have hdiv := div_le_div_of_nonneg_right hmean (by positivity : 0 ≤ 62*Real.sqrt ε)
  have he : 19*Real.sqrt ε/(62*Real.sqrt ε) = (19 : ℝ)/62 := by field_simp [hδ.ne']
  rw [he] at hdiv
  dsimp only at hdiv hcut ⊢
  change _ ≤ _ at hu
  dsimp only [potential] at hu
  change cutoffProbability C T (initialState C) ≤ (1 : ℝ)/100 at hcut
  change (run C T (initialState C)).expectation _ / (62*Real.sqrt ε) ≤ (19 : ℝ)/62 at hdiv
  linarith

end MatrixSpencer.KSEighthManuscriptAcceptance
