import MatrixSpencer.KSFullManuscriptParameters
import MatrixSpencer.KSDebitWalkAcceptance



open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSFullManuscriptAcceptance

open KSDebitWalkRun KSFullManuscriptParameters
variable {N d : ℕ}

/-- A finite diagonal scan after real Jacobi rotations. No exact matrix norm
is evaluated by this definition. -/
def normReport (A : Matrix (Fin d) (Fin d) ℂ) (δ : ℝ) : ℝ :=
  KSJacobiNorm.maxAbsDiagonal
    (KSJacobiRayleigh.finalMatrix (KSComplexTraceSqrt.realificationFin A) (δ / 4))

theorem normReport_le_norm (A : Matrix (Fin d) (Fin d) ℂ) (δ : ℝ) :
    normReport A δ ≤ ‖A‖ := by
  have h := KSJacobiNorm.maxAbsDiagonal_le_norm
    (KSJacobiRayleigh.finalMatrix (KSComplexTraceSqrt.realificationFin A) (δ / 4))
  simpa only [normReport, KSJacobiNorm.finalMatrix_norm,
    KSComplexNorm.realificationFin_norm] using h

theorem normReport_accuracy (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian)
    {δ : ℝ} (hδ : 0 < δ) : |normReport A δ - ‖A‖| ≤ δ / 4 := by
  have h := (KSComplexNorm.report_accuracy A hA (ν := δ / 4)
    (div_pos hδ (by norm_num))).1
  change ‖A‖ ≤ normReport A δ + δ / 4 at h
  exact abs_le.mpr ⟨by linarith, by linarith [normReport_le_norm A δ]⟩

variable [Nonempty (Fin d)]


def accepts (C : Controller N (Fin d)) (s : State C) : Bool :=
  (List.finRange N).all (fun i => decide (s.coeff i = 1) || decide (s.coeff i = -1)) &&
    decide (normReport (KSDebitWalkAcceptance.signedMatrix C s) C.δ ≤
      8 * signingScale * C.δ)

theorem accepts_iff (C : Controller N (Fin d)) (s : State C) :
    accepts C s = true ↔ (∀ i, IsSign (s.coeff i)) ∧
      normReport (KSDebitWalkAcceptance.signedMatrix C s) C.δ ≤
        8 * signingScale * C.δ := by
  simp [accepts, List.all_eq_true, IsSign]

theorem accepts_sound (C : Controller N (Fin d)) (s : State C)
    (haccept : accepts C s = true) :
    (∀ i, IsSign (s.coeff i)) ∧
      ‖KSDebitWalkAcceptance.signedMatrix C s‖ ≤ 8 * signingScale * C.δ + C.δ / 4 := by
  obtain ⟨hs, hr⟩ := (accepts_iff C s).mp haccept
  have ha := (abs_le.mp (normReport_accuracy _
    (KSDebitWalkAcceptance.signedMatrix_isHermitian C s) C.δ_pos)).1
  exact ⟨hs, by linarith⟩

theorem accepts_norm_lt_nine (C : Controller N (Fin d)) (s : State C)
    (haccept : accepts C s = true) :
    ‖KSDebitWalkAcceptance.signedMatrix C s‖ < 9 * signingScale * C.δ := by
  have hs := (accepts_sound C s haccept).2
  have hscale := mul_le_mul_of_nonneg_right signingScale_ge_one C.δ_pos.le
  nlinarith [C.δ_pos]

theorem seven_accepted (C : Controller N (Fin d)) (s : State C)
    (hs : ∀ i, IsSign (s.coeff i))
    (hn : ‖KSDebitWalkAcceptance.signedMatrix C s‖ ≤ 7 * signingScale * C.δ) :
    accepts C s = true := by
  apply (accepts_iff C s).mpr
  refine ⟨hs, (normReport_le_norm _ _).trans (hn.trans ?_)⟩
  have hscale := mul_le_mul_of_nonneg_right signingScale_ge_one C.δ_pos.le
  nlinarith [C.δ_pos]

def acceptanceProbability (C : Controller N (Fin d)) (T : ℕ) (s : State C) : ℝ :=
  (run C T s).expectation (fun z => if accepts C z then 1 else 0)

theorem successProbability_le_acceptanceProbability (C : Controller N (Fin d))
    (T : ℕ) (s : State C) :
    KSDebitWalkQuality.successProbability C T s (7 * signingScale * C.δ) ≤
      acceptanceProbability C T s := by
  classical
  unfold KSDebitWalkQuality.successProbability acceptanceProbability
    FiniteBranchingTermination.Tree.expectation
  apply Finset.sum_le_sum
  intro l _
  apply mul_le_mul_of_nonneg_left _ ((run C T s).leafWeight_pos l).le
  dsimp only
  by_cases hs : KSDebitWalkQuality.successful C (7 * signingScale * C.δ)
      ((run C T s).leafState l)
  · have ha := seven_accepted C ((run C T s).leafState l) hs.1 hs.2
    simp only [if_pos hs, ha, ↓reduceIte, le_refl]
  · simp only [if_neg hs]
    split_ifs <;> norm_num


theorem acceptanceProbability_from_zero_ge (C : Controller N (Fin d))
    (hparseval : (∑ i, KSRankOne.atom (C.vectors i)) = 1)
    (hηbudget : (N : ℝ) * C.η ≤ C.δ) {ε β : ℝ} (hεpos : 0 < ε)
    (hε : ∀ i, ‖KSRankOne.atom (C.vectors i)‖ ≤ ε)
    (hθ : C.θ = ksRegularizerScale ε (Fin d)) (hδ : C.δ = Real.sqrt ε)
    (hβ : 0 ≤ β) (hdrift : KSDebitWalkQuality.LocalPotentialDrift C β)
    (hdriftBudget : β * ((N : ℝ) * (2 * Real.log 2)) ≤ C.δ)
    (T : ℕ) (hT : 0 < T)
    (htime : ((N : ℝ) * (2 * Real.log 2)) / (C.stepSize ^ 2 * (T : ℝ)) ≤ 1 / 8) :
    (41 : ℝ) / 56 ≤ acceptanceProbability C T (initialState C) := by
  exact (KSDebitWalkQuality.successProbability_from_zero_ge C hparseval hηbudget
    hεpos hε hθ hδ hβ hdrift hdriftBudget T hT htime).trans
      (successProbability_le_acceptanceProbability C T (initialState C))

end MatrixSpencer.KSFullManuscriptAcceptance
