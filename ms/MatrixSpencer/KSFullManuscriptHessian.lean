import MatrixSpencer.KSFullManuscriptParameters
import MatrixSpencer.KSNumericalHessian



open Set Matrix
open scoped BigOperators Topology
noncomputable section
namespace MatrixSpencer.KSFullManuscriptHessian

open KSFullManuscriptParameters
open KSNumericalHessian (coordinate hessian Space)
variable {m N : ℕ}


def matrixReport (report : Space m → ℝ) (x : Space m) (t : ℝ) :
    Matrix (Fin m) (Fin m) ℝ := fun i j =>
  if i = j then KSFourthDifference.directionalSecond report x (coordinate i) t
  else KSFourthDifference.mixedStencil report x (coordinate i) (coordinate j) t

theorem diagonal_queries (report : Space m → ℝ) (x : Space m) (t : ℝ) (i : Fin m) :
    matrixReport report x t i i =
      (report (x + t • coordinate i) - 2 * report x + report (x - t • coordinate i)) / t ^ 2 := by
  simp [matrixReport, KSFourthDifference.directionalSecond]

theorem offDiagonal_queries (report : Space m → ℝ) (x : Space m) (t : ℝ)
    {i j : Fin m} (hij : i ≠ j) : matrixReport report x t i j =
      (report (x + t • coordinate i + t • coordinate j) -
        report (x + t • coordinate i - t • coordinate j) -
        report (x - t • coordinate i + t • coordinate j) +
        report (x - t • coordinate i - t • coordinate j)) / (4 * t ^ 2) := by
  rw [matrixReport, if_neg hij]
  exact KSFourthDifference.mixedStencil_eq_four_queries _ _ _ _ _

theorem matrixReport_isSymm (report : Space m → ℝ) (x : Space m) (t : ℝ) :
    (matrixReport report x t).IsSymm := by
  ext i j
  change matrixReport report x t j i = matrixReport report x t i j
  by_cases hij : i = j
  · subst j; rfl
  · rw [offDiagonal_queries report x t (Ne.symm hij), offDiagonal_queries report x t hij]
    have hpp : x + t • coordinate j + t • coordinate i =
        x + t • coordinate i + t • coordinate j := by abel
    have hpm : x + t • coordinate j - t • coordinate i =
        x - t • coordinate i + t • coordinate j := by abel
    have hmp : x - t • coordinate j + t • coordinate i =
        x + t • coordinate i - t • coordinate j := by abel
    have hmm : x - t • coordinate j - t • coordinate i =
        x - t • coordinate i - t • coordinate j := by abel
    rw [hpp, hpm, hmp, hmm]
    ring

/-- The factor four on mixed lines accounts for their length `sqrt 2`.
No bounds on a different normalized line are silently substituted. -/
def LineBounds (f : Space m → ℝ) (x : Space m) (t M : ℝ) : Prop :=
  (∀ i : Fin m,
    ContDiffOn ℝ 4 (fun s => f (x + s • coordinate i)) (Icc (-t) t) ∧
    ∀ s ∈ Icc (-t) t, |iteratedDeriv 4 (fun w => f (x + w • coordinate i)) s| ≤ M) ∧
  ∀ i j : Fin m, i ≠ j →
    ContDiffOn ℝ 4 (fun s => f (x + s • (coordinate i + coordinate j))) (Icc (-t) t) ∧
    ContDiffOn ℝ 4 (fun s => f (x + s • (coordinate i - coordinate j))) (Icc (-t) t) ∧
    (∀ s ∈ Icc (-t) t,
      |iteratedDeriv 4 (fun w => f (x + w • (coordinate i + coordinate j))) s| ≤ 4 * M) ∧
    (∀ s ∈ Icc (-t) t,
      |iteratedDeriv 4 (fun w => f (x + w • (coordinate i - coordinate j))) s| ≤ 4 * M)

def QueryAccuracy (f report : Space m → ℝ) (x : Space m) (t ν : ℝ) : Prop :=
  |report x - f x| ≤ ν ∧
  (∀ i : Fin m,
    |report (x + t • coordinate i) - f (x + t • coordinate i)| ≤ ν ∧
    |report (x - t • coordinate i) - f (x - t • coordinate i)| ≤ ν) ∧
  ∀ i j : Fin m, i ≠ j →
    |report (x + t • (coordinate i + coordinate j)) -
      f (x + t • (coordinate i + coordinate j))| ≤ ν ∧
    |report (x + t • (coordinate i - coordinate j)) -
      f (x + t • (coordinate i - coordinate j))| ≤ ν ∧
    |report (x - t • (coordinate i - coordinate j)) -
      f (x - t • (coordinate i - coordinate j))| ≤ ν ∧
    |report (x - t • (coordinate i + coordinate j)) -
      f (x - t • (coordinate i + coordinate j))| ≤ ν

theorem entry_error (f report : Space m → ℝ) (x : Space m)
    {t M ν : ℝ} (ht : 0 < t) (hM : 0 ≤ M) (hν : 0 ≤ ν)
    (hf : ContDiffAt ℝ 2 f x) (hline : LineBounds f x t M)
    (hquery : QueryAccuracy f report x t ν) (i j : Fin m) :
    |hessian f x i j - matrixReport report x t i j| ≤ 2 * M * t ^ 2 + 4 * ν / t ^ 2 := by
  have hMt : 0 ≤ M * t ^ 2 := mul_nonneg hM (sq_nonneg _)
  have hνt : 0 ≤ ν / t ^ 2 := div_nonneg hν (sq_nonneg _)
  by_cases hij : i = j
  · subst j
    obtain ⟨hfl, hMl⟩ := hline.1 i
    obtain ⟨hp, hm⟩ := hquery.2.1 i
    have he := KSFourthDifference.directionalSecond_error f report x (coordinate i)
      ht hf hfl hMl hp hquery.1 hm
    rw [matrixReport, if_pos rfl, abs_sub_comm]
    change |KSFourthDifference.directionalSecond report x (coordinate i) t -
      fderiv ℝ (fderiv ℝ f) x (coordinate i) (coordinate i)| ≤ _
    nlinarith
  · obtain ⟨hfp, hfm, hMp, hMm⟩ := hline.2 i j hij
    obtain ⟨hPP, hPM, hMP, hMM⟩ := hquery.2.2 i j hij
    have he := KSFourthDifference.mixedStencil_error_four_cap f report x (coordinate i)
      (coordinate j) ht hf hfp hfm hMp hMm hPP hPM hMP hMM
    rw [matrixReport, if_neg hij, abs_sub_comm]
    change |KSFourthDifference.mixedStencil report x (coordinate i) (coordinate j) t -
      fderiv ℝ (fderiv ℝ f) x (coordinate i) (coordinate j)| ≤ _
    have hnoise : 4 * ν / t ^ 2 = 4 * (ν / t ^ 2) := by ring
    rw [hnoise]
    nlinarith


theorem selected_entry_error (f report : Space m → ℝ) (x : Space m)
    (hN : 0 < N) {δ M : ℝ} (hδ : 0 < δ) (hM : 0 < M)
    (hf : ContDiffAt ℝ 2 f x)
    (hline : LineBounds f x (queryStep N δ M) M)
    (hquery : QueryAccuracy f report x (queryStep N δ M) (valueTolerance N δ M)) :
    ∀ i j, |hessian f x i j - matrixReport report x (queryStep N δ M) i j| ≤
      curvatureTolerance N δ / (2 * N) := by
  intro i j
  exact (entry_error f report x (queryStep_pos hN hδ hM) hM.le
    (valueTolerance_pos hN hδ hM).le hf hline hquery i j).trans
      (hessian_entry_budget hN hδ hM)

/-- Explicit diagonal conjugation `D^(1/2) A D^(1/2)/2`; the argument `w`
contains the real diagonal square roots. -/
def weighted (w : Fin m → ℝ) (A : Matrix (Fin m) (Fin m) ℝ) :
    Matrix (Fin m) (Fin m) ℝ := fun i j => w i * A i j * w j / 2

theorem weighted_isSymm (w : Fin m → ℝ) {A : Matrix (Fin m) (Fin m) ℝ}
    (hA : A.IsSymm) : (weighted w A).IsSymm := by
  ext i j
  have he : A j i = A i j := congrFun (congrFun hA i) j
  simp only [weighted, Matrix.transpose_apply, he]
  ring

theorem weighted_entry_error (w : Fin m → ℝ) (hw : ∀ i, |w i| ≤ 1)
    {A B : Matrix (Fin m) (Fin m) ℝ} {e : ℝ} (he : 0 ≤ e)
    (hab : ∀ i j, |A i j - B i j| ≤ e) :
    ∀ i j, |weighted w A i j - weighted w B i j| ≤ e := by
  intro i j
  have hid : weighted w A i j - weighted w B i j =
      w i * (A i j - B i j) * w j / 2 := by unfold weighted; ring
  rw [hid, abs_div, abs_mul, abs_mul]
  have hprod : |w i| * |A i j - B i j| * |w j| ≤ e := by
    calc
      _ ≤ 1 * e * 1 := mul_le_mul
        (mul_le_mul (hw i) (hab i j) (abs_nonneg _) (by norm_num)) (hw j)
        (abs_nonneg _) (by simpa using he)
      _ = e := by ring
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  linarith

/-- The Jacobi direction is computed from the unweighted stencil matrix,
followed by diagonal conjugation; no Hessian or eigenvector oracle occurs
in this definition. -/
def output (report : Space m → ℝ) (x : Space m) (w : Fin m → ℝ)
    (N : ℕ) (δ M : ℝ) (hm : 0 < m) : Space m :=
  KSJacobiRayleigh.outputVector
    (weighted w (matrixReport report x (queryStep N δ M)))
    (curvatureTolerance N δ) hm

theorem output_accuracy (f report : Space m → ℝ) (x : Space m)
    (w : Fin m → ℝ) (hw : ∀ i, |w i| ≤ 1) (hm : 0 < m) (hmN : m ≤ N)
    {δ M : ℝ} (hδ : 0 < δ) (hM : 0 < M)
    (hf : ContDiffAt ℝ 2 f x)
    (hline : LineBounds f x (queryStep N δ M) M)
    (hquery : QueryAccuracy f report x (queryStep N δ M) (valueTolerance N δ M)) :
    ‖output report x w N δ M hm‖ = 1 ∧
      KSRayleighAccuracy.realRayleigh (weighted w (hessian f x)) (output report x w N δ M hm) ≤
        KSRayleighAccuracy.leastRayleigh (weighted w (hessian f x)) +
          3 * curvatureTolerance N δ := by
  have hN : 0 < N := hm.trans_le hmN
  have hmreal : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hNreal : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hmNreal : (m : ℝ) ≤ N := by exact_mod_cast hmN
  have hκ := curvatureTolerance_pos hN hδ
  have he := weighted_entry_error w hw
    (div_nonneg hκ.le (by positivity : 0 ≤ 2 * (N : ℝ)))
    (selected_entry_error f report x hN hδ hM hf hline hquery)
  have hdim : curvatureTolerance N δ / (2 * N) ≤ curvatureTolerance N δ / m :=
    div_le_div_of_nonneg_left hκ.le hmreal (by linarith)
  have hentry : ∀ i j, |weighted w (hessian f x) i j -
      weighted w (matrixReport report x (queryStep N δ M)) i j| ≤
        curvatureTolerance N δ / m := fun i j => (he i j).trans hdim
  have hop := KSMatrixEntryAccuracy.operatorNorm_le_card_mul
    (weighted w (hessian f x) - weighted w (matrixReport report x (queryStep N δ M)))
    (div_nonneg hκ.le hmreal.le) hentry
  rw [mul_div_cancel₀ _ (ne_of_gt hmreal)] at hop
  exact KSJacobiRayleigh.outputVector_accuracy_of_matrix_error _ _
    (weighted_isSymm w (matrixReport_isSymm report x _)) hκ hm hop

end MatrixSpencer.KSFullManuscriptHessian
