import HigherRankKSRuntime.ThirdDifference
import MatrixSpencer.KSFullManuscriptHessian

/-! The actual three-point diagonal and four-point mixed Hessian queries,
with the new third-derivative error budget. No Hessian oracle is used. -/

open Matrix Set
open scoped BigOperators Topology Matrix.Norms.L2Operator
noncomputable section
namespace HigherRankKSRuntime.NumericHessian
open MatrixSpencer
open KSNumericalHessian (Space coordinate hessian)
open KSFullManuscriptHessian (matrixReport QueryAccuracy)
variable {m : ℕ}

/-- A bound on the third derivative along each actual query line. The
factor eight allows `||e_i ± e_j||<=2` without silently using a unit
direction bound on an unnormalized line. -/
def LineBounds (f : Space m → ℝ) (x : Space m) (t M : ℝ) : Prop :=
  (∀ i : Fin m,
    ContDiffOn ℝ 3 (fun s => f (x + s • coordinate i)) (Icc (-t) t) ∧
    ∀ s ∈ Icc (-t) t, |iteratedDeriv 3 (fun w => f (x + w • coordinate i)) s| ≤ M) ∧
  ∀ i j : Fin m, i ≠ j →
    ContDiffOn ℝ 3 (fun s => f (x + s • (coordinate i + coordinate j))) (Icc (-t) t) ∧
    ContDiffOn ℝ 3 (fun s => f (x + s • (coordinate i - coordinate j))) (Icc (-t) t) ∧
    (∀ s ∈ Icc (-t) t,
      |iteratedDeriv 3 (fun w => f (x + w • (coordinate i + coordinate j))) s| ≤ 8 * M) ∧
    (∀ s ∈ Icc (-t) t,
      |iteratedDeriv 3 (fun w => f (x + w • (coordinate i - coordinate j))) s| ≤ 8 * M)

theorem entry_error (f report : Space m → ℝ) (x : Space m)
    {t M ν : ℝ} (ht : 0 < t) (hM : 0 ≤ M) (hν : 0 ≤ ν)
    (hf : ContDiffAt ℝ 2 f x) (hline : LineBounds f x t M)
    (hquery : QueryAccuracy f report x t ν) (i j : Fin m) :
    |hessian f x i j - matrixReport report x t i j| ≤ 2 * M * t + 4 * ν / t ^ 2 := by
  have hMt : 0 ≤ M * t := mul_nonneg hM ht.le
  have hνt : 0 ≤ ν / t ^ 2 := div_nonneg hν (sq_nonneg _)
  by_cases hij : i = j
  · subst j
    obtain ⟨hfl, hMl⟩ := hline.1 i
    obtain ⟨hp, hm⟩ := hquery.2.1 i
    have he := ThirdDifference.directionalSecond_error f report x (coordinate i)
      ht hf hfl hMl hp hquery.1 hm
    rw [matrixReport, if_pos rfl, abs_sub_comm]
    change |KSFourthDifference.directionalSecond report x (coordinate i) t -
      fderiv ℝ (fderiv ℝ f) x (coordinate i) (coordinate i)| ≤ _
    nlinarith
  · obtain ⟨hfp, hfm, hMp, hMm⟩ := hline.2 i j hij
    obtain ⟨hPP, hPM, hMP, hMM⟩ := hquery.2.2 i j hij
    have he := ThirdDifference.mixedStencil_error f report x (coordinate i)
      (coordinate j) ht hf hfp hfm hMp hMm hPP hPM hMP hMM
    rw [matrixReport, if_neg hij, abs_sub_comm]
    change |KSFourthDifference.mixedStencil report x (coordinate i) (coordinate j) t -
      fderiv ℝ (fderiv ℝ f) x (coordinate i) (coordinate j)| ≤ _
    have hnoise : 4 * ν / t ^ 2 = 4 * (ν / t ^ 2) := by ring
    rw [hnoise]
    nlinarith

theorem operator_error (f report : Space m → ℝ) (x : Space m)
    {t M ν : ℝ} (ht : 0 < t) (hM : 0 ≤ M) (hν : 0 ≤ ν)
    (hf : ContDiffAt ℝ 2 f x) (hline : LineBounds f x t M)
    (hquery : QueryAccuracy f report x t ν) :
    ‖hessian f x - matrixReport report x t‖ ≤
      (m : ℝ) * (2 * M * t + 4 * ν / t ^ 2) := by
  apply KSMatrixEntryAccuracy.operatorNorm_le_card_mul
  · positivity
  · exact entry_error f report x ht hM hν hf hline hquery

theorem accuracy_budget {N : ℕ} {t M ν γ : ℝ}
    (hN : 0 < N) (hM : 0 < M) (ht : 0 < t) (hγ : 0 < γ)
    (htbound : t ≤ γ / (64 * N * M))
    (hνbound : ν ≤ γ * t ^ 2 / (256 * N)) :
    (N : ℝ) * (2 * M * t + 4 * ν / t ^ 2) < γ / 8 := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have ht2 : 0 < t ^ 2 := sq_pos_of_pos ht
  have htclear := (le_div_iff₀ (by positivity : 0 < 64 * (N : ℝ) * M)).mp htbound
  have hνclear := (le_div_iff₀ (by positivity : 0 < 256 * (N : ℝ))).mp hνbound
  have hfirst : (N : ℝ) * (2 * M * t) ≤ γ / 32 := by nlinarith
  have hsecond : (N : ℝ) * (4 * ν / t ^ 2) ≤ γ / 64 := by
    have hquot : 4 * (N : ℝ) * ν / t ^ 2 ≤ γ / 64 := by
      apply (div_le_iff₀ ht2).2
      nlinarith
    convert hquot using 1 <;> ring
  nlinarith

end HigherRankKSRuntime.NumericHessian
