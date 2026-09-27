import RadialKS.Frame
import RadialKS.RestrictedEVD
import RadialKS.DeterministicRun
import SeamlessKS.LocalNumerics

/-! Finite value queries for the unweighted Hessian, followed by restricted EVD
and deterministic comparison of the two physical movements. -/
open Matrix Set
open scoped BigOperators
noncomputable section
namespace RadialKS.RawNumerics
open MatrixSpencer MatrixSpencer.KSRayleighAccuracy
open MatrixSpencer.KSNumericalHessian (Space hessian)
open MatrixSpencer.KSFullManuscriptHessian (weighted matrixReport LineBounds QueryAccuracy)
open SeamlessKS.LocalNumerics (queryStep queryTolerance)
variable {m N : ℕ}

def half (A : Matrix (Fin m) (Fin m) ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  weighted (fun _ => 1) A

theorem half_rayleigh (A : Matrix (Fin m) (Fin m) ℝ) (g : Space m) :
    realRayleigh (half A) g = realRayleigh A g / 2 := by
  have he : SeamlessKS.NormalizedHessian.diagonalMap (fun _ : Fin m => 1) g = g := by
    ext i
    simp [SeamlessKS.NormalizedHessian.diagonalMap_apply]
  rw [half, SeamlessKS.NormalizedHessian.weighted_rayleigh, he]

theorem report_error (f report : Space m → ℝ) (x : Space m)
    (hN : 0 < N) (hmN : m ≤ N) {ρ β M : ℝ}
    (hρ : 0 < ρ) (hβ : 0 < β) (hM : 0 < M)
    (hf : ContDiffAt ℝ 2 f x)
    (hline : LineBounds f x (queryStep N ρ β M) M)
    (hquery : QueryAccuracy f report x (queryStep N ρ β M) (queryTolerance N ρ β M)) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ)
      (half (hessian f x) - half (matrixReport report x (queryStep N ρ β M)))‖ ≤ β / 16 := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hmNr : (m : ℝ) ≤ N := by exact_mod_cast hmN
  have he := KSFullManuscriptHessian.entry_error f report x
    (SeamlessKS.LocalNumerics.queryStep_pos hN hρ hβ hM) hM.le
    (SeamlessKS.LocalNumerics.queryTolerance_pos hN hρ hβ hM).le hf hline hquery
  have hb := SeamlessKS.LocalNumerics.query_error_budget hN hρ hβ hM
  have hw := SeamlessKS.NormalizedHessian.weighted_entry_error (fun _ : Fin m => (1 : ℝ))
    (by intro i; norm_num) (by positivity : 0 ≤ β / (16 * (N : ℝ)))
    (fun i j => (he i j).trans hb)
  have hop := KSMatrixEntryAccuracy.operatorNorm_le_card_mul
    (half (hessian f x) - half (matrixReport report x (queryStep N ρ β M)))
    (by positivity : 0 ≤ β / (16 * (N : ℝ))) hw
  apply hop.trans
  calc
    (m : ℝ) * (β / (16 * (N : ℝ))) ≤ (N : ℝ) * (β / (16 * (N : ℝ))) :=
      mul_le_mul_of_nonneg_right hmNr (by positivity)
    _ = β / 16 := by field_simp

def output (report : Space m → ℝ) (x z : Space m) (N : ℕ) (ρ β M : ℝ)
    (hr : 0 < (Frame.canonical m z).rank) : Space m :=
  RestrictedEVD.output (Frame.canonical m z).embed
    (half (matrixReport report x (queryStep N ρ β M))) hr

theorem output_norm (report : Space m → ℝ) (x z : Space m) (N : ℕ) (ρ β M : ℝ)
    (hr : 0 < (Frame.canonical m z).rank) : ‖output report x z N ρ β M hr‖ = 1 :=
  RestrictedEVD.output_norm _ _ _

theorem output_orthogonal (report : Space m → ℝ) (x z : Space m) (N : ℕ) (ρ β M : ℝ)
    (hr : 0 < (Frame.canonical m z).rank) : inner ℝ z (output report x z N ρ β M hr) = 0 :=
  (Frame.canonical m z).orthogonal _

theorem output_curvature (f report : Space m → ℝ) (x z : Space m)
    (hN : 0 < N) (hmN : m ≤ N) {ρ β M : ℝ}
    (hρ : 0 < ρ) (hβ : 0 < β) (hM : 0 < M)
    (hf : ContDiffAt ℝ 2 f x)
    (hline : LineBounds f x (queryStep N ρ β M) M)
    (hquery : QueryAccuracy f report x (queryStep N ρ β M) (queryTolerance N ρ β M))
    (hr : 0 < (Frame.canonical m z).rank)
    (g : Space m) (hg : ‖g‖ = 1) (horth : inner ℝ z g = 0)
    (hneg : realRayleigh (hessian f x) g < 0) :
    realRayleigh (half (hessian f x)) (output report x z N ρ β M hr) < β / 2 := by
  obtain ⟨w, hw⟩ := (Frame.canonical m z).onto g horth
  have hwn : ‖w‖ = 1 := by rw [← (Frame.canonical m z).embed.norm_map, hw, hg]
  have he := report_error f report x hN hmN hρ hβ hM hf hline hquery
  have hs := KSFullManuscriptHessian.weighted_isSymm (fun _ : Fin m => (1 : ℝ))
    (KSFullManuscriptHessian.matrixReport_isSymm report x (queryStep N ρ β M))
  have hc := RestrictedEVD.output_comparison (Frame.canonical m z).embed
    (half (hessian f x)) (half (matrixReport report x (queryStep N ρ β M))) hs hr he w hwn
  rw [hw] at hc
  have hng : realRayleigh (half (hessian f x)) g < 0 := by
    rw [half_rayleigh]
    linarith
  change realRayleigh (half (hessian f x)) (output report x z N ρ β M hr) ≤ _ at hc
  linarith

theorem chosen_potential (f : Space m → ℝ) (x g : Space m)
    {h β M qp qm ν : ℝ} (hh : 0 < h) (hβ : 0 ≤ β)
    (hf : ContDiffAt ℝ 2 f x)
    (hline : ContDiffOn ℝ 4 (fun t => f (x + t • g)) (Icc (-h) h))
    (hfourth : ∀ t ∈ Icc (-h) h, |iteratedDeriv 4 (fun t => f (x + t • g)) t| ≤ M)
    (hcurvature : realRayleigh (half (hessian f x)) g ≤ β / 2)
    (hbudget : M * h ^ 2 ≤ β)
    (hν : ν ≤ β * h ^ 2 / 8)
    (hqp : |qp - f (x + h • g)| ≤ ν) (hqm : |qm - f (x - h • g)| ≤ ν) :
    (if DeterministicRun.choosePlus qp qm then f (x + h • g) else f (x - h • g)) ≤
      f x + β * h ^ 2 := by
  have ht := KSFourthDifference.directional_average_le f x g hh hf hline hfourth
  have hs := DeterministicRun.chosen_value_le_average hqp hqm
  rw [half_rayleigh, KSNumericalHessian.hessian_rayleigh] at hcurvature
  have hc := mul_le_mul_of_nonneg_right hcurvature (sq_nonneg h)
  have hr := mul_le_mul_of_nonneg_right hbudget (sq_nonneg h)
  have hn := mul_nonneg hβ (sq_nonneg h)
  have he : h ^ 4 = h ^ 2 * h ^ 2 := by ring
  rw [he] at ht
  nlinarith

end RadialKS.RawNumerics
