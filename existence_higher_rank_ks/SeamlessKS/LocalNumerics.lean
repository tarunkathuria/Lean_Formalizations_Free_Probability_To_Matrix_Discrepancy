import SeamlessKS.NormalizedHessian
import SeamlessKS.ExactEVD

/-!
# Finite local Hessian queries and their true movement drift

This module constructs the stencil and exact-EVD vector from value reports.
The intermediate calculus hypotheses describe actual line derivatives and
finite query accuracy; a complete application must instantiate them from
the smooth-source regularity and the explicitly specified SDP routine.
Neither a Hessian oracle nor a selected negative direction is an input to
the numerical output definition.
-/

open Matrix Set
open scoped BigOperators Topology
noncomputable section
namespace SeamlessKS.LocalNumerics

open MatrixSpencer
open MatrixSpencer.KSNumericalHessian (Space hessian)
open MatrixSpencer.KSFullManuscriptHessian (weighted matrixReport LineBounds QueryAccuracy)
open MatrixSpencer.KSRayleighAccuracy
open SeamlessKS.NormalizedHessian

variable {m N : ℕ}

def queryStep (N : ℕ) (ρ β M : ℝ) : ℝ :=
  min (ρ / 16) (Real.sqrt (β / (128 * (N : ℝ) * M)))

def queryTolerance (N : ℕ) (ρ β M : ℝ) : ℝ :=
  β * queryStep N ρ β M ^ 2 / (128 * (N : ℝ))

def movementStep (ρ β M : ℝ) : ℝ :=
  min (ρ / 16) (Real.sqrt (β / (4 * M)))

theorem queryStep_pos (hN : 0 < N) {ρ β M : ℝ}
    (hρ : 0 < ρ) (hβ : 0 < β) (hM : 0 < M) : 0 < queryStep N ρ β M := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  exact lt_min (by positivity) (Real.sqrt_pos.mpr (by positivity))

theorem queryTolerance_pos (hN : 0 < N) {ρ β M : ℝ}
    (hρ : 0 < ρ) (hβ : 0 < β) (hM : 0 < M) : 0 < queryTolerance N ρ β M := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  unfold queryTolerance
  exact div_pos (mul_pos hβ (sq_pos_of_pos (queryStep_pos hN hρ hβ hM))) (by positivity)

theorem queryStep_le_radius (N : ℕ) (ρ β M : ℝ) : queryStep N ρ β M ≤ ρ / 16 :=
  min_le_left _ _


theorem query_error_budget (hN : 0 < N) {ρ β M : ℝ}
    (hρ : 0 < ρ) (hβ : 0 < β) (hM : 0 < M) :
    2 * M * queryStep N ρ β M ^ 2 +
      4 * queryTolerance N ρ β M / queryStep N ρ β M ^ 2 ≤ β / (16 * (N : ℝ)) := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have ht := queryStep_pos hN hρ hβ hM
  have ht2 : queryStep N ρ β M ^ 2 ≤ β / (128 * (N : ℝ) * M) := by
    have hh := pow_le_pow_left₀ ht.le
      (min_le_right (ρ / 16) (Real.sqrt (β / (128 * (N : ℝ) * M)))) 2
    rwa [Real.sq_sqrt (by positivity)] at hh
  have hmain : M * queryStep N ρ β M ^ 2 ≤ β / (128 * (N : ℝ)) := by
    apply (le_div_iff₀ (by positivity : 0 < 128 * (N : ℝ))).mpr
    have hh := (le_div_iff₀ (by positivity : 0 < 128 * (N : ℝ) * M)).mp ht2
    nlinarith
  have hnoise : queryTolerance N ρ β M / queryStep N ρ β M ^ 2 =
      β / (128 * (N : ℝ)) := by
    unfold queryTolerance
    field_simp [ht.ne', hNr.ne']
  have hsplit : β / (128 * (N : ℝ)) = (β / (16 * (N : ℝ))) / 8 := by ring
  rw [mul_div_assoc, hnoise]
  rw [hsplit] at hmain ⊢
  have hb : 0 ≤ β / (16 * (N : ℝ)) := by positivity
  nlinarith

/-- A value-report-only numerical direction; the true function is absent. -/
def output (report : Space m → ℝ) (x : Space m) (w : Fin m → ℝ)
    (N : ℕ) (ρ β M : ℝ) (hm : 0 < m) : Space m :=
  ExactEVD.output
    (weighted w (matrixReport report x (queryStep N ρ β M))) hm

theorem output_accuracy (f report : Space m → ℝ) (x : Space m)
    (w : Fin m → ℝ) (hw : ∀ i, w i ^ 2 ≤ 2) (hm : 0 < m) (hmN : m ≤ N)
    {ρ β M : ℝ} (hρ : 0 < ρ) (hβ : 0 < β) (hM : 0 < M)
    (hf : ContDiffAt ℝ 2 f x)
    (hline : LineBounds f x (queryStep N ρ β M) M)
    (hquery : QueryAccuracy f report x (queryStep N ρ β M) (queryTolerance N ρ β M)) :
    ‖output report x w N ρ β M hm‖ = 1 ∧
      realRayleigh (weighted w (hessian f x)) (output report x w N ρ β M hm) ≤
        leastRayleigh (weighted w (hessian f x)) + 3 * (β / 8) := by
  have hN : 0 < N := hm.trans_le hmN
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hmNr : (m : ℝ) ≤ N := by exact_mod_cast hmN
  have ht := queryStep_pos hN hρ hβ hM
  have hν := queryTolerance_pos hN hρ hβ hM
  have he := KSFullManuscriptHessian.entry_error f report x ht hM.le hν.le hf hline hquery
  have hb := query_error_budget hN hρ hβ hM
  have hwerr := SeamlessKS.NormalizedHessian.weighted_entry_error w hw
    (by positivity : 0 ≤ β / (16 * (N : ℝ))) (fun i j => (he i j).trans hb)
  have hop := KSMatrixEntryAccuracy.operatorNorm_le_card_mul
    (weighted w (hessian f x) - weighted w (matrixReport report x (queryStep N ρ β M)))
    (by positivity : 0 ≤ β / (16 * (N : ℝ))) hwerr
  have hdim : (m : ℝ) * (β / (16 * (N : ℝ))) ≤ β / 16 := by
    calc
      _ ≤ (N : ℝ) * (β / (16 * (N : ℝ))) :=
        mul_le_mul_of_nonneg_right hmNr (by positivity)
      _ = β / 16 := by field_simp
  have herr : ‖Matrix.toEuclideanCLM (𝕜 := ℝ)
      (weighted w (hessian f x) - weighted w (matrixReport report x (queryStep N ρ β M)))‖ ≤ β / 8 :=
    (hop.trans hdim).trans (by linarith)
  have hs := KSFullManuscriptHessian.weighted_isSymm w
    (KSFullManuscriptHessian.matrixReport_isSymm report x (queryStep N ρ β M))
  have hn := ExactEVD.output_norm (weighted w (matrixReport report x (queryStep N ρ β M))) hm
  have ha := ExactEVD.output_accuracy (weighted w (matrixReport report x (queryStep N ρ β M))) hs hm
  exact ⟨hn, approximate_minimum_Rayleigh_accuracy _ _ herr _ hn (ha.trans (le_add_of_nonneg_right (by positivity)))⟩

/-- Failed local tests supply negative curvature analytically; finite value
queries and exact EVD then return a true Rayleigh value below `β/2`. -/
theorem output_curvature (f report : Space m → ℝ) (x : Space m)
    (w : Fin m → ℝ) (hw : ∀ i, w i ^ 2 ≤ 2) (hm : 0 < m) (hmN : m ≤ N)
    {ρ β M : ℝ} (hρ : 0 < ρ) (hβ : 0 < β) (hM : 0 < M)
    (hf : ContDiffAt ℝ 2 f x)
    (hline : LineBounds f x (queryStep N ρ β M) M)
    (hquery : QueryAccuracy f report x (queryStep N ρ β M) (queryTolerance N ρ β M))
    (hnegative : leastRayleigh (weighted w (hessian f x)) ≤ 0) :
    ‖output report x w N ρ β M hm‖ = 1 ∧
      realRayleigh (weighted w (hessian f x)) (output report x w N ρ β M hm) < β / 2 := by
  have hh := output_accuracy f report x w hw hm hmN hρ hβ hM hf hline hquery
  exact ⟨hh.1, by linarith [hh.2]⟩

theorem movementStep_pos {ρ β M : ℝ} (hρ : 0 < ρ) (hβ : 0 < β) (hM : 0 < M) :
    0 < movementStep ρ β M := lt_min (by positivity) (Real.sqrt_pos.mpr (by positivity))

theorem movementStep_le_radius (ρ β M : ℝ) : movementStep ρ β M ≤ ρ / 16 :=
  min_le_left _ _

theorem movement_remainder_budget {ρ β M : ℝ}
    (hρ : 0 < ρ) (hβ : 0 < β) (hM : 0 < M) :
    M * movementStep ρ β M ^ 2 ≤ β := by
  have ht := movementStep_pos hρ hβ hM
  have ht2 := pow_le_pow_left₀ ht.le
    (min_le_right (ρ / 16) (Real.sqrt (β / (4 * M)))) 2
  rw [Real.sq_sqrt (by positivity)] at ht2
  have hh := (le_div_iff₀ (by positivity : 0 < 4 * M)).mp ht2
  nlinarith

/-- The symmetric walk drift is a proved fourth-order Taylor consequence
for the actual weighted direction, including the factor `1/2` in `K`. -/
theorem symmetric_average_le (f : Space m → ℝ) (x v : Space m) (w : Fin m → ℝ)
    {h β M : ℝ} (hh : 0 < h) (hβ : 0 ≤ β)
    (hf : ContDiffAt ℝ 2 f x)
    (hline : ContDiffOn ℝ 4 (fun t => f (x + t • diagonalMap w v)) (Icc (-h) h))
    (hfourth : ∀ t ∈ Icc (-h) h,
      |iteratedDeriv 4 (fun s => f (x + s • diagonalMap w v)) t| ≤ M)
    (hcurvature : realRayleigh (weighted w (hessian f x)) v ≤ β / 2)
    (hbudget : M * h ^ 2 ≤ β) :
    (f (x + h • diagonalMap w v) + f (x - h • diagonalMap w v)) / 2 ≤ f x + β * h ^ 2 := by
  have ht := KSFourthDifference.directional_average_le f x (diagonalMap w v) hh hf hline hfourth
  have he := weighted_hessian_rayleigh w f x v
  have hc := mul_le_mul_of_nonneg_right hcurvature (sq_nonneg h)
  have hr := mul_le_mul_of_nonneg_right hbudget (sq_nonneg h)
  have hp : h ^ 4 = h ^ 2 * h ^ 2 := by ring
  rw [hp] at ht
  have hb := mul_nonneg hβ (sq_nonneg h)
  nlinarith

end SeamlessKS.LocalNumerics
