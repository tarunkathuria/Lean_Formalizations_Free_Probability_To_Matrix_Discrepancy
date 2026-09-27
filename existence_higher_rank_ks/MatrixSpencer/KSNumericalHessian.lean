import MatrixSpencer.KSFourthDifference
import MatrixSpencer.KSMatrixEntryAccuracy

/-!
# A finite Hessian report and its constructed Jacobi direction

Every matrix entry is the actual four-query mixed stencil, including diagonal
entries. The query lines therefore use the unnormalized directions `eᵢ + eⱼ`
and `eᵢ - eⱼ`; when `i = j` the first direction is `2 eᵢ`. The common fourth
derivative bound in this file is explicitly a bound on those actual lines.

An explicit positive mesh and value-report tolerance give entry error `κ/d`.
Symmetrizing the finite matrix and running the existing finite Jacobi routine
then returns a unit vector with true Rayleigh value at most the least true
Rayleigh value plus `3 κ`. No Hessian-entry or eigenvector oracle is used.
The actual line smoothness, fourth derivative cap, and query-value accuracy
remain hypotheses here; this file does not derive an outer potential bound.
-/

open Matrix Set
open scoped BigOperators Topology
noncomputable section
namespace MatrixSpencer.KSNumericalHessian

variable {d : ℕ}

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

def coordinate (i : Fin d) : Space d := EuclideanSpace.single i 1

def hessian (f : Space d → ℝ) (x : Space d) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j => fderiv ℝ (fderiv ℝ f) x (coordinate i) (coordinate j)

/-- All `d²` entries use the same four-query formula, without a diagonal branch. -/
def matrixReport (r : Space d → ℝ) (x : Space d) (t : ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  fun i j => KSFourthDifference.mixedStencil r x (coordinate i) (coordinate j) t

theorem matrixReport_queries (r : Space d → ℝ) (x : Space d) (t : ℝ) (i j : Fin d) :
    matrixReport r x t i j =
      (r (x + t • coordinate i + t • coordinate j) -
        r (x + t • coordinate i - t • coordinate j) -
        r (x - t • coordinate i + t • coordinate j) +
        r (x - t • coordinate i - t • coordinate j)) / (4 * t ^ 2) :=
  KSFourthDifference.mixedStencil_eq_four_queries r x (coordinate i) (coordinate j) t

theorem hessian_isSymm (f : Space d → ℝ) (x : Space d)
    (hf : ContDiffAt ℝ 2 f x) : (hessian f x).IsSymm := by
  have hs := hf.isSymmSndFDerivAt
    (by simp only [minSmoothness_of_isRCLikeNormedField]; exact le_rfl)
  ext i j
  exact hs _ _

/-- Smoothness and a common cap on the exact two lines sampled for each entry. -/
def LineBounds (f : Space d → ℝ) (x : Space d) (radius M : ℝ) : Prop :=
  ∀ i j : Fin d,
    ContDiffOn ℝ 4 (fun s => f (x + s • (coordinate i + coordinate j)))
        (Icc (-radius) radius) ∧
    ContDiffOn ℝ 4 (fun s => f (x + s • (coordinate i - coordinate j)))
        (Icc (-radius) radius) ∧
    (∀ s ∈ Icc (-radius) radius,
      |iteratedDeriv 4 (fun w => f (x + w • (coordinate i + coordinate j))) s| ≤ M) ∧
    (∀ s ∈ Icc (-radius) radius,
      |iteratedDeriv 4 (fun w => f (x + w • (coordinate i - coordinate j))) s| ≤ M)

/-- Accuracy is required only at the finitely many queried points. -/
def QueryAccuracy (f r : Space d → ℝ) (x : Space d) (t ν : ℝ) : Prop :=
  ∀ i j : Fin d,
    |r (x + t • (coordinate i + coordinate j)) -
      f (x + t • (coordinate i + coordinate j))| ≤ ν ∧
    |r (x + t • (coordinate i - coordinate j)) -
      f (x + t • (coordinate i - coordinate j))| ≤ ν ∧
    |r (x - t • (coordinate i - coordinate j)) -
      f (x - t • (coordinate i - coordinate j))| ≤ ν ∧
    |r (x - t • (coordinate i + coordinate j)) -
      f (x - t • (coordinate i + coordinate j))| ≤ ν

theorem matrixReport_entry_error (f r : Space d → ℝ) (x : Space d)
    {t radius M ν : ℝ} (ht : 0 < t) (htr : t ≤ radius)
    (hf : ContDiffAt ℝ 2 f x) (hlines : LineBounds f x radius M)
    (hquery : QueryAccuracy f r x t ν) (i j : Fin d) :
    |hessian f x i j - matrixReport r x t i j| ≤ M * t ^ 2 / 24 + ν / t ^ 2 := by
  rcases hlines i j with ⟨hfp, hfm, hMp, hMm⟩
  rcases hquery i j with ⟨hPP, hPM, hMP, hMM⟩
  have hsub : Icc (-t) t ⊆ Icc (-radius) radius := by
    intro s hs
    exact ⟨by linarith [hs.1], hs.2.trans htr⟩
  have he := KSFourthDifference.mixedStencil_error f r x (coordinate i) (coordinate j)
    ht hf (hfp.mono hsub) (hfm.mono hsub)
    (fun s hs => hMp s (hsub hs)) (fun s hs => hMm s (hsub hs)) hPP hPM hMP hMM
  rw [abs_sub_comm] at he
  change |hessian f x i j - matrixReport r x t i j| ≤ _ at he
  convert he using 1
  ring

def mesh (d : ℕ) (radius M κ : ℝ) : ℝ :=
  min radius (Real.sqrt (κ / ((d : ℝ) * (M + 1))))

def valueTolerance (d : ℕ) (radius M κ : ℝ) : ℝ :=
  κ * mesh d radius M κ ^ 2 / (4 * d)

theorem mesh_pos (hd : 0 < d) {radius M κ : ℝ}
    (hr : 0 < radius) (hM : 0 ≤ M) (hκ : 0 < κ) : 0 < mesh d radius M κ := by
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  exact lt_min hr (Real.sqrt_pos.2 (div_pos hκ (mul_pos hdr (by linarith))))

theorem mesh_le_radius (d : ℕ) (radius M κ : ℝ) : mesh d radius M κ ≤ radius :=
  min_le_left _ _

theorem valueTolerance_pos (hd : 0 < d) {radius M κ : ℝ}
    (hr : 0 < radius) (hM : 0 ≤ M) (hκ : 0 < κ) :
    0 < valueTolerance d radius M κ := by
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  exact div_pos (mul_pos hκ (sq_pos_of_pos (mesh_pos hd hr hM hκ))) (by positivity)

/-- The mesh and report tolerance use only the supplied radius, cap, dimension,
and requested operator error; no limiting or unbounded numerical search occurs. -/
theorem parameter_error_bound (hd : 0 < d) {radius M κ : ℝ}
    (hr : 0 < radius) (hM : 0 ≤ M) (hκ : 0 < κ) :
    M * mesh d radius M κ ^ 2 / 24 +
      valueTolerance d radius M κ / mesh d radius M κ ^ 2 ≤ κ / d := by
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have ht := mesh_pos hd hr hM hκ
  have hden : 0 < (d : ℝ) * (M + 1) := mul_pos hdr (by linarith)
  have hs : mesh d radius M κ ^ 2 ≤ κ / ((d : ℝ) * (M + 1)) := by
    calc
      _ ≤ Real.sqrt (κ / ((d : ℝ) * (M + 1))) ^ 2 :=
        pow_le_pow_left₀ ht.le (min_le_right _ _) 2
      _ = _ := Real.sq_sqrt (div_nonneg hκ.le hden.le)
  have hmul : mesh d radius M κ ^ 2 * ((d : ℝ) * (M + 1)) ≤ κ :=
    (le_div_iff₀ hden).mp hs
  have hfourth : M * mesh d radius M κ ^ 2 ≤ κ / d := by
    apply (le_div_iff₀ hdr).mpr
    nlinarith [mul_nonneg hdr.le (sq_nonneg (mesh d radius M κ))]
  have hnoise : valueTolerance d radius M κ / mesh d radius M κ ^ 2 = (κ / d) / 4 := by
    unfold valueTolerance
    field_simp [ne_of_gt ht, ne_of_gt hdr]
  rw [hnoise]
  nlinarith [div_pos hκ hdr]

/-- Every entry is accurate enough for the dimension-to-operator estimate. -/
theorem selected_entry_error (f r : Space d → ℝ) (x : Space d)
    (hd : 0 < d) {radius M κ : ℝ} (hr : 0 < radius) (hM : 0 ≤ M) (hκ : 0 < κ)
    (hf : ContDiffAt ℝ 2 f x) (hlines : LineBounds f x radius M)
    (hquery : QueryAccuracy f r x (mesh d radius M κ) (valueTolerance d radius M κ)) :
    ∀ i j, |hessian f x i j - matrixReport r x (mesh d radius M κ) i j| ≤ κ / d := by
  intro i j
  exact (matrixReport_entry_error f r x (mesh_pos hd hr hM hκ)
    (mesh_le_radius d radius M κ) hf hlines hquery i j).trans
      (parameter_error_bound hd hr hM hκ)

theorem coordinate_expansion (v : Space d) : (∑ i, v i • coordinate i) = v := by
  simpa [coordinate] using (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr v

/-- The true matrix quadratic form is exactly the actual Hessian quadratic form. -/
theorem hessian_rayleigh (f : Space d → ℝ) (x v : Space d) :
    KSRayleighAccuracy.realRayleigh (hessian f x) v =
      fderiv ℝ (fderiv ℝ f) x v v := by
  have he : fderiv ℝ (fderiv ℝ f) x v v =
      ∑ i, ∑ j, v i * (hessian f x i j * v j) := by
    calc
      _ = fderiv ℝ (fderiv ℝ f) x (∑ i, v i • coordinate i)
          (∑ j, v j • coordinate j) := by rw [coordinate_expansion]
      _ = _ := by
        simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply,
          ContinuousLinearMap.smul_apply, smul_eq_mul, Finset.mul_sum, hessian]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
  rw [he, KSRayleighAccuracy.realRayleigh_eq_quadratic]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  rfl

/-- The numerical output evaluates only the value report and finite arithmetic
Jacobi routine. The exact function `f` is absent from this definition. -/
def output (r : Space d → ℝ) (x : Space d) (radius M κ : ℝ) (hd : 0 < d) : Space d :=
  KSJacobiRayleigh.outputVector
    (KSMatrixEntryAccuracy.symmetrize (matrixReport r x (mesh d radius M κ))) κ hd

theorem output_accuracy (f r : Space d → ℝ) (x : Space d)
    (hd : 0 < d) {radius M κ : ℝ} (hr : 0 < radius) (hM : 0 ≤ M) (hκ : 0 < κ)
    (hf : ContDiffAt ℝ 2 f x) (hlines : LineBounds f x radius M)
    (hquery : QueryAccuracy f r x (mesh d radius M κ) (valueTolerance d radius M κ)) :
    ‖output r x radius M κ hd‖ = 1 ∧
      KSRayleighAccuracy.realRayleigh (hessian f x) (output r x radius M κ hd) ≤
        KSRayleighAccuracy.leastRayleigh (hessian f x) + 3 * κ :=
  KSMatrixEntryAccuracy.jacobi_output_accuracy (hessian_isSymm f x hf) hd hκ
    (selected_entry_error f r x hd hr hM hκ hf hlines hquery)

/-- The same guarantee stated directly for the actual scalar curve's second
derivative along the computed vector. -/
theorem output_curve_accuracy (f r : Space d → ℝ) (x : Space d)
    (hd : 0 < d) {radius M κ : ℝ} (hr : 0 < radius) (hM : 0 ≤ M) (hκ : 0 < κ)
    (hf : ContDiffAt ℝ 2 f x) (hlines : LineBounds f x radius M)
    (hquery : QueryAccuracy f r x (mesh d radius M κ) (valueTolerance d radius M κ)) :
    ‖output r x radius M κ hd‖ = 1 ∧
      iteratedDeriv 2 (fun s : ℝ => f (x + s • output r x radius M κ hd)) 0 ≤
        KSRayleighAccuracy.leastRayleigh (hessian f x) + 3 * κ := by
  rcases output_accuracy f r x hd hr hM hκ hf hlines hquery with ⟨hn, he⟩
  refine ⟨hn, ?_⟩
  rw [KSFourthDifference.line_second f x _ hf, ← hessian_rayleigh]
  exact he

end MatrixSpencer.KSNumericalHessian
