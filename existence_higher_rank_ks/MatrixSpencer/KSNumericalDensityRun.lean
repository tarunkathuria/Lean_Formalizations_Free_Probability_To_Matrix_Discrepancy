import MatrixSpencer.KSNumericalGradient
import MatrixSpencer.KSCoordinateProjection
import MatrixSpencer.KSOptimizerParameters

/-!
# The actual finite physical-matrix density optimizer

The numerical loop operates on complex matrix entries, using the proved
finite gradient and Jacobi/simplex projection routines. Its coordinate view
is identified with the analyzed projected iteration, so the convergence
theorem has no supplied gradient or projection accuracy hypotheses.
-/

open Matrix Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSNumericalDensityRun

open KSFullHermitianChart KSOptimizerParameters KSInexactIteration KSComplexProjectionGeometry
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}
local instance : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
local instance : NormedSpace ℝ (selfAdjoint (Matrix (Fin d) (Fin d) ℂ)) := inferInstance

def stepSize (a κ θ : ℝ) : ℝ := step (θ / 2) (densityL (n := Fin d) a κ θ)
def gradientTolerance (a κ θ τ : ℝ) : ℝ := gradientError (θ / 2) (densityL (n := Fin d) a κ θ) τ
def projectionTolerance (a κ θ τ : ℝ) : ℝ := projectionError (θ / 2) (densityL (n := Fin d) a κ θ) τ
def iterationCount (a κ θ τ : ℝ) : ℕ := count (θ / 2) (densityL (n := Fin d) a κ θ) τ

/-- A physical update contains no analytical chart or exact optimizer. -/
def update (H : Matrix (Fin d) (Fin d) ℂ) (A : ι → Matrix (Fin d) (Fin d) ℂ)
    (C : Matrix ι ι ℝ) (θ a κ τ : ℝ) (hd : 0 < d) (S : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  KSComplexMatrixProjection.report
    (S + stepSize (d := d) a κ θ • KSNumericalGradient.report H A C θ S a κ
      (gradientTolerance (d := d) a κ θ τ)) a 1 hd (projectionTolerance (d := d) a κ θ τ)

def run (H : Matrix (Fin d) (Fin d) ℂ) (A : ι → Matrix (Fin d) (Fin d) ℂ)
    (C : Matrix ι ι ℝ) (θ a κ τ : ℝ) (hd : 0 < d) (S₀ : Matrix (Fin d) (Fin d) ℂ) :
    ℕ → Matrix (Fin d) (Fin d) ℂ := iterate (fun _ => update H A C θ a κ τ hd) S₀

def output (H : Matrix (Fin d) (Fin d) ℂ) (A : ι → Matrix (Fin d) (Fin d) ℂ)
    (C : Matrix ι ι ℝ) (θ a κ τ : ℝ) (hd : 0 < d) (S₀ : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  run H A C θ a κ τ hd S₀ (iterationCount (d := d) a κ θ τ)

theorem update_feasible (H : Matrix (Fin d) (Fin d) ℂ) (A : ι → Matrix (Fin d) (Fin d) ℂ)
    (C : Matrix ι ι ℝ) (θ a κ τ : ℝ) (hd : 0 < d) (has : (d : ℝ) * a ≤ 1)
    (S : Matrix (Fin d) (Fin d) ℂ) : ComplexFeasible a 1 (update H A C θ a κ τ hd S) :=
  KSComplexMatrixProjection.report_feasible _ a 1 hd has _

theorem run_feasible (H : Matrix (Fin d) (Fin d) ℂ) (A : ι → Matrix (Fin d) (Fin d) ℂ)
    (C : Matrix ι ι ℝ) (θ a κ τ : ℝ) (hd : 0 < d) (has : (d : ℝ) * a ≤ 1)
    (S₀ : Matrix (Fin d) (Fin d) ℂ) (hstart : ComplexFeasible a 1 S₀) (k : ℕ) :
    ComplexFeasible a 1 (run H A C θ a κ τ hd S₀ k) :=
  iterate_mem _ S₀ {S | ComplexFeasible a 1 S} hstart
    (fun _ S _ => update_feasible H A C θ a κ τ hd has S) k

def coordinateRun (H : Matrix (Fin d) (Fin d) ℂ) (A : ι → Matrix (Fin d) (Fin d) ℂ)
    (C : Matrix ι ι ℝ) (θ a κ τ : ℝ) (hd : 0 < d) (has : (d : ℝ) * a ≤ 1)
    (x₀ : Coordinates (Fin d)) : ℕ → Coordinates (Fin d) :=
  projectedGradientIteration (stepSize (d := d) a κ θ)
    (KSNumericalGradient.coordinateReport H A C θ a κ (gradientTolerance (d := d) a κ θ τ))
    (KSCoordinateProjection.projectionReport a hd has (projectionTolerance (d := d) a κ θ τ)) x₀

/-- The chart is only a proof bridge: it maps each computed iteration to
the same physical matrix produced by the arithmetic loop. -/
theorem coordinateRun_physical (H : Matrix (Fin d) (Fin d) ℂ)
    (A : ι → Matrix (Fin d) (Fin d) ℂ) (C : Matrix ι ι ℝ) (θ a κ τ : ℝ)
    (hd : 0 < d) (has : (d : ℝ) * a ≤ 1) (x₀ : Coordinates (Fin d)) (k : ℕ) :
    (chart (Fin d) (coordinateRun H A C θ a κ τ hd has x₀ k) : Matrix (Fin d) (Fin d) ℂ) =
      run H A C θ a κ τ hd (chart (Fin d) x₀) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (chart (Fin d) (KSCoordinateProjection.report a hd has
      (projectionTolerance (d := d) a κ θ τ)
      (coordinateRun H A C θ a κ τ hd has x₀ k + stepSize (d := d) a κ θ •
        KSNumericalGradient.coordinateReport H A C θ a κ (gradientTolerance (d := d) a κ θ τ)
          k (coordinateRun H A C θ a κ τ hd has x₀ k))) : Matrix (Fin d) (Fin d) ℂ) =
      update H A C θ a κ τ hd (run H A C θ a κ τ hd (chart (Fin d) x₀) k)
    rw [KSCoordinateProjection.chart_report]
    unfold KSCoordinateProjection.physicalReport KSCoordinateProjection.physical update
    simp only [map_add, map_smul]
    have hg (x : Coordinates (Fin d)) :
        chart (Fin d) (KSNumericalGradient.coordinateReport H A C θ a κ
          (gradientTolerance (d := d) a κ θ τ) k x) =
          ⟨KSNumericalGradient.report H A C θ (chart (Fin d) x) a κ
            (gradientTolerance (d := d) a κ θ τ),
            KSNumericalGradient.report_isHermitian H A C θ (chart (Fin d) x) a κ
              (gradientTolerance (d := d) a κ θ τ)⟩ :=
      (chartEquiv (Fin d)).apply_symm_apply _
    rw [hg]
    change KSComplexMatrixProjection.report
      ((chart (Fin d) (coordinateRun H A C θ a κ τ hd has x₀ k) : Matrix (Fin d) (Fin d) ℂ) +
        stepSize (d := d) a κ θ • KSNumericalGradient.report H A C θ
          (chart (Fin d) (coordinateRun H A C θ a κ τ hd has x₀ k)) a κ
          (gradientTolerance (d := d) a κ θ τ)) a 1 hd (projectionTolerance (d := d) a κ θ τ) = _
    rw [ih]

/-- Convergence of the actual finite numerical iteration; all gradient,
projection and upper-Hessian obligations have been discharged. -/
theorem coordinateRun_accuracy (H : Matrix (Fin d) (Fin d) ℂ)
    (A : ι → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) {θ a κ τ : ℝ}
    (hθ : 0 < θ) (ha : 0 < a) (hκ : 0 ≤ κ) (hτ : 0 < τ)
    (hd : 0 < d) (has : (d : ℝ) * a ≤ 1)
    (hbudget : (∑ i, (covarianceKraus A C i)ᴴ * covarianceKraus A C i) ≤
      κ • (1 : Matrix (Fin d) (Fin d) ℂ))
    (x₀ xstar : Coordinates (Fin d))
    (hstart : x₀ ∈ KSObjectiveChart.densityFloor (chart (Fin d)) a)
    (hxstar : xstar ∈ KSObjectiveChart.densityFloor (chart (Fin d)) a)
    (hmax : IsMaxOn (KSObjectiveChart.objective H (covarianceKraus A C) θ (chart (Fin d)))
      (KSObjectiveChart.densityFloor (chart (Fin d)) a) xstar) :
    dist (coordinateRun H A C θ a κ τ hd has x₀ (iterationCount (d := d) a κ θ τ)) xstar ≤ τ := by
  have hμ : 0 < θ / 2 := by linarith
  have hμL : θ / 2 ≤ densityL (n := Fin d) a κ θ := le_max_left _ _
  have heg := gradientError_pos hμ hμL hτ
  have hep := projectionError_pos hμ hμL hτ
  let hne := KSCoordinateProjection.densityFloor_nonempty a hd has
  have hproj := KSCoordinateProjection.projectionReport_spec a hd has hep hne
  exact inexact_density_run_accuracy H (covarianceKraus A C) θ hθ (chart (Fin d))
    (chart_trace_square (Fin d)) ha hκ hτ hbudget hne _ _ x₀ xstar hstart hxstar hmax
    hproj.1 (fun k x hx => KSNumericalGradient.coordinateReport_accuracy H A hA hC hθ ha hκ heg
      hbudget k x hx) hproj.2

end MatrixSpencer.KSNumericalDensityRun
