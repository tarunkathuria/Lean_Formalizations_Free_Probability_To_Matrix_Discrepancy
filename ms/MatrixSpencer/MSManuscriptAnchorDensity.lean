import MatrixSpencer.KSNumericalOwnerPotential
import MatrixSpencer.OwnerCertificate



open Matrix Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 800000
namespace MatrixSpencer.MSManuscriptAnchorDensity
open KSOwnerOptimizerDomain KSOwnerInputBounds KSFullHermitianChart
open KSComplexProjectionGeometry
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}
local instance : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
local instance : NormedSpace ℝ (selfAdjoint (Matrix (Fin d) (Fin d) ℂ)) := inferInstance

def density (H : Matrix (Fin d) (Fin d) ℂ) (A : ι → Matrix (Fin d) (Fin d) ℂ)
    (C : Matrix ι ι ℝ) (θ τ : ℝ) (hd : 0 < d) : Matrix (Fin d) (Fin d) ℂ :=
  KSNumericalDensityRun.output H A C θ (optimizerFloor H A C θ)
    (krausBudget A C) τ hd (initialDensity hd)

theorem density_feasible (H : Matrix (Fin d) (Fin d) ℂ)
    (A : ι → Matrix (Fin d) (Fin d) ℂ) (C : Matrix ι ι ℝ) (θ τ : ℝ) (hd : 0 < d) :
    ComplexFeasible (optimizerFloor H A C θ) 1 (density H A C θ τ hd) :=
  KSNumericalDensityRun.run_feasible H A C θ _ _ _ hd
    (optimizerFloor_scaled_le_one H A C θ) (initialDensity hd)
    ⟨(initialDensity hd).property, initialDensity_mem_floor H A C θ hd⟩ _

theorem density_coordinates (H : Matrix (Fin d) (Fin d) ℂ) (hH : H.IsHermitian)
    (A : ι → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) {θ τ : ℝ} (hθ : 0 < θ) (hτ : 0 < τ)
    (hd : 0 < d) : ∃ y : Coordinates (Fin d),
      (chart (Fin d) y : Matrix (Fin d) (Fin d) ℂ) = density H A C θ τ hd ∧
      dist y (optimizerCoordinates H A C θ hd) ≤ τ := by
  let a := optimizerFloor H A C θ
  let κ := krausBudget A C
  have has : (d : ℝ) * a ≤ 1 := optimizerFloor_scaled_le_one H A C θ
  let x₀ := initialCoordinates hd
  let k := KSNumericalDensityRun.iterationCount (d := d) a κ θ τ
  let y := KSNumericalDensityRun.coordinateRun H A C θ a κ τ hd has x₀ k
  refine ⟨y, ?_, ?_⟩
  · have hh := KSNumericalDensityRun.coordinateRun_physical H A C θ a κ τ hd has x₀ k
    have hinit : chart (Fin d) x₀ = initialDensity hd := (chartEquiv (Fin d)).apply_symm_apply _
    rw [hinit] at hh
    exact hh
  · exact KSNumericalDensityRun.coordinateRun_accuracy H A hA hC hθ
      (optimizerFloor_pos H A C hθ hd) (krausBudget_pos A C).le hτ hd has
      (covarianceKraus_budget A hA hC) x₀ (optimizerCoordinates H A C θ hd)
      (initialCoordinates_mem_floor H A C θ hd)
      (optimizerCoordinates_mem_floor H hH A hA hC hθ hd)
      (optimizer_isMaxOn_objective H hH A hA hC hθ hd)

theorem density_accuracy (H : Matrix (Fin d) (Fin d) ℂ) (hH : H.IsHermitian)
    (A : ι → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) {θ τ : ℝ} (hθ : 0 < θ) (hτ : 0 < τ)
    (hd : 0 < d) :
    Real.sqrt (matrixEnergy (density H A C θ τ hd - (optimizer H A C θ hd : Matrix (Fin d) (Fin d) ℂ))) ≤ τ := by
  obtain ⟨y, hy, hdist⟩ := density_coordinates H hH A hA hC hθ hτ hd
  let xstar := optimizerCoordinates H A C θ hd
  have hs : chart (Fin d) xstar = optimizer H A C θ hd := (chartEquiv (Fin d)).apply_symm_apply _
  have he : (chart (Fin d) (y-xstar) : Matrix (Fin d) (Fin d) ℂ) =
      density H A C θ τ hd - (optimizer H A C θ hd : Matrix (Fin d) (Fin d) ℂ) := by
    rw [map_sub]
    change (chart (Fin d) y : Matrix (Fin d) (Fin d) ℂ) - chart (Fin d) xstar = _
    rw [hy, hs]
  rw [← he, matrixEnergy_eq_trace_square _ (chart (Fin d) (y-xstar)).property,
    chart_trace_square, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
  exact hdist

def emptyFamily : Empty → Matrix (Fin d) (Fin d) ℂ := fun _ => 0

/-- The saved density is actually computed at the saved center. -/
def saved (Hstar : Matrix (Fin d) (Fin d) ℂ) (θ τ : ℝ) (hd : 0 < d) :
    Matrix (Fin d) (Fin d) ℂ := density Hstar emptyFamily 0 θ τ hd

theorem empty_optimizer_eq [Nonempty (Fin d)] (Hstar : Matrix (Fin d) (Fin d) ℂ) (θ : ℝ) (hd : 0 < d) :
    (optimizer Hstar emptyFamily 0 θ hd : Matrix (Fin d) (Fin d) ℂ) =
      ownerCertificateDensity Hstar θ := by
  have hB : covarianceKraus (emptyFamily (d := d)) 0 = emptyFamily := by
    funext i
    exact i.elim
  change densityOptimizer Hstar (covarianceKraus emptyFamily 0) θ = _
  rw [hB]
  rfl

theorem saved_accuracy [Nonempty (Fin d)] (Hstar : Matrix (Fin d) (Fin d) ℂ) (hH : Hstar.IsHermitian)
    {θ τ : ℝ} (hθ : 0 < θ) (hτ : 0 < τ) (hd : 0 < d) :
    Real.sqrt (matrixEnergy (saved Hstar θ τ hd -
      ownerCertificateDensity Hstar θ)) ≤ τ := by
  rw [← empty_optimizer_eq]
  exact density_accuracy Hstar hH emptyFamily (fun i => i.elim) Matrix.PosSemidef.zero hθ hτ hd

theorem saved_mem_densitySet (Hstar : Matrix (Fin d) (Fin d) ℂ)
    {θ : ℝ} (hθ : 0 < θ) (τ : ℝ) (hd : 0 < d) : saved Hstar θ τ hd ∈ densitySet := by
  have hf := density_feasible Hstar emptyFamily 0 θ τ hd
  refine ⟨?_, hf.2.2⟩
  have hp := (Matrix.PosSemidef.one.smul
    (optimizerFloor_pos Hstar emptyFamily 0 hθ hd).le).add (Matrix.le_iff.mp hf.2.1)
  simpa only [add_sub_cancel] using hp

/-- Trace pairing is controlled by the two entry-computed Frobenius norms. -/
theorem trace_pairing_bound (X Y : Matrix (Fin d) (Fin d) ℂ)
    (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    |realTrace (X*Y)| ≤ Real.sqrt (matrixEnergy X) * Real.sqrt (matrixEnergy Y) := by
  let x := (chartEquiv (Fin d)).symm ⟨X, hX⟩
  let y := (chartEquiv (Fin d)).symm ⟨Y, hY⟩
  have hx : (chart (Fin d) x : Matrix (Fin d) (Fin d) ℂ) = X :=
    congrArg Subtype.val ((chartEquiv (Fin d)).apply_symm_apply ⟨X,hX⟩)
  have hy : (chart (Fin d) y : Matrix (Fin d) (Fin d) ℂ) = Y :=
    congrArg Subtype.val ((chartEquiv (Fin d)).apply_symm_apply ⟨Y,hY⟩)
  rw [← hx, ← hy, chart_trace_pairing,
    matrixEnergy_eq_trace_square _ (chart (Fin d) x).property,
    matrixEnergy_eq_trace_square _ (chart (Fin d) y).property,
    chart_trace_square, chart_trace_square, Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs,
    abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)]
  exact abs_real_inner_le_norm _ _

theorem saved_tangent_error [Nonempty (Fin d)] (Hstar : Matrix (Fin d) (Fin d) ℂ) (hH : Hstar.IsHermitian)
    {θ τ : ℝ} (hθ : 0 < θ) (hτ : 0 < τ) (hd : 0 < d)
    (D : Matrix (Fin d) (Fin d) ℂ) (hD : D.IsHermitian) :
    |realTrace (saved Hstar θ τ hd * D) -
      realTrace (ownerCertificateDensity Hstar θ * D)| ≤
      τ * Real.sqrt (matrixEnergy D) := by
  rw [← realTrace_sub, ← Matrix.sub_mul]
  have hs := (saved_mem_densitySet Hstar hθ τ hd).1.isHermitian
  have ht := (ownerCertificateDensity_mem Hstar θ).1.isHermitian
  exact (trace_pairing_bound _ D (hs.sub ht) hD).trans
    (mul_le_mul_of_nonneg_right (saved_accuracy Hstar hH hθ hτ hd) (Real.sqrt_nonneg _))

end MatrixSpencer.MSManuscriptAnchorDensity
