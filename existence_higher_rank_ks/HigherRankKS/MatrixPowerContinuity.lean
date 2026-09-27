import MatrixSpencer.SqrtContinuity

/-!
# Positive matrix powers

Continuity of fixed nonnegative real powers on the whole PSD cone.
-/

open Matrix Filter MeasureTheory Set
open scoped NNReal Topology MatrixOrder ComplexOrder Matrix.Norms.L2Operator

noncomputable section
namespace HigherRankKS

variable {n : Type*} [Fintype n] [DecidableEq n]
local instance matrixPowerContinuityCStar : CStarAlgebra (Matrix n n ℂ) := {}

/-- Fixed nonnegative real powers are continuous on the whole PSD cone. -/
theorem continuous_matrix_rpow_psd {p : ℝ} (hp : 0 ≤ p) :
    Continuous (fun A : {A : Matrix n n ℂ // A.PosSemidef} =>
      CFC.rpow (A : Matrix n n ℂ) p) := by
  rw [continuous_iff_continuousAt]
  intro A
  have hval : ContinuousAt
      (fun B : {B : Matrix n n ℂ // B.PosSemidef} => (B : Matrix n n ℂ)) A :=
    continuous_subtype_val.continuousAt
  have hnorm : ∀ᶠ B : {B : Matrix n n ℂ // B.PosSemidef} in 𝓝 A,
      ‖(B : Matrix n n ℂ)‖₊ < ‖(A : Matrix n n ℂ)‖₊ + 1 :=
    (continuous_nnnorm.comp continuous_subtype_val).continuousAt.eventually
      (gt_mem_nhds (lt_add_of_pos_right _ zero_lt_one))
  have hspectrum : ∀ᶠ B : {B : Matrix n n ℂ // B.PosSemidef} in 𝓝 A,
      spectrum ℝ≥0 (B : Matrix n n ℂ) ⊆
        Set.Icc 0 (‖(A : Matrix n n ℂ)‖₊ + 1) := by
    filter_upwards [hnorm] with B hB
    intro r hr
    exact ⟨zero_le r,
      (IsometricContinuousFunctionalCalculus.spectrum_le
        (B : Matrix n n ℂ) hr B.property.nonneg).trans hB.le⟩
  have hnonneg : ∀ᶠ B : {B : Matrix n n ℂ // B.PosSemidef} in 𝓝 A,
      (0 : Matrix n n ℂ) ≤ (B : Matrix n n ℂ) :=
    Filter.Eventually.of_forall (fun B => B.property.nonneg)
  have h := hval.cfc_nnreal isCompact_Icc (fun r : ℝ≥0 => r ^ p) hspectrum hnonneg
    (hf := (NNReal.continuous_rpow_const hp).continuousOn)
  simpa only [CFC.rpow_def] using h

theorem continuous_matrix_rpow_of_psd {X : Type*} [TopologicalSpace X]
    {A : X → Matrix n n ℂ} (hA : Continuous A) (hpos : ∀ x, (A x).PosSemidef)
    {p : ℝ} (hp : 0 ≤ p) : Continuous (fun x => CFC.rpow (A x) p) :=
  (continuous_matrix_rpow_psd hp).comp (hA.subtype_mk hpos)

end HigherRankKS
