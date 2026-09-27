import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-!
# Continuity of the positive matrix square root

The topology is the matrix topology induced by the Euclidean operator norm.
Continuity holds on the entire positive semidefinite cone, including singular
matrices and zero-dimensional matrices. A local norm bound supplies the compact
spectral interval required by continuity of the functional calculus.
-/

open Matrix
open scoped NNReal Topology MatrixOrder ComplexOrder Matrix.Norms.L2Operator

namespace MatrixSpencer

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The actual positive square root is continuous on the PSD matrix subtype. -/
theorem continuous_matrix_sqrt_psd :
    Continuous (fun A : {A : Matrix n n ℂ // A.PosSemidef} =>
      CFC.sqrt (A : Matrix n n ℂ)) := by
  letI : CStarAlgebra (Matrix n n ℂ) := {}
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
  have h := hval.cfc_nnreal isCompact_Icc NNReal.sqrt hspectrum hnonneg
  simpa only [CFC.sqrt_eq_cfc] using h

/-- No positive-definiteness or lower eigenvalue bound is required. -/
theorem continuousOn_matrix_sqrt_psd :
    ContinuousOn (CFC.sqrt : Matrix n n ℂ → Matrix n n ℂ)
      {A : Matrix n n ℂ | A.PosSemidef} := by
  exact continuousOn_iff_continuous_restrict.mpr continuous_matrix_sqrt_psd

/-- Any continuous family of PSD matrices has a continuous positive square root. -/
theorem continuous_matrix_sqrt_of_psd {X : Type*} [TopologicalSpace X]
    {A : X → Matrix n n ℂ} (hA : Continuous A)
    (hpos : ∀ x, (A x).PosSemidef) :
    Continuous (fun x => CFC.sqrt (A x)) := by
  exact continuous_matrix_sqrt_psd.comp (hA.subtype_mk hpos)

/-- Matrix square roots preserve limits through PSD matrices, even at the boundary. -/
theorem tendsto_matrix_sqrt_of_psd {X : Type*} {l : Filter X}
    {A : X → Matrix n n ℂ} {B : Matrix n n ℂ}
    (hA : Filter.Tendsto A l (𝓝 B))
    (hpos : ∀ᶠ x in l, (A x).PosSemidef) (hB : B.PosSemidef) :
    Filter.Tendsto (fun x => CFC.sqrt (A x)) l (𝓝 (CFC.sqrt B)) := by
  have hwithin : Filter.Tendsto A l (𝓝[{M : Matrix n n ℂ | M.PosSemidef}] B) :=
    tendsto_nhdsWithin_iff.mpr ⟨hA, hpos⟩
  exact (continuousOn_matrix_sqrt_psd B hB).tendsto.comp hwithin

end MatrixSpencer
