import MatrixSpencer.KSFullHermitianChart

/-!
# The full trace-zero Frobenius density chart

The coordinate space is the trace kernel in the already established full
Hermitian Frobenius space. Its embedding has exactly the physical trace-square
norm. Linear trace removal gives coordinates for every trace-one Hermitian
matrix, and in particular for the actual canonical density optimizer.
-/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
noncomputable section
namespace MatrixSpencer.KSFrobeniusTangent
variable (n : Type*) [Fintype n] [DecidableEq n]
local instance : CStarAlgebra (Matrix n n ℂ) := {}
local instance : NormedAddCommGroup (selfAdjoint (Matrix n n ℂ)) := inferInstance
local instance : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance
local instance : FiniteDimensional ℝ (selfAdjoint (Matrix n n ℂ)) :=
  inferInstanceAs (FiniteDimensional ℝ (selfAdjoint.submodule ℝ (Matrix n n ℂ)))

/-- Trace in the full real Frobenius coordinates. -/
def traceCLM : KSFullHermitianChart.Frobenius n →L[ℝ] ℝ :=
  realTraceCLM.comp (hermitianInclusion.comp (KSFullHermitianChart.physicalEquiv n).toContinuousLinearMap)

/-- The full trace-zero Frobenius space, with its inherited Hilbert norm. -/
def tangent : Submodule ℝ (KSFullHermitianChart.Frobenius n) := LinearMap.ker (traceCLM n).toLinearMap
abbrev Coordinates := ↥(tangent n)
local instance : NormedAddCommGroup (Coordinates n) := inferInstance
local instance : NormedSpace ℝ (Coordinates n) := inferInstance

/-- Physical embedding; the physical codomain keeps its operator norm. -/
def embedding : Coordinates n →L[ℝ] selfAdjoint (Matrix n n ℂ) :=
  (KSFullHermitianChart.physicalEquiv n).toContinuousLinearMap.comp (tangent n).subtypeL

theorem embedding_trace (u : Coordinates n) : realTrace (embedding n u : Matrix n n ℂ) = 0 :=
  u.property

theorem embedding_trace_square (u : Coordinates n) :
    realTrace ((embedding n u : Matrix n n ℂ) * (embedding n u : Matrix n n ℂ)) = ‖u‖ ^ 2 :=
  KSFullHermitianChart.physicalEquiv_trace_square n u.val

variable [Nonempty n]

def center : selfAdjoint (Matrix n n ℂ) := ⟨maximallyMixed, maximallyMixed_posDef.isHermitian⟩

theorem center_trace : realTrace (center n : Matrix n n ℂ) = 1 := maximallyMixed_mem_densitySet.2

/-- Affine parametrization of the entire trace-one Hermitian hyperplane. -/
def chart (u : Coordinates n) : selfAdjoint (Matrix n n ℂ) := center n + embedding n u

/-- The actual linear trace-removal projection, expressed in Frobenius coordinates. -/
def project : selfAdjoint (Matrix n n ℂ) →L[ℝ] Coordinates n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => ⟨(KSFullHermitianChart.physicalEquiv n).symm
        (X - realTrace (X : Matrix n n ℂ) • center n), by
          change realTrace ((KSFullHermitianChart.physicalEquiv n
            ((KSFullHermitianChart.physicalEquiv n).symm
              (X - realTrace (X : Matrix n n ℂ) • center n))) : Matrix n n ℂ) = 0
          rw [ContinuousLinearEquiv.apply_symm_apply]
          change realTrace ((X : Matrix n n ℂ) - realTrace (X : Matrix n n ℂ) • (center n : Matrix n n ℂ)) = 0
          rw [realTrace_sub, realTrace_smul, center_trace, mul_one, sub_self]⟩
      map_add' := by
        intro X Y
        apply Subtype.ext
        change (KSFullHermitianChart.physicalEquiv n).symm _ =
          (KSFullHermitianChart.physicalEquiv n).symm _ + (KSFullHermitianChart.physicalEquiv n).symm _
        rw [← map_add]
        congr 1
        change X + Y - realTrace ((X : Matrix n n ℂ) + (Y : Matrix n n ℂ)) • center n = _
        rw [realTrace_add, add_smul]
        abel
      map_smul' := by
        intro r X
        apply Subtype.ext
        change (KSFullHermitianChart.physicalEquiv n).symm _ =
          r • (KSFullHermitianChart.physicalEquiv n).symm _
        rw [← map_smul]
        congr 1
        change r • X - realTrace (r • (X : Matrix n n ℂ)) • center n = _
        rw [realTrace_smul, smul_sub, smul_smul] }

theorem embedding_project (X : selfAdjoint (Matrix n n ℂ)) :
    embedding n (project n X) = X - realTrace (X : Matrix n n ℂ) • center n :=
  (KSFullHermitianChart.physicalEquiv n).apply_symm_apply _

theorem chart_project_of_trace_one (X : selfAdjoint (Matrix n n ℂ))
    (hX : realTrace (X : Matrix n n ℂ) = 1) : chart n (project n X) = X := by
  rw [chart, embedding_project, hX, one_smul]
  abel

theorem chart_trace (u : Coordinates n) : realTrace (chart n u : Matrix n n ℂ) = 1 := by
  change realTrace ((center n : Matrix n n ℂ) + (embedding n u : Matrix n n ℂ)) = 1
  rw [realTrace_add, center_trace, embedding_trace, add_zero]

theorem hasFDerivAt_chart (u : Coordinates n) : HasFDerivAt (chart n) (embedding n) u := by
  simpa only [zero_add] using (hasFDerivAt_const (𝕜 := ℝ) (center n) u).add (embedding n).hasFDerivAt

theorem contDiff_chart : ContDiff ℝ ∞ (chart n) := contDiff_const.add (embedding n).contDiff

end MatrixSpencer.KSFrobeniusTangent
