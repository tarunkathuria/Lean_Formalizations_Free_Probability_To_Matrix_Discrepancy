import ExistenceKS.ExactValue
import ExistenceKS.InputTransfer
import RadialKS.EndToEnd

/-! Pure existence through the new deterministic radial walk.
The exact value specification is constructed in this package. Neither a
solver, a runtime promise, nor an analytic walk certificate is quantified
in either endpoint below. -/
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace ExistenceKS
open MatrixSpencer

theorem exists_signing : Frozen.radialTarget := by
  apply InputTransfer.close_target_of_positive_dimension 35 (by norm_num)
  intro N d hd ε hε v hp hsize
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  have h := RadialKS.EndToEnd.guarantee ExactValue.specification v hd hp hε hsize
  exact ⟨RadialKS.Run.output ExactValue.specification v hd hp,h.1,h.2.1⟩


theorem exists_signing_manuscript : Frozen.manuscriptTarget := by
  intro N d ε hε v hp hsize
  obtain ⟨s,hs,hbound⟩ := exists_signing N d ε hε v hp hsize
  refine ⟨s,hs,hbound.trans ?_⟩
  exact mul_le_mul_of_nonneg_right (by norm_num : (35 : ℝ) ≤ 400) (Real.sqrt_nonneg ε)

end ExistenceKS
