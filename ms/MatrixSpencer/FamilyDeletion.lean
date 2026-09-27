import MatrixSpencer.OwnerShavingDerivative

/-! Deleting original matrix labels can only decrease the actual identity-owner potential. -/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace MatrixSpencer
noncomputable section
variable {ι κ n : Type*} [Fintype ι] [Fintype κ] [Fintype n]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq n]

def familyInclusion (e : κ ↪ ι) : Matrix ι κ ℝ := fun i j => if i = e j then 1 else 0

omit [Fintype κ] in
theorem familyInclusion_isometry (e : κ ↪ ι) : (familyInclusion e)ᵀ * familyInclusion e = 1 := by
  ext j k
  simp only [Matrix.mul_apply, Matrix.transpose_apply, familyInclusion, Matrix.one_apply]
  by_cases hjk : j = k
  · subst k
    simp
  · simp [hjk, Ne.symm hjk]

omit [Fintype κ] [Fintype n] [DecidableEq κ] [DecidableEq n] in
theorem mixFamily_familyInclusion (A : ι → Matrix n n ℂ) (e : κ ↪ ι) :
    mixFamily A (familyInclusion e) = fun j => A (e j) := by
  funext j
  simp [mixFamily, familyInclusion, ite_smul]

/-- A coordinate subfamily has no larger actual potential at the same full physical center. -/
theorem ownerPotential_subfamily_le [Nonempty n] (H : Matrix n n ℂ)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) (e : κ ↪ ι) (θ : ℝ) :
    ownerPotential H (fun j => A (e j)) 1 θ ≤ ownerPotential H A 1 θ := by
  rw [← mixFamily_familyInclusion A e, ← ownerPotential_covarianceLift]
  exact ownerPotential_mono_covariance H A hA
    (covarianceLift_posSemidef _ Matrix.PosSemidef.one) Matrix.PosSemidef.one
    (covarianceLift_le_one _ (familyInclusion_isometry e) le_rfl) θ

end
end MatrixSpencer
