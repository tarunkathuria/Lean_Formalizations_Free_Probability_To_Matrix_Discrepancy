import MatrixSpencer.DyadicOptimizerResponse

/-! The actual supremum potential is smooth and its second derivative is the
proved optimizer response, for all source ranks. -/
open Matrix Filter Topology
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
namespace MatrixSpencer
noncomputable section
set_option maxHeartbeats 800000
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
local instance dyadicPotentialResponseCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance dyadicPotentialResponseSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance
local instance dyadicPotentialResponseFinite : FiniteDimensional ℝ (selfAdjoint (Matrix n n ℂ)) :=
  inferInstanceAs (FiniteDimensional ℝ (selfAdjoint.submodule ℝ (Matrix n n ℂ)))
local instance dyadicPotentialResponseTangentGroup : NormedAddCommGroup (densityTangent (n := n)) := inferInstance
local instance dyadicPotentialResponseTangentSpace : NormedSpace ℝ (densityTangent (n := n)) := inferInstance
local instance dyadicPotentialResponseTangentFinite : FiniteDimensional ℝ (densityTangent (n := n)) := inferInstance
local instance dyadicPotentialResponseTangentComplete : CompleteSpace (densityTangent (n := n)) := FiniteDimensional.complete ℝ _
local instance dyadicPotentialResponseDualGroup : NormedAddCommGroup (densityTangent (n := n) →L[ℝ] ℝ) := inferInstance
local instance dyadicPotentialResponseDualSpace : NormedSpace ℝ (densityTangent (n := n) →L[ℝ] ℝ) := inferInstance

theorem contDiffAt_hermitianDyadicDensityPotential [Nonempty n]
    (H : selfAdjoint (Matrix n n ℂ)) (B : ι → Matrix n n ℂ) (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (hθ : 0 < θ) :
    ContDiffAt ℝ ∞ (hermitianDyadicDensityPotential B m θ) H := by
  have hs := contDiffAt_hermitianDyadicDensityOptimizer H B m hm θ hθ
  have hmat := (hermitianInclusion (n := n)).contDiff.contDiffAt.comp H hs
  have hlinear := realTraceCLM.contDiff.contDiffAt.comp H
    ((hermitianInclusion (n := n)).contDiff.contDiffAt.mul hmat)
  have hf := (contDiffAt_krausSourceFidelity_source_unrestricted B (hermitianDyadicDensityOptimizer (H : Matrix n n ℂ) B m θ)
    (hermitianDyadicDensityOptimizer_posDef (H : Matrix n n ℂ) B m hm θ hθ)
).comp H hs
  have ht := (contDiffAt_dyadicTsallisPotential m θ (hermitianDyadicDensityOptimizer (H : Matrix n n ℂ) B m θ)
    (hermitianDyadicDensityOptimizer_posDef (H : Matrix n n ℂ) B m hm θ hθ)).comp H hs
  apply ((hlinear.add hf).add ht).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun K => hermitianDyadicDensityPotential_eq_objective K B m θ

/-- The genuine supremum potential has the actual optimizer as its trace gradient. -/
theorem hasFDerivAt_hermitianDyadicDensityPotential [Nonempty n]
    (H : selfAdjoint (Matrix n n ℂ)) (B : ι → Matrix n n ℂ) (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (hθ : 0 < θ) :
    HasFDerivAt (hermitianDyadicDensityPotential B m θ) (tracePairing (dyadicDensityOptimizer (H : Matrix n n ℂ) B m θ)) H := by
  have hd := ((contDiffAt_hermitianDyadicDensityPotential H B m hm θ hθ).differentiableAt
    (by simp : (1 : WithTop ℕ∞) ≤ ∞)).hasFDerivAt
  let L := tracePairing (dyadicDensityOptimizer (H : Matrix n n ℂ) B m θ)
  have hmin : IsLocalMin (fun K => hermitianDyadicDensityPotential B m θ K - L K) H := by
    apply Filter.Eventually.of_forall
    intro K
    have h := dyadicDensityPotential_supporting_plane (H : Matrix n n ℂ) (K : Matrix n n ℂ) B m θ
      (S := dyadicDensityOptimizer (H : Matrix n n ℂ) B m θ)
      (dyadicDensityOptimizer_mem (H : Matrix n n ℂ) B m θ)
      (dyadicDensityOptimizer_isMaxOn (H : Matrix n n ℂ) B m θ)
    rw [realTrace_mul_comm] at h
    change dyadicDensityPotential H B m θ + L (K - H) ≤ dyadicDensityPotential K B m θ at h
    rw [map_sub] at h
    change dyadicDensityPotential H B m θ - L H ≤ dyadicDensityPotential K B m θ - L K
    linarith
  have hz := hmin.hasFDerivAt_eq_zero (hd.sub L.hasFDerivAt)
  rwa [sub_eq_zero.mp hz] at hd

theorem hasStrictFDerivAt_hermitianDyadicDensityPotential [Nonempty n]
    (H : selfAdjoint (Matrix n n ℂ)) (B : ι → Matrix n n ℂ) (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (hθ : 0 < θ) :
    HasStrictFDerivAt (hermitianDyadicDensityPotential B m θ) (tracePairing (dyadicDensityOptimizer (H : Matrix n n ℂ) B m θ)) H :=
  (contDiffAt_hermitianDyadicDensityPotential H B m hm θ hθ).hasStrictFDerivAt'
    (hasFDerivAt_hermitianDyadicDensityPotential H B m hm θ hθ) (by simp)

theorem hasStrictFDerivAt_fderiv_hermitianDyadicDensityPotential [Nonempty n]
    (H : selfAdjoint (Matrix n n ℂ)) (B : ι → Matrix n n ℂ) (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (hθ : 0 < θ) :
    HasStrictFDerivAt (fun K => fderiv ℝ (hermitianDyadicDensityPotential B m θ) K)
      ((tracePairing.comp hermitianInclusion).comp
        (dyadicDensityResponseDerivative (H : Matrix n n ℂ) B m hm θ hθ (hermitianDyadicDensityOptimizer (H : Matrix n n ℂ) B m θ)
          (hermitianDyadicDensityOptimizer_posDef (H : Matrix n n ℂ) B m hm θ hθ)
)) H := by
  have hs := hasStrictFDerivAt_hermitianDyadicDensityOptimizer H B m hm θ hθ
  have hd := (tracePairing.comp (hermitianInclusion (n := n))).hasStrictFDerivAt.comp H hs
  apply hd.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun K =>
    (hasFDerivAt_hermitianDyadicDensityPotential K B m hm θ hθ).fderiv.symm

/-- The actual potential Hessian is the trace pairing with the proved optimizer response. -/
theorem fderiv_fderiv_hermitianDyadicDensityPotential_apply [Nonempty n]
    (H X Y : selfAdjoint (Matrix n n ℂ)) (B : ι → Matrix n n ℂ) (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (hθ : 0 < θ) :
    fderiv ℝ (fun K => fderiv ℝ (hermitianDyadicDensityPotential B m θ) K) H X Y =
      realTrace ((dyadicDensityResponseDerivative (H : Matrix n n ℂ) B m hm θ hθ (hermitianDyadicDensityOptimizer (H : Matrix n n ℂ) B m θ)
        (hermitianDyadicDensityOptimizer_posDef (H : Matrix n n ℂ) B m hm θ hθ)
       X : Matrix n n ℂ) * (Y : Matrix n n ℂ)) := by
  rw [(hasStrictFDerivAt_fderiv_hermitianDyadicDensityPotential H B m hm θ hθ).hasFDerivAt.fderiv]
  rfl

theorem dyadicDensityResponseDerivative_trace (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (hθ : 0 < θ) (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef)
    (X : selfAdjoint (Matrix n n ℂ)) :
    realTrace (dyadicDensityResponseDerivative H B m hm θ hθ S hS X : Matrix n n ℂ) = 0 :=
  (mem_densityTangent_iff _).mp
    ((dyadicDensityTangentHessianEquiv H B m hm θ hθ S hS).symm (densityCenterFunctional X)).property

theorem dyadicDensityResponseDerivative_quadratic_nonneg (H : Matrix n n ℂ)
    (B : ι → Matrix n n ℂ) (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (hθ : 0 < θ) (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef)
    (X : selfAdjoint (Matrix n n ℂ)) :
    0 ≤ realTrace ((dyadicDensityResponseDerivative H B m hm θ hθ S hS X : Matrix n n ℂ) *
      (X : Matrix n n ℂ)) := by
  let U := (dyadicDensityTangentHessianEquiv H B m hm θ hθ S hS).symm (densityCenterFunctional X)
  have hrep : dyadicDensityTangentNegativeHessian H B m θ S U U = densityCenterFunctional X U := by
    change dyadicDensityTangentHessianEquiv H B m hm θ hθ S hS U U = _
    dsimp only [U]
    rw [ContinuousLinearEquiv.apply_symm_apply]
  rw [realTrace_mul_comm]
  change 0 ≤ densityCenterFunctional X U
  by_cases hU : U = 0
  · rw [hU]
    exact le_of_eq ((densityCenterFunctional X).map_zero).symm
  · rw [← hrep]
    exact (dyadicDensityTangentNegativeHessian_pos H B m hm θ hθ S hS U hU).le

theorem fderiv_fderiv_hermitianDyadicDensityPotential_quadratic_nonneg [Nonempty n]
    (H X : selfAdjoint (Matrix n n ℂ)) (B : ι → Matrix n n ℂ) (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (hθ : 0 < θ) :
    0 ≤ fderiv ℝ (fun K => fderiv ℝ (hermitianDyadicDensityPotential B m θ) K) H X X := by
  rw [fderiv_fderiv_hermitianDyadicDensityPotential_apply H X X B m hm θ hθ ]
  exact dyadicDensityResponseDerivative_quadratic_nonneg (H : Matrix n n ℂ) B m hm θ hθ
    (hermitianDyadicDensityOptimizer (H : Matrix n n ℂ) B m θ)
    (hermitianDyadicDensityOptimizer_posDef (H : Matrix n n ℂ) B m hm θ hθ)
     X

/-- Global smoothness of the actual optimizer in its Hermitian center. -/
theorem contDiff_hermitianDyadicDensityOptimizer [Nonempty n]
    (B : ι → Matrix n n ℂ) (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (hθ : 0 < θ) :
    ContDiff ℝ ∞ (fun H : selfAdjoint (Matrix n n ℂ) =>
      hermitianDyadicDensityOptimizer (H : Matrix n n ℂ) B m θ) :=
  contDiff_iff_contDiffAt.mpr fun H => contDiffAt_hermitianDyadicDensityOptimizer H B m hm θ hθ

/-- Global smoothness of the actual supremum potential, with no source-rank restriction. -/
theorem contDiff_hermitianDyadicDensityPotential [Nonempty n]
    (B : ι → Matrix n n ℂ) (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (hθ : 0 < θ) :
    ContDiff ℝ ∞ (hermitianDyadicDensityPotential B m θ) :=
  contDiff_iff_contDiffAt.mpr fun H => contDiffAt_hermitianDyadicDensityPotential H B m hm θ hθ

end
end MatrixSpencer
