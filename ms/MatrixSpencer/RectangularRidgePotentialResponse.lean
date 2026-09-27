import MatrixSpencer.RectangularRidgeOptimizerResponse

/-! Smoothness and the exact Hessian of the actual optimized mixed potential.
The optimizer is differentiated through its trace-constrained stationarity
equation, including singular Kraus sources. -/
open Matrix Filter Topology
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
noncomputable section
namespace MatrixSpencer.RectangularRidgeCalculus
open RectangularRidgePotential
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
local instance ridgePotentialResponseLocal1 : CStarAlgebra (Matrix n n ℂ) := {}
local instance ridgePotentialResponseLocal2 : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance
local instance ridgePotentialResponseLocal3 : FiniteDimensional ℝ (selfAdjoint (Matrix n n ℂ)) :=
  inferInstanceAs (FiniteDimensional ℝ (selfAdjoint.submodule ℝ (Matrix n n ℂ)))
local instance ridgePotentialResponseLocal4 : NormedAddCommGroup (densityTangent (n := n)) := inferInstance
local instance ridgePotentialResponseLocal5 : NormedSpace ℝ (densityTangent (n := n)) := inferInstance
local instance ridgePotentialResponseLocal6 : NormedAddCommGroup (densityTangent (n := n) →L[ℝ] ℝ) := inferInstance
local instance ridgePotentialResponseLocal7 : NormedSpace ℝ (densityTangent (n := n) →L[ℝ] ℝ) := inferInstance
set_option maxHeartbeats 300000
attribute [local irreducible] RectangularRidgePotential.optimizer

def hermitianPotential (B : ι → Matrix n n ℂ) (m : ℕ) (θ κ : ℝ)
    (H : selfAdjoint (Matrix n n ℂ)) : ℝ := potential H B m θ κ

theorem hermitianPotential_eq_objective [Nonempty n] (H : selfAdjoint (Matrix n n ℂ))
    (B : ι → Matrix n n ℂ) (m : ℕ) (θ κ : ℝ) :
    hermitianPotential B m θ κ H = hermitianObjective H B m θ κ (hermitianOptimizer (H : Matrix n n ℂ) B m θ κ) := by
  change potential (H : Matrix n n ℂ) B m θ κ = objective (H : Matrix n n ℂ) B m θ κ (optimizer (H : Matrix n n ℂ) B m θ κ)
  exact potential_eq_optimizer (H : Matrix n n ℂ) B m θ κ

theorem contDiffAt_hermitianPotential [Nonempty n] (H : selfAdjoint (Matrix n n ℂ))
    (B : ι → Matrix n n ℂ) (m : ℕ) (hm : 1 ≤ m) (θ κ : ℝ)
    (hθ : 0 < θ) (hκ : 0 < κ) : ContDiffAt ℝ ∞ (hermitianPotential B m θ κ) H := by
  have hs := contDiffAt_hermitianOptimizer H B m hm θ κ hθ hκ
  have hp := hermitianOptimizer_posDef (H : Matrix n n ℂ) B m hm θ κ hθ hκ
  have hmat := (hermitianInclusion (n := n)).contDiff.contDiffAt.comp H hs
  have hl := realTraceCLM.contDiff.contDiffAt.comp H
    ((hermitianInclusion (n := n)).contDiff.contDiffAt.mul hmat)
  have hf := (contDiffAt_krausSourceFidelity_source_unrestricted B
    (hermitianOptimizer (H : Matrix n n ℂ) B m θ κ) hp).comp H hs
  have hd := (contDiffAt_dyadicTsallisPotential m θ (hermitianOptimizer (H : Matrix n n ℂ) B m θ κ) hp).comp H hs
  have hr := (contDiffAt_tsallisPotential κ (hermitianOptimizer (H : Matrix n n ℂ) B m θ κ) hp).comp H hs
  apply (((hl.add hf).add hd).add hr).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun K => hermitianPotential_eq_objective K B m θ κ

theorem potential_supporting_plane [Nonempty n] (H K : Matrix n n ℂ)
    (B : ι → Matrix n n ℂ) (m : ℕ) (θ κ : ℝ) :
    potential H B m θ κ + realTrace ((K - H) * optimizer (H : Matrix n n ℂ) B m θ κ) ≤ potential K B m θ κ := by
  have ht := objective_le_potential K B m θ κ (optimizer_mem H B m θ κ)
  rw [potential_eq_optimizer (H : Matrix n n ℂ) B m θ κ]
  have he : objective H B m θ κ (optimizer (H : Matrix n n ℂ) B m θ κ) +
      realTrace ((K - H) * optimizer (H : Matrix n n ℂ) B m θ κ) = objective K B m θ κ (optimizer (H : Matrix n n ℂ) B m θ κ) := by
    simp only [objective, dyadicDensityObjective, Matrix.sub_mul, realTrace_sub]
    ring
  rw [he]
  exact ht

theorem hasFDerivAt_hermitianPotential [Nonempty n] (H : selfAdjoint (Matrix n n ℂ))
    (B : ι → Matrix n n ℂ) (m : ℕ) (hm : 1 ≤ m) (θ κ : ℝ)
    (hθ : 0 < θ) (hκ : 0 < κ) :
    HasFDerivAt (hermitianPotential B m θ κ) (tracePairing (optimizer (H : Matrix n n ℂ) B m θ κ)) H := by
  have hd := ((contDiffAt_hermitianPotential H B m hm θ κ hθ hκ).differentiableAt
    (by simp : (1 : WithTop ℕ∞) ≤ ∞)).hasFDerivAt
  let L := tracePairing (optimizer (H : Matrix n n ℂ) B m θ κ)
  have hl : IsLocalMin (fun K => hermitianPotential B m θ κ K - L K) H := by
    apply Filter.Eventually.of_forall
    intro K
    have ht := potential_supporting_plane (H : Matrix n n ℂ) (K : Matrix n n ℂ) B m θ κ
    rw [realTrace_mul_comm] at ht
    change potential H B m θ κ + L (K - H) ≤ potential K B m θ κ at ht
    rw [map_sub] at ht
    change potential H B m θ κ - L H ≤ potential K B m θ κ - L K
    linarith
  have hz := hl.hasFDerivAt_eq_zero (hd.sub L.hasFDerivAt)
  rwa [sub_eq_zero.mp hz] at hd

theorem hasStrictFDerivAt_fderiv_hermitianPotential [Nonempty n]
    (H : selfAdjoint (Matrix n n ℂ)) (B : ι → Matrix n n ℂ)
    (m : ℕ) (hm : 1 ≤ m) (θ κ : ℝ) (hθ : 0 < θ) (hκ : 0 < κ) :
    HasStrictFDerivAt (fun K => fderiv ℝ (hermitianPotential B m θ κ) K)
      ((tracePairing.comp hermitianInclusion).comp
        (responseDerivative (H : Matrix n n ℂ) B m hm θ κ hθ hκ (hermitianOptimizer (H : Matrix n n ℂ) B m θ κ)
          (hermitianOptimizer_posDef (H : Matrix n n ℂ) B m hm θ κ hθ hκ))) H := by
  have hs := hasStrictFDerivAt_hermitianOptimizer H B m hm θ κ hθ hκ
  have hd := (tracePairing.comp (hermitianInclusion (n := n))).hasStrictFDerivAt.comp H hs
  apply hd.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun K =>
    (hasFDerivAt_hermitianPotential K B m hm θ κ hθ hκ).fderiv.symm

theorem fderiv_fderiv_hermitianPotential_apply [Nonempty n]
    (H X Y : selfAdjoint (Matrix n n ℂ)) (B : ι → Matrix n n ℂ)
    (m : ℕ) (hm : 1 ≤ m) (θ κ : ℝ) (hθ : 0 < θ) (hκ : 0 < κ) :
    fderiv ℝ (fun K => fderiv ℝ (hermitianPotential B m θ κ) K) H X Y =
      realTrace ((responseDerivative (H : Matrix n n ℂ) B m hm θ κ hθ hκ (hermitianOptimizer (H : Matrix n n ℂ) B m θ κ)
        (hermitianOptimizer_posDef (H : Matrix n n ℂ) B m hm θ κ hθ hκ) X : Matrix n n ℂ) * (Y : Matrix n n ℂ)) := by
  rw [(hasStrictFDerivAt_fderiv_hermitianPotential H B m hm θ κ hθ hκ).hasFDerivAt.fderiv]
  rfl

theorem potential_hessian_eq_inverse [Nonempty n]
    (H X : selfAdjoint (Matrix n n ℂ)) (B : ι → Matrix n n ℂ)
    (m : ℕ) (hm : 1 ≤ m) (θ κ : ℝ) (hθ : 0 < θ) (hκ : 0 < κ) :
    fderiv ℝ (fun K => fderiv ℝ (hermitianPotential B m θ κ) K) H X X =
      densityCenterFunctional X
        ((tangentHessianEquiv (H : Matrix n n ℂ) B m hm θ κ hθ hκ (hermitianOptimizer (H : Matrix n n ℂ) B m θ κ)
          (hermitianOptimizer_posDef (H : Matrix n n ℂ) B m hm θ κ hθ hκ)).symm (densityCenterFunctional X)) := by
  rw [fderiv_fderiv_hermitianPotential_apply H X X B m hm θ κ hθ hκ, realTrace_mul_comm]
  rfl

theorem potential_hessian_nonneg [Nonempty n]
    (H X : selfAdjoint (Matrix n n ℂ)) (B : ι → Matrix n n ℂ)
    (m : ℕ) (hm : 1 ≤ m) (θ κ : ℝ) (hθ : 0 < θ) (hκ : 0 < κ) :
    0 ≤ fderiv ℝ (fun K => fderiv ℝ (hermitianPotential B m θ κ) K) H X X := by
  rw [potential_hessian_eq_inverse H X B m hm θ κ hθ hκ]
  let S := hermitianOptimizer (H : Matrix n n ℂ) B m θ κ
  let hS := hermitianOptimizer_posDef (H : Matrix n n ℂ) B m hm θ κ hθ hκ
  let J := tangentHessianEquiv (H : Matrix n n ℂ) B m hm θ κ hθ hκ S hS
  let U := J.symm (densityCenterFunctional X)
  have he : J U U = densityCenterFunctional X U := by
    dsimp only [U]
    rw [ContinuousLinearEquiv.apply_symm_apply]
  change 0 ≤ densityCenterFunctional X U
  by_cases hU : U = 0
  · rw [hU]
    exact le_of_eq ((densityCenterFunctional X).map_zero).symm
  · rw [← he]
    exact (negativeHessian_pos (H : Matrix n n ℂ) B m hm hθ hκ S U hS (fun h => hU (Subtype.ext h))).le

end MatrixSpencer.RectangularRidgeCalculus
