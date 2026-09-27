import HigherRankKSRuntime.Tangent.RadialBasis

/-! Exact EVD of the Hessian compressed to an explicitly parametrized subspace. -/
open Matrix
open scoped BigOperators
noncomputable section
namespace HigherRankKSRuntime.Tangent.RestrictedEVD
open MatrixSpencer.KSRayleighAccuracy SeamlessKS.ExactEVD
open HigherRankKSRuntime.Tangent.RadialBasis (Space)
variable {m r : ℕ}

def compression (U : Space r →ₗᵢ[ℝ] Space m) (A : Matrix (Fin m) (Fin m) ℝ) :
    Matrix (Fin r) (Fin r) ℝ :=
  (Matrix.toEuclideanCLM (n := Fin r) (𝕜 := ℝ)).symm
    (U.toContinuousLinearMap.adjoint ∘L
      Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℝ) A ∘L U.toContinuousLinearMap)

theorem compression_rayleigh (U : Space r →ₗᵢ[ℝ] Space m)
    (A : Matrix (Fin m) (Fin m) ℝ) (v : Space r) :
    realRayleigh (compression U A) v = realRayleigh A (U v) := by
  simp only [realRayleigh, compression, StarAlgEquiv.apply_symm_apply,
    ContinuousLinearMap.comp_apply]
  exact U.toContinuousLinearMap.adjoint_inner_right v _

theorem compression_symmetric (U : Space r →ₗᵢ[ℝ] Space m)
    (A : Matrix (Fin m) (Fin m) ℝ) (hA : A.IsSymm) :
    (compression U A).IsSymm := by
  have ha : IsSelfAdjoint A := hA
  have hc := (ha.map (Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℝ))).adjoint_conj
    U.toContinuousLinearMap
  exact hc.map (Matrix.toEuclideanCLM (n := Fin r) (𝕜 := ℝ)).symm

def output (U : Space r →ₗᵢ[ℝ] Space m) (A : Matrix (Fin m) (Fin m) ℝ)
    (hr : 0 < r) : Space m := U (SeamlessKS.ExactEVD.output (compression U A) hr)

theorem output_norm (U : Space r →ₗᵢ[ℝ] Space m) (A : Matrix (Fin m) (Fin m) ℝ)
    (hr : 0 < r) : ‖output U A hr‖ = 1 := by
  rw [output, U.norm_map]
  exact SeamlessKS.ExactEVD.output_norm _ _

theorem output_minimal (U : Space r →ₗᵢ[ℝ] Space m) (A : Matrix (Fin m) (Fin m) ℝ)
    (hA : A.IsSymm) (hr : 0 < r) (v : Space r) (hv : ‖v‖ = 1) :
    realRayleigh A (output U A hr) ≤ realRayleigh A (U v) := by
  have h := SeamlessKS.ExactEVD.output_minimal (compression U A)
    (compression_symmetric U A hA) hr v hv
  simpa only [compression_rayleigh, output] using h

theorem output_comparison (U : Space r →ₗᵢ[ℝ] Space m)
    (A B : Matrix (Fin m) (Fin m) ℝ) (hB : B.IsSymm) (hr : 0 < r)
    {κ : ℝ} (herr : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (A - B)‖ ≤ κ)
    (v : Space r) (hv : ‖v‖ = 1) :
    realRayleigh A (output U B hr) ≤ realRayleigh A (U v) + 2 * κ := by
  have ho := abs_le.mp (realRayleigh_error A B herr _ (output_norm U B hr))
  have hw := abs_le.mp (realRayleigh_error A B herr (U v) ((U.norm_map v).trans hv))
  have hm := output_minimal U B hB hr v hv
  linarith

end HigherRankKSRuntime.Tangent.RestrictedEVD
