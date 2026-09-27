import MatrixSpencer.OptimizerResponse

/-!
# Deleting a concave source term at a stationary density

This is the tangent argument used by the endpoint certificate. It needs
no interchange of optimization orders. The function g is the fixed
transport objective after deleting one source term; tau is that term.
-/

open MatrixSpencer Set

noncomputable section
namespace HigherRankKS.EndpointMajorant

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem deletion_bound {K : Set E} {g τ new : E → ℝ} {S : E}
    (hg : ConcaveOn ℝ K g) (hS : S ∈ K)
    {g' τ' δ : E →L[ℝ] ℝ} (hd : HasFDerivAt g g' S) (c : ℝ)
    (hstationary : ∀ T ∈ K, (g' + c • τ') (T - S) = 0)
    (heuler : τ' S = τ S)
    (hcertificate : ∀ T ∈ K, δ T ≤ c * τ' T)
    (hmajorant : ∀ T ∈ K, new T ≤ g T + δ T) :
    ∀ T ∈ K, new T ≤ g S + c * τ S := by
  intro T hT
  have ht := concaveOn_le_tangent hg hS hT hd
  have hs := hstationary T hT
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, map_sub, heuler] at hs ht
  have hc := hcertificate T hT
  have hm := hmajorant T hT
  linarith

/-- The same argument with the supremum explicitly defined on the full
comparison domain. Boundedness is obtained from the pointwise proof. -/
theorem supremum_deletion_bound {K : Set E} {g τ new : E → ℝ} {S : E}
    (hg : ConcaveOn ℝ K g) (hS : S ∈ K)
    {g' τ' δ : E →L[ℝ] ℝ} (hd : HasFDerivAt g g' S) (c : ℝ)
    (hstationary : ∀ T ∈ K, (g' + c • τ') (T - S) = 0)
    (heuler : τ' S = τ S)
    (hcertificate : ∀ T ∈ K, δ T ≤ c * τ' T)
    (hmajorant : ∀ T ∈ K, new T ≤ g T + δ T) :
    sSup (new '' K) ≤ g S + c * τ S := by
  apply csSup_le ⟨new S, mem_image_of_mem new hS⟩
  rintro _ ⟨T, hT, rfl⟩
  exact deletion_bound hg hS hd c hstationary heuler hcertificate hmajorant T hT

end HigherRankKS.EndpointMajorant
