import AugmentedHigherRankKS.ActualPreparation
import AugmentedHigherRankKS.EpochBounds

/-! The actual compact minimizer and its reserve tie-break, including all
boundary and zero-atom cases. -/
open Matrix MatrixSpencer Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace AugmentedHigherRankKS
variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n] [Nonempty n]

theorem exists_epoch_minimizer
    (A : ι → Matrix n n ℂ) {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1) (θ : ℝ)
    (x₀ : ι → ℝ) (hx : ∀ i, -1 ≤ x₀ i ∧ x₀ i ≤ 1)
    {a R : ℝ} (ha : 0 < a) (hR : 0 ≤ R) :
    ∃ z ∈ epochDomain a R,
      IsMinOn (epochPotential A β θ x₀) (epochDomain a R) z ∧
      (∀ i, |position z i| = 1 → reserve z i = 0) ∧
      (∀ i, A i = 0 → reserve z i = 0) ∧
      epochPotential A β θ x₀ z ≤ epochPotential A β θ x₀ (initialState a R x₀) := by
  obtain ⟨z, hz, hmin, htie⟩ := exists_lexicographic_minimum ha.le hR x₀ hx
    (epochPotential A β θ x₀) (continuousOn_epochPotential A hβ hβ1 θ x₀ a R)
  have hface := face_reserve_zero_at_lexicographic_minimum (epochPotential A β θ x₀)
    hz hmin htie (fun y hy i _ => epochPotential_dropReserve_le A hβ hβ1 θ x₀ hy i)
  have hzero := zero_atom_reserve_zero_at_minimum A β θ x₀ ha hz htie
  exact ⟨z, hz, hmin, hface, hzero, hmin (initialState_mem ha.le hR x₀ hx)⟩

/-- Once exhaustion has been proved for each positive regularizer, its
removal uses only compactness of the unchanged original reserve state set. -/
theorem exhausted_epoch_bound_of_regularized_values
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    {b : ℝ} (hsum : ∑ i, A i ≤ b • (1 : Matrix n n ℂ))
    {ε : ℝ} (hε : 0 ≤ ε) (hN : ∀ i, ‖A i‖ ≤ ε)
    {r : ℕ} (hr : ∀ i, (A i).rank ≤ r)
    {β : ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    {a R : ℝ} (haR : 0 ≤ a * R) (x₀ : ι → ℝ)
    (hvalues : ∀ θ : ℝ, 0 < θ → ∃ z ∈ epochDomain a R,
      (∀ i, reserve z i = 0) ∧
      epochPotential A β θ x₀ z ≤ epochPotential A β θ x₀ (initialState a R x₀)) :
    ∃ z ∈ epochDomain a R, (∀ i, reserve z i = 0) ∧
      epochCenterSize A x₀ z ≤ 2 * Real.sqrt (4 * (a * R) * ε * (r : ℝ)^β * b) := by
  apply exists_exhausted_bound_of_arbitrarily_small_error a R (epochCenterSize A x₀)
    (continuous_epochCenterSize A x₀)
  intro η hη
  let C := 2 * Real.sqrt (Fintype.card (FourSpin n) : ℝ)
  have hC : 0 ≤ C := by positivity
  let θ := η / (C + 1)
  have hθ : 0 < θ := div_pos hη (by linarith)
  obtain ⟨z, hz, hc, hval⟩ := hvalues θ hθ
  refine ⟨z, hz, hc, ?_⟩
  have hi := epochPotential_initial_le A hA hsum hε hN hr hβ hβ1 haR hθ.le x₀
  have he := (epochCenterSize_le_potential A hA hβ.le hβ1.le hθ.le x₀ hz).trans
    (hval.trans hi)
  have hθC : θ * C ≤ η := by
    have ht : θ * (C + 1) = η := div_mul_cancel₀ η (by linarith : C + 1 ≠ 0)
    nlinarith
  dsimp only [C] at hθC
  nlinarith

end AugmentedHigherRankKS
