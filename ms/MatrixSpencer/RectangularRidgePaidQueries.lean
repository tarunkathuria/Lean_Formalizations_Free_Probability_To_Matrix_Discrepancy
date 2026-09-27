import MatrixSpencer.RectangularRidgeCovarianceQueries

/-! Exact finite covariance differences and real paid cuts for the mixed SDP.
The covariance-query cap is instantiated by the previous module; its only
conditioning input is a matrix lower bound on the actual mixed optimizer. -/
open Matrix Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
noncomputable section
namespace MatrixSpencer.RectangularRidgePaidQueries
open RectangularRidgeCovarianceQueries MSManuscriptGammaSmoothness
variable {k d : ℕ} [Nonempty (Fin d)]
local instance ridgePaidQueryCStar : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
local instance ridgePaidQueryPhysicalSpace : NormedSpace ℝ (selfAdjoint (Matrix (Fin d) (Fin d) ℂ)) := inferInstance
attribute [local irreducible] RectangularRidgePotential.optimizer
set_option maxHeartbeats 300000

def gram (H : selfAdjoint (Matrix (Fin d) (Fin d) ℂ))
    (A : Fin k → Matrix (Fin d) (Fin d) ℂ) (C : Matrix (Fin k) (Fin k) ℝ)
    (m : ℕ) (θ κ : ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  RectangularRidgeOwnerFrame.ownedGram A C
    (RectangularRidgePotential.optimizer (H : Matrix (Fin d) (Fin d) ℂ) (covarianceKraus A C) m θ κ)

def probe (H : Matrix (Fin d) (Fin d) ℂ) (A : Fin k → Matrix (Fin d) (Fin d) ℂ)
    (C : Matrix (Fin k) (Fin k) ℝ) (m : ℕ) (θ κ s : ℝ)
    (u : EuclideanSpace ℝ (Fin k)) : ℝ :=
  MSManuscriptGammaDifference.negativeSlope (curve H A C m θ κ u) s

theorem curve_derivative_zero (H : selfAdjoint (Matrix (Fin d) (Fin d) ℂ))
    (A : Fin k → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C : Matrix (Fin k) (Fin k) ℝ} (hC : C.PosDef)
    (m : ℕ) (hm : 1 ≤ m) {θ κ : ℝ} (hθ : 0 < θ) (hκ : 0 < κ)
    (u : EuclideanSpace ℝ (Fin k)) :
    HasDerivAt (curve (H : Matrix (Fin d) (Fin d) ℂ) A C m θ κ u)
      (-(WithLp.ofLp u ⬝ᵥ (gram H A C m θ κ *ᵥ WithLp.ofLp u))) 0 :=
  hasDerivAt_ridgeOwnerPotential_supported_shave H A hA hC.posSemidef u
    (range_mem_of_posDef hC u) m hm θ κ hθ hκ

/-- Exact SDP values give a finite one-sided derivative query with a proved
error bound. The optimizer floor is required along its short real segment. -/
theorem probe_accuracy (H : selfAdjoint (Matrix (Fin d) (Fin d) ℂ))
    (A : Fin k → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ i, (A i).IsHermitian)
    {L : ℝ} (hL : 0 ≤ L) (hAn : ∀ i, ‖A i‖ ≤ L) {C : Matrix (Fin k) (Fin k) ℝ}
    (m : ℕ) (hm : 1 ≤ m) {R θ κ δ μ s : ℝ} (hθ : 0 < θ) (hκ : 0 < κ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (hR : ‖(H : Matrix (Fin d) (Fin d) ℂ)‖ ≤ R)
    (hfloor : δ • (1 : Matrix (Fin k) (Fin k) ℝ) ≤ C) (hC1 : C ≤ 1)
    (u : EuclideanSpace ℝ (Fin k)) (hu : ‖u‖ = 1) (hs : 0 < s) (hsδ : s ≤ δ/4)
    (hoptimizer : ∀ a ∈ Ioo 0 s, μ • (1 : Matrix (Fin d) (Fin d) ℂ) ≤
      RectangularRidgePotential.optimizer (H : Matrix (Fin d) (Fin d) ℂ)
        (covarianceKraus A (C-a • realRankOne (WithLp.ofLp u))) m θ κ) :
    |probe (H : Matrix (Fin d) (Fin d) ℂ) A C m θ κ s u -
      WithLp.ofLp u ⬝ᵥ (gram H A C m θ κ *ᵥ WithLp.ofLp u)| ≤
        secondCap k d R κ δ μ L*s/2 := by
  let f := curve (H : Matrix (Fin d) (Fin d) ℂ) A C m θ κ u
  have hf : ContDiffOn ℝ 2 f (Icc 0 s) :=
    query_contDiffOn _ _ hA m hm hθ hκ hδ hfloor (by linarith) u hu
  have hd := curve_derivative_zero H A hA (posDef_of_floor hδ hfloor) m hm hθ hκ u
  have hsecond : ∀ a ∈ Ioo 0 s, |iteratedDeriv 2 f a| ≤ secondCap k d R κ δ μ L := by
    intro a ha
    exact query_second_le H A hA hL hAn m hm hθ hκ hδ hδ1 hμ hμ1 hR hfloor hC1 u hu
      ⟨ha.1, by linarith [ha.2]⟩ (hoptimizer a ha)
  have hh := MSManuscriptGammaDifference.negativeSlope_accuracy f f (ν := 0) hs hf hd hsecond
    (by simp) (by simp)
  simpa only [probe, f, mul_zero, zero_mul, zero_div, add_zero] using hh

/-- Real paid decrease of the actual optimized mixed potential, with all
second derivatives and Taylor errors supplied by the proved query estimate. -/
theorem paid_drop (H : selfAdjoint (Matrix (Fin d) (Fin d) ℂ))
    (A : Fin k → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ i, (A i).IsHermitian)
    {L : ℝ} (hL : 0 ≤ L) (hAn : ∀ i, ‖A i‖ ≤ L) {C : Matrix (Fin k) (Fin k) ℝ}
    (m : ℕ) (hm : 1 ≤ m) {R θ κ δ μ α price : ℝ} (hθ : 0 < θ) (hκ : 0 < κ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (hR : ‖(H : Matrix (Fin d) (Fin d) ℂ)‖ ≤ R)
    (hfloor : δ • (1 : Matrix (Fin k) (Fin k) ℝ) ≤ C) (hC1 : C ≤ 1)
    (u : EuclideanSpace ℝ (Fin k)) (hu : ‖u‖ = 1) (hα : 0 < α) (hαδ : α ≤ δ/4)
    (hq : 7*price/8 ≤ WithLp.ofLp u ⬝ᵥ (gram H A C m θ κ *ᵥ WithLp.ofLp u))
    (hstep : secondCap k d R κ δ μ L*α ≤ price/2)
    (hoptimizer : ∀ a ∈ Ioo 0 α, μ • (1 : Matrix (Fin d) (Fin d) ℂ) ≤
      RectangularRidgePotential.optimizer (H : Matrix (Fin d) (Fin d) ℂ)
        (covarianceKraus A (C-a • realRankOne (WithLp.ofLp u))) m θ κ) :
    RectangularRidgeCovarianceCalculus.ownerPotential m H A
        (C-α • realRankOne (WithLp.ofLp u)) θ κ + 5*price*α/8 ≤
      RectangularRidgeCovarianceCalculus.ownerPotential m H A C θ κ := by
  let f := curve (H : Matrix (Fin d) (Fin d) ℂ) A C m θ κ u
  have hf : ContDiffOn ℝ 2 f (Icc 0 α) :=
    query_contDiffOn _ _ hA m hm hθ hκ hδ hfloor (by linarith) u hu
  have hd := curve_derivative_zero H A hA (posDef_of_floor hδ hfloor) m hm hθ hκ u
  have hsecond : ∀ a ∈ Ioo 0 α, iteratedDeriv 2 f a ≤ secondCap k d R κ δ μ L := by
    intro a ha
    exact (le_abs_self _).trans (query_second_le H A hA hL hAn m hm hθ hκ hδ hδ1 hμ hμ1
      hR hfloor hC1 u hu ⟨ha.1, by linarith [ha.2]⟩ (hoptimizer a ha))
  have hh := MSManuscriptPaidStep.paid_drop f hα hf hd hsecond hq hstep
  simp only [f,curve,zero_smul,sub_zero] at hh
  linarith

end MatrixSpencer.RectangularRidgePaidQueries
