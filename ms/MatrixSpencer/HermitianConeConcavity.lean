import MatrixSpencer.FidelityContinuity
import MatrixSpencer.TsallisHessian
import MatrixSpencer.SecondDerivativeConcavity

/-! Positive-cone geometry and extension of scalar concavity to singular endpoints. -/
open Matrix Set Filter Topology
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace MatrixSpencer
noncomputable section
variable {n : Type*} [Fintype n] [DecidableEq n]
local instance hermConeCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance hermConeSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance

def hermitianPositiveCone : Set (selfAdjoint (Matrix n n ℂ)) :=
  {S | (S : Matrix n n ℂ).PosDef}

def hermitianSemidefiniteCone : Set (selfAdjoint (Matrix n n ℂ)) :=
  {S | (S : Matrix n n ℂ).PosSemidef}

theorem isOpen_hermitianPositiveCone : IsOpen (hermitianPositiveCone (n := n)) := by
  rw [isOpen_iff_mem_nhds]
  intro S hS
  exact eventually_posDef_of_posDef S hS

theorem convex_hermitianPositiveCone : Convex ℝ (hermitianPositiveCone (n := n)) := by
  intro S hS T hT a b ha hb hab
  exact posDef_convex_mixture hS hT ha hb hab

theorem convex_hermitianSemidefiniteCone : Convex ℝ (hermitianSemidefiniteCone (n := n)) := by
  intro S hS T hT a b ha hb _
  exact posSemidef_weighted_add hS hT ha hb

def hermitianRegularize (S : selfAdjoint (Matrix n n ℂ)) (r : ℝ) :
    selfAdjoint (Matrix n n ℂ) := S + r • 1

theorem hermitianRegularize_posDef (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosSemidef) {r : ℝ} (hr : 0 < r) :
    ((hermitianRegularize S r) : Matrix n n ℂ).PosDef := regularize_posDef hS hr

theorem hermitianRegularize_tendsto (S : selfAdjoint (Matrix n n ℂ)) :
    Tendsto (hermitianRegularize S) (𝓝[Ioi 0] 0) (𝓝 S) := by
  have hc : Continuous (hermitianRegularize S) :=
    continuous_const.add (continuous_id.smul continuous_const)
  simpa only [hermitianRegularize, zero_smul, add_zero] using
    (hc.tendsto 0).mono_left inf_le_left

omit [DecidableEq n] in
theorem tendsto_of_continuousOn_hermitianSemidefiniteCone {X : Type*} {l : Filter X}
    {f : selfAdjoint (Matrix n n ℂ) → ℝ}
    (hf : ContinuousOn f hermitianSemidefiniteCone)
    {S : X → selfAdjoint (Matrix n n ℂ)} {S₀ : selfAdjoint (Matrix n n ℂ)}
    (ht : Tendsto S l (𝓝 S₀)) (hS : ∀ᶠ x in l, (S x : Matrix n n ℂ).PosSemidef)
    (hS₀ : (S₀ : Matrix n n ℂ).PosSemidef) :
    Tendsto (fun x => f (S x)) l (𝓝 (f S₀)) :=
  (hf S₀ hS₀).tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨ht, hS⟩)

theorem concaveOn_hermitianSemidefiniteCone_of_posDef
    {f : selfAdjoint (Matrix n n ℂ) → ℝ}
    (hf : ContinuousOn f hermitianSemidefiniteCone)
    (hc : ConcaveOn ℝ hermitianPositiveCone f) :
    ConcaveOn ℝ hermitianSemidefiniteCone f := by
  refine ⟨convex_hermitianSemidefiniteCone, ?_⟩
  intro S hS T hT a b ha hb hab
  have hlim (X : selfAdjoint (Matrix n n ℂ)) (hX : (X : Matrix n n ℂ).PosSemidef) :
      Tendsto (fun r => f (hermitianRegularize X r)) (𝓝[Ioi 0] 0) (𝓝 (f X)) := by
    apply tendsto_of_continuousOn_hermitianSemidefiniteCone hf (hermitianRegularize_tendsto X) _ hX
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (hermitianRegularize_posDef X hX hr).posSemidef
  have hleft := ((hlim S hS).const_mul a).add ((hlim T hT).const_mul b)
  have hmix := ((hermitianRegularize_tendsto S).const_smul a).add
    ((hermitianRegularize_tendsto T).const_smul b)
  have hright := tendsto_of_continuousOn_hermitianSemidefiniteCone hf hmix
    (show ∀ᶠ r : ℝ in 𝓝[Ioi 0] 0,
      ((a • hermitianRegularize S r + b • hermitianRegularize T r :
        selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ).PosSemidef from by
      filter_upwards [self_mem_nhdsWithin] with r hr
      exact posSemidef_weighted_add (hermitianRegularize_posDef S hS hr).posSemidef
        (hermitianRegularize_posDef T hT hr).posSemidef ha hb)
    (posSemidef_weighted_add hS hT ha hb)
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact hc.2 (hermitianRegularize_posDef S hS hr) (hermitianRegularize_posDef T hT hr) ha hb hab

end
end MatrixSpencer
