import AugmentedHigherRankKS.FourBlockSource
import MatrixSpencer.FidelityContinuity
import MatrixSpencer.SpectralDensity

/-!
# The nonlinear density objective and an actual attained maximum

This is the augmented objective with its concrete four-block carrier-power source.
Compactness constructs the optimizer mathematically. No optimizer or value
solver is supplied as a premise.
-/

open Matrix MatrixSpencer Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

noncomputable section
namespace AugmentedHigherRankKS

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
local instance potentialCStar {k : Type*} [Fintype k] [DecidableEq k] :
    CStarAlgebra (Matrix k k ℂ) := {}

/-- Full ambient density objective, including the nonlinear source. -/
def objective (H : Matrix (FourSpin n) (FourSpin n) ℂ)
    (A : ι → Matrix n n ℂ) (β : ℝ) (c : ι → ℝ) (θ : ℝ)
    (S : Matrix (FourSpin n) (FourSpin n) ℂ) : ℝ :=
  realTrace (H * S) + 2 * fidelity S (source A β c S) +
    2 * θ * realTrace (CFC.sqrt S)

/-- Supremum over the actual compact density set. -/
def potential (H : Matrix (FourSpin n) (FourSpin n) ℂ)
    (A : ι → Matrix n n ℂ) (β : ℝ) (c : ι → ℝ) (θ : ℝ) : ℝ :=
  sSup (objective H A β c θ '' densitySet)

theorem continuousOn_objective (H : Matrix (FourSpin n) (FourSpin n) ℂ)
    (A : ι → Matrix n n ℂ) {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    {c : ι → ℝ} (hc : ∀ i, 0 ≤ c i) (θ : ℝ) :
    ContinuousOn (objective H A β c θ) densitySet := by
  apply continuousOn_iff_continuous_restrict.mpr
  have hs : Continuous
      (fun S : (densitySet : Set (Matrix (FourSpin n) (FourSpin n) ℂ)) =>
        (S : Matrix (FourSpin n) (FourSpin n) ℂ)) := continuous_subtype_val
  have hsource := continuous_source_of_psd A hs (fun S => S.property.1)
    (c := fun _ => c) (fun _ => continuous_const) hβ hβ1
  have hf := continuous_fidelity_of_psd hs hsource (fun S => S.property.1)
    (fun S => source_posSemidef A β hc S.property.1)
  have hroot := continuous_matrix_sqrt_of_psd hs (fun S => S.property.1)
  exact ((continuous_realTrace.comp (continuous_const.mul hs)).add
    (continuous_const.mul hf)).add
      (continuous_const.mul (continuous_realTrace.comp hroot))

/-- Attainment is proved for the concrete source, including singular inputs. -/
theorem exists_optimizer [Nonempty n]
    (H : Matrix (FourSpin n) (FourSpin n) ℂ) (A : ι → Matrix n n ℂ)
    {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    {c : ι → ℝ} (hc : ∀ i, 0 ≤ c i) (θ : ℝ) :
    ∃ S ∈ densitySet,
      ∀ T ∈ densitySet, objective H A β c θ T ≤ objective H A β c θ S :=
  isCompact_densitySet.exists_isMaxOn densitySet_nonempty
    (continuousOn_objective H A hβ hβ1 hc θ)

theorem potential_eq_of_optimizer
    (H : Matrix (FourSpin n) (FourSpin n) ℂ) (A : ι → Matrix n n ℂ)
    (β : ℝ) (c : ι → ℝ) (θ : ℝ)
    {S : Matrix (FourSpin n) (FourSpin n) ℂ} (hS : S ∈ densitySet)
    (hmax : ∀ T ∈ densitySet, objective H A β c θ T ≤ objective H A β c θ S) :
    potential H A β c θ = objective H A β c θ S := by
  apply IsGreatest.csSup_eq
  exact ⟨⟨S, hS, rfl⟩, by
    rintro z ⟨T, hT, rfl⟩
    exact hmax T hT⟩

theorem objective_le_potential [Nonempty n]
    (H : Matrix (FourSpin n) (FourSpin n) ℂ) (A : ι → Matrix n n ℂ)
    {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    {c : ι → ℝ} (hc : ∀ i, 0 ≤ c i) (θ : ℝ)
    {S : Matrix (FourSpin n) (FourSpin n) ℂ} (hS : S ∈ densitySet) :
    objective H A β c θ S ≤ potential H A β c θ := by
  obtain ⟨T, hT, hmax⟩ := exists_optimizer H A hβ hβ1 hc θ
  rw [potential_eq_of_optimizer H A β c θ hT hmax]
  exact hmax S hS

theorem trace_center_le_potential [Nonempty n]
    (H : Matrix (FourSpin n) (FourSpin n) ℂ) (A : ι → Matrix n n ℂ)
    {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    {c : ι → ℝ} (hc : ∀ i, 0 ≤ c i) {θ : ℝ} (hθ : 0 ≤ θ)
    {S : Matrix (FourSpin n) (FourSpin n) ℂ} (hS : S ∈ densitySet) :
    realTrace (H * S) ≤ potential H A β c θ := by
  have ho := objective_le_potential H A hβ hβ1 hc θ hS
  have hf := fidelity_nonneg S (source A β c S)
  have hr := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hθ)
    (realTrace_nonneg (CFC.sqrt_nonneg S).posSemidef)
  unfold objective at ho
  linarith

theorem eigenvalue_le_potential [Nonempty n]
    {H : Matrix (FourSpin n) (FourSpin n) ℂ} (hH : H.IsHermitian)
    (A : ι → Matrix n n ℂ)
    {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    {c : ι → ℝ} (hc : ∀ i, 0 ≤ c i) {θ : ℝ} (hθ : 0 ≤ θ)
    (j : FourSpin n) : hH.eigenvalues j ≤ potential H A β c θ := by
  have h := trace_center_le_potential H A hβ hβ1 hc hθ (eigenDensity_mem hH j)
  rwa [realTrace_mul_eigenDensity] at h

theorem continuous_objective_of_psd {X : Type*} [TopologicalSpace X]
    (A : ι → Matrix n n ℂ)
    {H S : X → Matrix (FourSpin n) (FourSpin n) ℂ}
    (hH : Continuous H) (hS : Continuous S) (hpos : ∀ x, (S x).PosSemidef)
    {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    {c : X → ι → ℝ} (hc : ∀ i, Continuous (fun x => c x i))
    (hnonneg : ∀ x i, 0 ≤ c x i) (θ : ℝ) :
    Continuous (fun x => objective (H x) A β (c x) θ (S x)) := by
  have hsource := continuous_source_of_psd A hS hpos hc hβ hβ1
  have hf := continuous_fidelity_of_psd hS hsource hpos
    (fun x => source_posSemidef A β (hnonneg x) (hpos x))
  have hroot := continuous_matrix_sqrt_of_psd hS hpos
  exact ((continuous_realTrace.comp (hH.mul hS)).add
    (continuous_const.mul hf)).add
      (continuous_const.mul (continuous_realTrace.comp hroot))

/-- Continuity of the optimized value follows from a continuous objective
on a fixed compact density set, including singular densities and sources. -/
theorem continuous_potential_of_data {X : Type*} [TopologicalSpace X]
    (A : ι → Matrix n n ℂ)
    {H : X → Matrix (FourSpin n) (FourSpin n) ℂ} (hH : Continuous H)
    {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    {c : X → ι → ℝ} (hc : ∀ i, Continuous (fun x => c x i))
    (hnonneg : ∀ x i, 0 ≤ c x i) (θ : ℝ) :
    Continuous (fun x => potential (H x) A β (c x) θ) := by
  let D := (densitySet : Set (Matrix (FourSpin n) (FourSpin n) ℂ))
  letI : CompactSpace D := isCompact_iff_compactSpace.mp isCompact_densitySet
  have hjoint : Continuous (fun z : X × D =>
      objective (H z.1) A β (c z.1) θ z.2) :=
    continuous_objective_of_psd A (hH.comp continuous_fst)
      (continuous_subtype_val.comp continuous_snd) (fun z => z.2.property.1)
      hβ hβ1 (fun i => (hc i).comp continuous_fst)
      (fun z i => hnonneg z.1 i) θ
  have hs := (isCompact_univ : IsCompact (Set.univ : Set D)).continuous_sSup
    (f := fun x (S : D) => objective (H x) A β (c x) θ S) hjoint
  have heq : ∀ x, (fun S : D => objective (H x) A β (c x) θ S) '' Set.univ =
      objective (H x) A β (c x) θ '' densitySet := by
    intro x
    ext y
    constructor
    · rintro ⟨S, _, rfl⟩
      exact ⟨S, S.property, rfl⟩
    · rintro ⟨S, hS, rfl⟩
      exact ⟨⟨S, hS⟩, Set.mem_univ _, rfl⟩
  simpa only [potential, heq] using hs

end AugmentedHigherRankKS
