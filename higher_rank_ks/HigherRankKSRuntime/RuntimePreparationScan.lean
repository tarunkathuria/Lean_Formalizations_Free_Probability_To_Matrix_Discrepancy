import HigherRankKSRuntime.PreparationAnalysis
import HigherRankKSRuntime.RuntimePreparationBounds

/-! The preparation scan's true derivative conclusions, with all Taylor
regularity discharged for the actual optimized four-block potential. -/
noncomputable section
open Matrix MatrixSpencer Set
open scoped BigOperators Topology ContDiff MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace HigherRankKSRuntime.RuntimePreparationScan
open AugmentedHigherRankKS ActiveEnumeration RuntimeParameters
open MatrixSpencer.RealRAM.JacobiIteration (Counted)
variable {N : ℕ} {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

theorem state_regular (p : Dimensions) (hp : p ∈ Domain) (hd : (Fintype.card n : ℝ) ≤ p.D)
    (A : Fin N → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef) (hsum : ∑ i, A i ≤ 1)
    {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hN : ∀ i, ‖A i‖ ≤ ε)
    {r : ℕ} (hrank : ∀ i, (A i).rank ≤ r) (k : ℕ) (hk : 1 ≤ k)
    (hrβ : (r:ℝ)^((1:ℝ)/2^k) ≤ 2)
    (x₀ : Fin N → ℝ) (hx₀ : ∀ i, |x₀ i| ≤ 1)
    {z : EpochState (Fin N)} (hz : z ∈ epochDomain (a p) 4)
    (hc : NextEvent.Clean z (rho p) (zeta p)) (i : Fin N) (hi : i ∈ labels z) :
    ContDiffOn ℝ 2 (fun s => epochPotential A ((1:ℝ)/2^k) (theta p) x₀
      (prepareOwner (a p) z i s)) (Icc 0 (prep p)) ∧
    DifferentiableAt ℝ (fun s => epochPotential A ((1:ℝ)/2^k) (theta p) x₀
      (prepareOwner (a p) z i s)) 0 ∧
    ∀ s ∈ Ioo 0 (prep p), |iteratedDeriv 2 (fun t =>
      epochPotential A ((1:ℝ)/2^k) (theta p) x₀ (prepareOwner (a p) z i t)) s| ≤ M p := by
  let ai : ActiveOwners z := ⟨i,(mem_positiveReserves z i).mpr ((mem_labels z i).mp hi)⟩
  let j := (activeEquiv z).symm ai
  have he : (fun t => epochPotential A ((1:ℝ)/2^k) (theta p) x₀ (prepareOwner (a p) z i t)) =
      RuntimeCurvature.prepCurve (ActiveEnumeration.center A x₀ z) (restrictedAtoms A z)
        ((1:ℝ)/2^k) (theta p) (a p) (restrictedReserve z) j := by
    funext t
    have hh := preparation_chart_eq A ((1:ℝ)/2^k) (theta p) x₀ hz j t
    simpa only [j,Equiv.apply_symm_apply] using hh
  rw [he]
  have hb := RuntimePreparationBounds.prep_line_bounds p hp hd
    _ (RuntimeStateBounds.state_center_hermitian A hA x₀ z)
    (RuntimeStateBounds.state_center_bound A hA hsum x₀ hx₀ hz)
    (restrictedAtoms A z) (fun i => hA _) (restricted_atoms_subisotropic A hA hsum z)
    hε hε1 (fun i => hN _) (fun i => hrank _) k hk hrβ (restrictedReserve z)
    (RuntimeStateBounds.active_clean hc).2 (RuntimeStateBounds.active_reserve_upper hz) j
  have hdiff := RuntimePreparationBounds.prep_differentiable_zero
    (ActiveEnumeration.center A x₀ z) (restrictedAtoms A z) (fun i => hA _)
    k hk (theta_poly.positive p hp) (a p) (restrictedReserve z)
    (RuntimeStateBounds.active_positive z) j
  exact ⟨hb.1,hdiff,fun s hs => hb.2 s ⟨hs.1.le,hs.2.le⟩⟩

theorem rejected_derivatives (p : Dimensions) (hp : p ∈ Domain) (hd : (Fintype.card n : ℝ) ≤ p.D)
    (A : Fin N → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef) (hsum : ∑ i, A i ≤ 1)
    {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hN : ∀ i, ‖A i‖ ≤ ε)
    {r : ℕ} (hrank : ∀ i, (A i).rank ≤ r) (k : ℕ) (hk : 1 ≤ k)
    (hrβ : (r:ℝ)^((1:ℝ)/2^k) ≤ 2)
    (x₀ : Fin N → ℝ) (hx₀ : ∀ i, |x₀ i| ≤ 1)
    (query : EpochState (Fin N) → Counted ℝ)
    (hquery : ∀ y, (∀ i, 0 ≤ reserve y i) →
      |(query y).value-epochPotential A ((1:ℝ)/2^k) (theta p) x₀ y| ≤ accuracy p)
    {z : EpochState (Fin N)} (hz : z ∈ epochDomain (a p) 4)
    (hc : NextEvent.Clean z (rho p) (zeta p))
    (hreject : NextEvent.Rejected query (a p) (prep p) (p0 p) z) :
    ∀ i, -(p0 p/(2*a p)) < deriv (RuntimeCurvature.prepCurve
      (ActiveEnumeration.center A x₀ z) (restrictedAtoms A z) ((1:ℝ)/2^k)
      (theta p) (a p) (restrictedReserve z) i) 0 :=
  PreparationAnalysis.rejected_active_derivatives p hp A ((1:ℝ)/2^k) (theta p) x₀ query
    hz hc hquery (state_regular p hp hd A hA hsum hε hε1 hN hrank k hk hrβ x₀ hx₀ hz hc) hreject
end HigherRankKSRuntime.RuntimePreparationScan
