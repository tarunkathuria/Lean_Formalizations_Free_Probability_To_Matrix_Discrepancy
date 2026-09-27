import FaithfulMS.DirectDensity
import MatrixSpencer.KSConvexValueOracle
import MatrixSpencer.RectangularRidgeAffineSDP

/-!
# Extracting the direct density report from the concrete affine SDP

The hypotheses here are exactly those of an optimizing-primal SDP primitive:
its output is feasible and maximizes the supplied affine objective. The
density component is read from the existing explicit coordinate chart.
Optimality for the nonlinear density objective is then proved using the
already established exact lift, rather than added to the primitive contract.
-/

open Matrix Set
open scoped BigOperators InnerProductSpace MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace FaithfulMS.DirectDensitySDP
open MatrixSpencer DirectDensity

variable {n ι : Type*} [Fintype n] [LinearOrder n] [Fintype ι] [DecidableEq ι]
local instance : CStarAlgebra (Matrix n n ℂ) := {}

def squareOfAffine (a : n) (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (C : Matrix ι ι ℝ) (hC : C.PosSemidef)
    (S₀ Y₀ : selfAdjoint (Matrix n n ℂ)) (htr : realTrace (S₀ : Matrix n n ℂ) = 1)
    (θ : ℝ) (hθ : 0 < θ) (x : KSFullManuscriptAffineData.Space a)
    (hx : x ∈ KSFullManuscriptAffinePSD.target
      (OwnerSDPProgramSize.data a A hA C hC S₀ Y₀ 0))
    (hmax : ∀ y ∈ KSFullManuscriptAffinePSD.target
      (OwnerSDPProgramSize.data a A hA C hC S₀ Y₀ 0),
      KSFullManuscriptAffineObjective.offset H θ S₀ Y₀ +
        ⟪KSFullManuscriptAffineObjective.coefficient a H θ, y⟫_ℝ ≤
      KSFullManuscriptAffineObjective.offset H θ S₀ Y₀ +
        ⟪KSFullManuscriptAffineObjective.coefficient a H θ, x⟫_ℝ) :
    SquareSolution H A C θ := by
  letI : Nonempty n := ⟨a⟩
  let S := KSFullManuscriptSDPCoordinates.density a S₀
    (KSFullManuscriptAffineData.entries a x)
  let Y := KSFullManuscriptSDPCoordinates.regularizer a Y₀
    (KSFullManuscriptAffineData.entries a x)
  let Z := KSFullManuscriptSDPCoordinates.fidelityLinear a
    (KSFullManuscriptAffineData.entries a x)
  have hf : KSFullManuscriptSDPIdentity.Feasible (krausChannel (covarianceKraus A C))
      0 S Y Z := by
    have h := (OwnerSDPProgramSize.target_iff a A hA C hC S₀ Y₀ htr 0 x).mp hx
    simpa only [KSFullManuscriptSDPIdentity.Feasible, covarianceSource_eq_kraus A hA hC]
      using h
  refine ⟨S, KSFullManuscriptSDPIdentity.feasible_density hf, ?_⟩
  intro T hT
  obtain ⟨y, hy, hval, _⟩ := OwnerSDPProgramSize.exists_maximizer
    a H A hA C hC S₀ Y₀ htr hθ
  have hm := hmax y hy
  rw [hval, ownerPotential_eq_densityPotential H A hA hC θ] at hm
  have hupper := KSFullManuscriptSDPIdentity.feasible_value_le (H := H) hθ.le hf
  have he := KSFullManuscriptAffineObjective.value_eq_affine a H θ S₀ Y₀ x
  change KSFullManuscriptSDPIdentity.value H θ S Y Z = _ at he
  rw [he] at hupper
  have heobj : KSFullManuscriptSDPIdentity.objective H
      (krausChannel (covarianceKraus A C)) θ 0 S =
      densityObjective H (covarianceKraus A C) θ S := by
    simp only [KSFullManuscriptSDPIdentity.objective, densityObjective, zero_smul, add_zero]
  rw [heobj] at hupper
  exact (densityObjective_le_potential H (covarianceKraus A C) θ hT).trans
    (hm.trans hupper)

def rectangularOfAffine (m : ℕ) (hm : 1 ≤ m) (a : n) (H : Matrix n n ℂ)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (C : Matrix ι ι ℝ) (hC : C.PosSemidef) (θ κ : ℝ)
    (hθ : 0 < θ) (hκ : 0 ≤ κ) (x : DyadicSDPCoordinates.Space m a)
    (hx : x ∈ DyadicOwnerSDP.feasible m a A hA C hC)
    (hmax : ∀ y ∈ DyadicOwnerSDP.feasible m a A hA C hC,
      RectangularRidgeAffineSDP.objective m hm a H θ κ y ≤
        RectangularRidgeAffineSDP.objective m hm a H θ κ x) :
    RectangularSolution H A C m θ κ := by
  letI : Nonempty n := ⟨a⟩
  let S := DyadicSDPCoordinates.density m a (DyadicOwnerSDP.center a)
    (DyadicSDPCoordinates.entries m a x)
  let X := DyadicSDPCoordinates.chain m a (DyadicSDPCoordinates.entries m a x)
  let Z := DyadicSDPCoordinates.fidelityLinear m a (DyadicSDPCoordinates.entries m a x)
  have hf : DyadicOwnerSDPIdentity.Feasible (krausChannel (covarianceKraus A C)) m S X Z := by
    rw [DyadicOwnerSDP.feasible_eq] at hx
    exact (DyadicOwnerSDPIdentity.covariance_feasible_iff A hA hC).mp hx
  refine ⟨S, hf.1, ?_⟩
  intro T hT
  obtain ⟨y, hy, hval, _⟩ := RectangularRidgeAffineSDP.exists_maximizer
    m hm a H A hA C hC hθ hκ
  have hlow := hmax y hy
  rw [hval] at hlow
  have hupper := RectangularRidgeSDP.feasible_value_le H (covarianceKraus A C)
    hm hθ.le hκ hf
  have he := RectangularRidgeAffineSDP.value_eq_affine m hm a H θ κ x
  change RectangularRidgeSDP.value H m θ κ hm S X Z = _ at he
  rw [he] at hupper
  exact (RectangularRidgePotential.objective_le_potential H (covarianceKraus A C)
    m θ κ hT).trans (hlow.trans hupper)

end FaithfulMS.DirectDensitySDP
