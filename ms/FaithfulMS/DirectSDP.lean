import FaithfulMS.DirectDensitySDP
import MatrixSpencer.RectangularRidgeConvexValue

/-!
# The permitted exact primal SDP service

This is an arithmetic-model primitive. Its input consists solely of affine
real PSD pencils, an objective vector, and an offset. When that program has
an attained maximum, the returned point is feasible and maximizing. It is
not a derivative, stability, covariance-selection, or signing oracle.

Exact primal optimization and its polynomial work bound are deliberately
explicit assumptions. Neither is asserted to follow from finite-precision
ellipsoid/IPM theory. The walk and the density-to-response computation are
proved outside this interface.
-/

open Matrix Set
open scoped BigOperators InnerProductSpace MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace FaithfulMS.DirectSDP
open MatrixSpencer KSFullManuscriptAffinePSD

def feasible {β : Type} [Fintype β] {ℓ k : ℕ} (D : β → Data ℓ k) : Set (Space ℓ) :=
  {x | ∀ b, x ∈ target (D b)}

def dataSize (b ℓ k : ℕ) : ℕ := b * (ℓ + 1) * k ^ 2 + ℓ + 2

structure Service where
  solve : {β : Type} → [Fintype β] → {ℓ k : ℕ} →
    (β → Data ℓ k) → Space ℓ → ℝ → Space ℓ
  optimal : ∀ {β : Type} [Fintype β] {ℓ k : ℕ} (D : β → Data ℓ k)
    (c : Space ℓ) (offset : ℝ),
    (∃ x ∈ feasible D, ∀ y ∈ feasible D,
      offset + ⟪c, y⟫_ℝ ≤ offset + ⟪c, x⟫_ℝ) →
    solve D c offset ∈ feasible D ∧
      ∀ y ∈ feasible D, offset + ⟪c, y⟫_ℝ ≤ offset + ⟪c, solve D c offset⟫_ℝ

structure PolynomialService where
  service : Service
  work : {β : Type} → [Fintype β] → {ℓ k : ℕ} →
    (β → Data ℓ k) → Space ℓ → ℝ → ℕ
  coefficient : ℕ
  degree : ℕ
  bound : ∀ {β : Type} [Fintype β] {ℓ k : ℕ} (D : β → Data ℓ k)
    (c : Space ℓ) (offset : ℝ),
    work D c offset ≤ coefficient * (dataSize (Fintype.card β) ℓ k + 1) ^ degree

def PolynomialService.run (P : PolynomialService) {β : Type} [Fintype β] {ℓ k : ℕ}
    (D : β → Data ℓ k) (c : Space ℓ) (offset : ℝ) : RealRAM.JacobiIteration.Counted (Space ℓ) :=
  ⟨P.service.solve D c offset, P.work D c offset⟩

theorem PolynomialService.run_cost_le (P : PolynomialService) {β : Type} [Fintype β]
    {ℓ k : ℕ} (D : β → Data ℓ k) (c : Space ℓ) (offset : ℝ) {B : ℕ}
    (hB : dataSize (Fintype.card β) ℓ k ≤ B) :
    (P.run D c offset).cost ≤ P.coefficient * (B + 1) ^ P.degree :=
  (P.bound D c offset).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right hB 1) _))

variable {ι : Type} [Fintype ι] [DecidableEq ι] {d : ℕ}

def squareData (a : Fin d) (A : ι → Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀ i, (A i).IsHermitian) (C : Matrix ι ι ℝ) (hC : C.PosSemidef)
    (hd : 0 < d) : Unit → Data (KSFullManuscriptAffineData.dimension a)
      (KSFullManuscriptAffineData.matrixSize (Fin d)) :=
  fun _ => KSConvexValueOracle.ownerData a A hA C hC hd

def Service.squareSolution (O : Service) (H : Matrix (Fin d) (Fin d) ℂ)
    (A : ι → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ i, (A i).IsHermitian)
    (C : Matrix ι ι ℝ) (hC : C.PosSemidef) (hd : 0 < d)
    (θ : ℝ) (hθ : 0 < θ) : DirectDensity.SquareSolution H A C θ := by
  let a : Fin d := ⟨0, hd⟩
  let S₀ := KSFullManuscriptCenterData.densityCenter hd
  let D := squareData a A hA C hC hd
  let c := KSFullManuscriptAffineObjective.coefficient a H θ
  let offset := KSFullManuscriptAffineObjective.offset H θ S₀ 0
  let x := O.solve D c offset
  have hfeas (y : KSFullManuscriptAffineData.Space a) :
      y ∈ feasible D ↔ y ∈ target (OwnerSDPProgramSize.data a A hA C hC S₀ 0 0) := by
    simp only [feasible, Set.mem_setOf_eq, D, squareData, KSConvexValueOracle.ownerData,
      S₀, forall_const]
  have hopt := O.optimal D c offset (by
    obtain ⟨y, hy, _, hmax⟩ := OwnerSDPProgramSize.exists_maximizer
      a H A hA C hC S₀ 0 (KSFullManuscriptStrictFeasible.density_trace hd) hθ
    exact ⟨y, (hfeas y).mpr hy, fun z hz => hmax z ((hfeas z).mp hz)⟩)
  exact DirectDensitySDP.squareOfAffine a H A hA C hC S₀ 0
    (KSFullManuscriptStrictFeasible.density_trace hd) θ hθ x
    ((hfeas x).mp hopt.1) (fun y hy => hopt.2 y ((hfeas y).mpr hy))

def Service.rectangularSolution (O : Service) (m : ℕ) (hm : 1 ≤ m)
    (H : Matrix (Fin d) (Fin d) ℂ) (A : ι → Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀ i, (A i).IsHermitian) (C : Matrix ι ι ℝ) (hC : C.PosSemidef)
    (hd : 0 < d) (θ κ : ℝ) (hθ : 0 < θ) (hκ : 0 ≤ κ) :
    DirectDensity.RectangularSolution H A C m θ κ := by
  let a : Fin d := ⟨0, hd⟩
  let D := RectangularRidgeConvexValue.ownerData m a A hA C hC
  let c := RectangularRidgeAffineSDP.coefficient m hm a H θ κ
  let offset := RectangularRidgeAffineSDP.offset m hm a H θ κ
  let x := O.solve D c offset
  have hfeas (y : DyadicSDPCoordinates.Space m a) :
      y ∈ feasible D ↔ y ∈ DyadicOwnerSDP.feasible m a A hA C hC := Iff.rfl
  have hopt := O.optimal D c offset (by
    obtain ⟨y, hy, _, hmax⟩ := RectangularRidgeAffineSDP.exists_maximizer
      m hm a H A hA C hC hθ hκ
    exact ⟨y, (hfeas y).mpr hy, fun z hz => hmax z ((hfeas z).mp hz)⟩)
  exact DirectDensitySDP.rectangularOfAffine m hm a H A hA C hC θ κ hθ hκ x
    ((hfeas x).mp hopt.1) (fun y hy => hopt.2 y ((hfeas y).mpr hy))


attribute [local instance] Classical.propDecidable

/-- Mathematical primal solution selection for existence-only proofs. This
uses classical choice on an attained maximum and carries no computational
cost or polynomial solvability claim. -/
def exactService : Service where
  solve D c offset := if h : ∃ x ∈ feasible D, ∀ y ∈ feasible D,
      offset + ⟪c, y⟫_ℝ ≤ offset + ⟪c, x⟫_ℝ then Classical.choose h else 0
  optimal D c offset h := by
    simp only [dif_pos h]
    exact Classical.choose_spec h

end FaithfulMS.DirectSDP
