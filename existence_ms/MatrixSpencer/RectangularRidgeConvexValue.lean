import MatrixSpencer.RectangularRidgePrimitiveSDP
import MatrixSpencer.RealRAMJacobiIteration

/-! Accurate values of the actual rectangular mixed SDP, from the permitted
polynomial convex solver. Its input is the explicit finite family of affine
real PSD pencils and affine objective. The solver contract concerns only
an attained convex optimum; it assumes no derivative, walk, or signing fact.
The runtime below charges solving materialized arrays. Their construction
and the number of calls are separate parts of the execution ledger. -/

open Matrix Set
open scoped BigOperators InnerProductSpace MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.RectangularRidgeConvexValue
open KSFullManuscriptAffinePSD
open RealRAM.JacobiIteration (Counted)

def feasible {β : Type} [Fintype β] {ℓ k : ℕ} (D : β → Data ℓ k) : Set (Space ℓ) :=
  {x | ∀ b, x ∈ target (D b)}

def dataSize (b ℓ k : ℕ) : ℕ := b*(ℓ+1)*k^2+ℓ+2


structure Solver where
  report : {β : Type} → [Fintype β] → {ℓ k : ℕ} →
    (β → Data ℓ k) → Space ℓ → ℝ → ℝ → ℝ
  accuracy : ∀ {β : Type} [Fintype β] {ℓ k : ℕ} (D : β → Data ℓ k)
    (c : Space ℓ) (offset ν : ℝ), 0 < ν → ∀ x ∈ feasible D,
    (∀ y ∈ feasible D, offset+⟪c,y⟫_ℝ ≤ offset+⟪c,x⟫_ℝ) →
    |report D c offset ν-(offset+⟪c,x⟫_ℝ)| ≤ ν

structure PolynomialSolver where
  solver : Solver
  work : {β : Type} → [Fintype β] → {ℓ k : ℕ} →
    (β → Data ℓ k) → Space ℓ → ℝ → ℝ → ℕ
  coefficient : ℕ
  degree : ℕ
  bound : ∀ {β : Type} [Fintype β] {ℓ k : ℕ} (D : β → Data ℓ k)
    (c : Space ℓ) (offset ν : ℝ), 0 < ν →
    work D c offset ν ≤ coefficient*(dataSize (Fintype.card β) ℓ k+⌈ν⁻¹⌉₊+1)^degree

def PolynomialSolver.run (P : PolynomialSolver) {β : Type} [Fintype β] {ℓ k : ℕ}
    (D : β → Data ℓ k) (c : Space ℓ) (offset ν : ℝ) : Counted ℝ :=
  ⟨P.solver.report D c offset ν, P.work D c offset ν⟩

theorem PolynomialSolver.run_cost_le (P : PolynomialSolver) {β : Type} [Fintype β]
    {ℓ k : ℕ} (D : β → Data ℓ k) (c : Space ℓ) (offset : ℝ) {ν : ℝ} (hν : 0<ν)
    {S V : ℕ} (hS : dataSize (Fintype.card β) ℓ k≤S) (hV : ν⁻¹≤(V : ℝ)) :
    (P.run D c offset ν).cost≤P.coefficient*(S+V+1)^P.degree := by
  have hv : ⌈ν⁻¹⌉₊≤V := Nat.ceil_le.mpr hV
  apply (P.bound D c offset ν hν).trans
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)

variable {d : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

def ownerData (m : ℕ) (a : Fin d) (A : ι → Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀ i, (A i).IsHermitian) (C : Matrix ι ι ℝ) (hC : C.PosSemidef) :=
  DyadicSDPAffineData.data m a A hA C hC (DyadicOwnerSDP.center a)

def report (O : Solver) (m : ℕ) (hm : 1≤m) (a : Fin d)
    (H : Matrix (Fin d) (Fin d) ℂ) (A : ι → Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀ i, (A i).IsHermitian) (C : Matrix ι ι ℝ) (hC : C.PosSemidef)
    (θ κ ν : ℝ) : ℝ :=
  O.report (ownerData m a A hA C hC)
    (RectangularRidgeAffineSDP.coefficient m hm a H θ κ)
    (RectangularRidgeAffineSDP.offset m hm a H θ κ) ν

theorem report_accuracy (O : Solver) (m : ℕ) (hm : 1≤m) (a : Fin d)
    (H : Matrix (Fin d) (Fin d) ℂ) (A : ι → Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀ i, (A i).IsHermitian) (C : Matrix ι ι ℝ) (hC : C.PosSemidef)
    {θ κ ν : ℝ} (hθ : 0<θ) (hκ : 0≤κ) (hν : 0<ν) :
    |report O m hm a H A hA C hC θ κ ν-
      RectangularRidgePotential.potential H (covarianceKraus A C) m θ κ|≤ν := by
  obtain ⟨x,hx,hval,hmax⟩ := RectangularRidgeAffineSDP.exists_maximizer m hm a H A hA C hC hθ hκ
  have hh := O.accuracy (ownerData m a A hA C hC)
    (RectangularRidgeAffineSDP.coefficient m hm a H θ κ)
    (RectangularRidgeAffineSDP.offset m hm a H θ κ) ν hν x hx hmax
  change |report O m hm a H A hA C hC θ κ ν-
    RectangularRidgeAffineSDP.objective m hm a H θ κ x|≤ν at hh
  rwa [hval] at hh

/-- The coefficient arrays, objective vector, and offset used by this exact
query have fixed-degree polynomial size at the actual comparison-tuned depth. -/
theorem primitive_dataSize_le {N d : ℕ} (hN : 1≤N) (a : Fin d) :
    let m := RectangularRidgeTuning.depth N d hN
    dataSize (Fintype.card (DyadicSDPAffineData.Constraint m))
      (DyadicSDPCoordinates.dimension m a) (DyadicSDPAffineData.matrixSize (Fin d)) ≤
      16*(2*d+3)*(d+4)*d^4+(d+4)*d^2+2 := by
  have h := RectangularRidgePrimitiveSDP.actual_size_bounds hN a
  dsimp only [dataSize]
  omega

def run (P : PolynomialSolver) (m : ℕ) (hm : 1≤m) (a : Fin d)
    (H : Matrix (Fin d) (Fin d) ℂ) (A : ι → Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀ i, (A i).IsHermitian) (C : Matrix ι ι ℝ) (hC : C.PosSemidef)
    (θ κ ν : ℝ) : Counted ℝ :=
  P.run (ownerData m a A hA C hC)
    (RectangularRidgeAffineSDP.coefficient m hm a H θ κ)
    (RectangularRidgeAffineSDP.offset m hm a H θ κ) ν

theorem run_value (P : PolynomialSolver) (m : ℕ) (hm : 1≤m) (a : Fin d)
    (H : Matrix (Fin d) (Fin d) ℂ) (A : ι → Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀ i, (A i).IsHermitian) (C : Matrix ι ι ℝ) (hC : C.PosSemidef) (θ κ ν : ℝ) :
    (run P m hm a H A hA C hC θ κ ν).value=report P.solver m hm a H A hA C hC θ κ ν := rfl

theorem primitive_run_cost_le (P : PolynomialSolver) {N : ℕ} (hN : 1≤N)
    (a : Fin d) (H : Matrix (Fin d) (Fin d) ℂ) (A : ι → Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀ i, (A i).IsHermitian) (C : Matrix ι ι ℝ) (hC : C.PosSemidef)
    (θ κ : ℝ) {ν : ℝ} (hν : 0<ν) {V : ℕ} (hV : ν⁻¹≤(V : ℝ)) :
    (run P (RectangularRidgeTuning.depth N d hN) (RectangularRidgeTuning.depth_positive N d hN)
      a H A hA C hC θ κ ν).cost ≤
      P.coefficient*(16*(2*d+3)*(d+4)*d^4+(d+4)*d^2+2+V+1)^P.degree :=
  P.run_cost_le _ _ _ hν (primitive_dataSize_le hN a) hV

end MatrixSpencer.RectangularRidgeConvexValue
