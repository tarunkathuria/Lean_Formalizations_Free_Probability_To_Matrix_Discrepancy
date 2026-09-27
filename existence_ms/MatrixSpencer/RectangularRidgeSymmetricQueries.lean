import MatrixSpencer.RectangularRidgeConvexValue
import MatrixSpencer.CovarianceCalculus

/-! A total finite affine-program query on symmetric coefficient matrices.
No PSD decision or optimizer selection is performed by this query. Positive
semidefiniteness is needed only in the theorem identifying its optimum. This
allows every rank-one finite difference to use the same numerical routine. -/

open Matrix
open scoped BigOperators InnerProductSpace MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.RectangularRidgeSymmetricQueries
open DyadicSDPCoordinates DyadicSDPAffineData KSFullManuscriptSDPBlockPencil
open KSComplexTraceSqrt KSComplexProjectionGeometry
variable {d : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

theorem block_hermitian (A : ι → Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀ i, (A i).IsHermitian) (C : selfAdjoint (Matrix ι ι ℝ)) (m : ℕ)
    {S : Matrix (Fin d) (Fin d) ℂ} (hS : S.IsHermitian)
    {X : Fin (m+1) → Matrix (Fin d) (Fin d) ℂ} (hX : ∀ j, (X j).IsHermitian)
    (Z : Matrix (Fin d) (Fin d) ℂ) (b : Constraint m) :
    (block A C m S X Z b).IsHermitian := by
  rcases b with u | (j|j)
  · exact Matrix.IsHermitian.fromBlocks hS rfl (covarianceSource_isHermitian A hA C ⟨S,hS⟩)
  · exact Matrix.IsHermitian.fromBlocks hS (hX j.succ).eq (hX j.castSucc)
  · exact Matrix.IsHermitian.fromBlocks (hX j.succ) (by simp) Matrix.isHermitian_zero

def data (m : ℕ) (a : Fin d) (A : ι → Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀ i, (A i).IsHermitian) (C : selfAdjoint (Matrix ι ι ℝ))
    (b : Constraint m) : KSFullManuscriptAffinePSD.Data (dimension m a) (matrixSize (Fin d)) where
  constant := constant m a A C (DyadicOwnerSDP.center a) b
  coefficient i := finiteLinear m a A C b (unit m a i)
  constant_symmetric := (realification_symmetric _
    (block_hermitian A hA C m (DyadicOwnerSDP.center a).property
      (chain_hermitian m a 0) 0 b)).submatrix _
  coefficient_symmetric i := (realification_symmetric _
    (block_hermitian A hA C m (densityLinear m a _).property
      (chainLinear_hermitian m a _) _ b)).submatrix _

theorem data_eq (m : ℕ) (a : Fin d) (A : ι → Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀ i, (A i).IsHermitian) (C : selfAdjoint (Matrix ι ι ℝ))
    (hC : (C : Matrix ι ι ℝ).PosSemidef) :
    data m a A hA C=RectangularRidgeConvexValue.ownerData m a A hA C hC := rfl

def report (O : RectangularRidgeConvexValue.Solver) (m : ℕ) (hm : 1≤m) (a : Fin d)
    (H : Matrix (Fin d) (Fin d) ℂ) (A : ι → Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀ i, (A i).IsHermitian) (C : selfAdjoint (Matrix ι ι ℝ)) (θ κ ν : ℝ) : ℝ :=
  O.report (data m a A hA C) (RectangularRidgeAffineSDP.coefficient m hm a H θ κ)
    (RectangularRidgeAffineSDP.offset m hm a H θ κ) ν

theorem report_accuracy (O : RectangularRidgeConvexValue.Solver)
    (m : ℕ) (hm : 1≤m) (a : Fin d) (H : Matrix (Fin d) (Fin d) ℂ)
    (A : ι → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ i, (A i).IsHermitian)
    (C : selfAdjoint (Matrix ι ι ℝ)) (hC : (C : Matrix ι ι ℝ).PosSemidef)
    {θ κ ν : ℝ} (hθ : 0<θ) (hκ : 0≤κ) (hν : 0<ν) :
    |report O m hm a H A hA C θ κ ν-
      RectangularRidgePotential.potential H (covarianceKraus A C) m θ κ|≤ν :=
  RectangularRidgeConvexValue.report_accuracy O m hm a H A hA C hC hθ hκ hν

def run (P : RectangularRidgeConvexValue.PolynomialSolver) (m : ℕ) (hm : 1≤m) (a : Fin d)
    (H : Matrix (Fin d) (Fin d) ℂ) (A : ι → Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀ i, (A i).IsHermitian) (C : selfAdjoint (Matrix ι ι ℝ)) (θ κ ν : ℝ) :
    RealRAM.JacobiIteration.Counted ℝ :=
  P.run (data m a A hA C) (RectangularRidgeAffineSDP.coefficient m hm a H θ κ)
    (RectangularRidgeAffineSDP.offset m hm a H θ κ) ν

theorem primitive_run_cost_le (P : RectangularRidgeConvexValue.PolynomialSolver)
    {N : ℕ} (hN : 1≤N) (a : Fin d) (H : Matrix (Fin d) (Fin d) ℂ)
    (A : ι → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ i, (A i).IsHermitian)
    (C : selfAdjoint (Matrix ι ι ℝ)) (θ κ : ℝ) {ν : ℝ} (hν : 0<ν)
    {V : ℕ} (hV : ν⁻¹≤(V : ℝ)) :
    (run P (RectangularRidgeTuning.depth N d hN) (RectangularRidgeTuning.depth_positive N d hN)
      a H A hA C θ κ ν).cost≤
      P.coefficient*(16*(2*d+3)*(d+4)*d^4+(d+4)*d^2+2+V+1)^P.degree :=
  P.run_cost_le _ _ _ hν (RectangularRidgeConvexValue.primitive_dataSize_le hN a) hV

end MatrixSpencer.RectangularRidgeSymmetricQueries
