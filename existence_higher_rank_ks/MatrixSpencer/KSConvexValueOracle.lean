import MatrixSpencer.OwnerSDPProgramSize
import MatrixSpencer.KSOwnerReindex

/-!
# The permitted convex value solver and explicit owner-value queries

The sole solver contract is accuracy for the attained maximum of the supplied
affine objective on its supplied affine PSD region. No walk, derivative,
curvature, termination, or signing property is assumed. The query data below
are the actual direct covariance pencil, with polynomial size. Its maximum
is proved equal to the owner potential. This interface does not assign a
unit cost to the previously implemented finite ellipsoid algorithm.
-/

open Matrix
open scoped BigOperators InnerProductSpace MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSConvexValueOracle
open KSFullManuscriptAffinePSD KSFullManuscriptAffineData
open KSFullManuscriptAffineObjective KSFullManuscriptSDPBlockPencil

/-- A value solver for an explicit affine semidefinite program. Its output
function receives only the program and requested error, never a maximizer. -/
structure Solver where
  report : {ℓ k : ℕ} → Data ℓ k → KSFullManuscriptAffinePSD.Space ℓ → ℝ → ℝ → ℝ
  accuracy : ∀ {ℓ k : ℕ} (D : Data ℓ k) (c : KSFullManuscriptAffinePSD.Space ℓ)
    (offset ν : ℝ), 0 < ν → ∀ x ∈ target D,
      (∀ y ∈ target D, offset + ⟪c,y⟫_ℝ ≤ offset + ⟪c,x⟫_ℝ) →
        |report D c offset ν - (offset + ⟪c,x⟫_ℝ)| ≤ ν

variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

def ownerData (a : Fin d) (A : ι → Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀ i, (A i).IsHermitian) (C : Matrix ι ι ℝ) (hC : C.PosSemidef) (hd : 0 < d) :
    Data (dimension a) (matrixSize (Fin d)) :=
  OwnerSDPProgramSize.data a A hA C hC (KSFullManuscriptCenterData.densityCenter hd) 0 0

def ownerReport (O : Solver) (a : Fin d) (H : Matrix (Fin d) (Fin d) ℂ)
    (A : ι → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ i, (A i).IsHermitian)
    (C : Matrix ι ι ℝ) (hC : C.PosSemidef) (hd : 0 < d) (θ ν : ℝ) : ℝ :=
  O.report (ownerData a A hA C hC hd) (coefficient a H θ)
    (offset H θ (KSFullManuscriptCenterData.densityCenter hd) 0) ν

theorem ownerData_convex (a : Fin d) (A : ι → Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀ i, (A i).IsHermitian) (C : Matrix ι ι ℝ) (hC : C.PosSemidef) (hd : 0 < d) :
    Convex ℝ (target (ownerData a A hA C hC hd)) :=
  OwnerSDPProgramSize.convex_target a A hA C hC _ 0 0

theorem ownerReport_accuracy (O : Solver) (a : Fin d) (H : Matrix (Fin d) (Fin d) ℂ)
    (A : ι → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ i, (A i).IsHermitian)
    (C : Matrix ι ι ℝ) (hC : C.PosSemidef) (hd : 0 < d)
    {θ ν : ℝ} (hθ : 0 < θ) (hν : 0 < ν) :
    |ownerReport O a H A hA C hC hd θ ν - ownerPotential H A C θ| ≤ ν := by
  obtain ⟨x,hx,hval,hmax⟩ := OwnerSDPProgramSize.exists_maximizer a H A hA C hC
    (KSFullManuscriptCenterData.densityCenter hd) 0
    (KSFullManuscriptStrictFeasible.density_trace hd) hθ
  have h := O.accuracy (ownerData a A hA C hC hd) (coefficient a H θ)
    (offset H θ (KSFullManuscriptCenterData.densityCenter hd) 0) ν hν x hx hmax
  simpa only [ownerReport,hval] using h

variable {n : Type*} [Fintype n] [DecidableEq n]

def reindexedOwnerReport (O : Solver) (a : Fin d) (e : Fin d ≃ n) (H : Matrix n n ℂ)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (C : Matrix ι ι ℝ) (hC : C.PosSemidef) (hd : 0 < d) (θ ν : ℝ) : ℝ :=
  ownerReport O a (H.submatrix e e) (fun i => (A i).submatrix e e)
    (fun i => (hA i).submatrix e) C hC hd θ ν

theorem reindexedOwnerReport_accuracy (O : Solver) (a : Fin d) (e : Fin d ≃ n)
    (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (C : Matrix ι ι ℝ) (hC : C.PosSemidef) (hd : 0 < d)
    {θ ν : ℝ} (hθ : 0 < θ) (hν : 0 < ν) :
    |reindexedOwnerReport O a e H A hA C hC hd θ ν - ownerPotential H A C θ| ≤ ν := by
  have h := ownerReport_accuracy O a (H.submatrix e e) (fun i => (A i).submatrix e e)
    (fun i => (hA i).submatrix e) C hC hd hθ hν
  rwa [KSOwnerReindex.ownerPotential_reindex H A hA hC θ e] at h

theorem variableCount (a : Fin d) : dimension a = 4*d^2-1 :=
  KSFullManuscriptProgramSize.variableCount a

theorem pencilOrder : matrixSize (Fin d) = 10*d := KSFullManuscriptProgramSize.pencilOrder

theorem pencilEntries (a : Fin d) : (dimension a+1)*matrixSize (Fin d)^2 = 400*d^4 :=
  KSFullManuscriptProgramSize.pencilEntries a

end MatrixSpencer.KSConvexValueOracle
