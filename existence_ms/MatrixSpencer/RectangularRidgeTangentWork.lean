import MatrixSpencer.RectangularRidgeSolverAcceptance
import MatrixSpencer.RealRAMMSValueAcceptance

/-! Counted supporting-tangent queries. Scalar tolerances and both perturbed
centers use existing primitive real-RAM expressions. Each solver call receives
the actual mixed affine program. This local count includes solver work and
tangent arithmetic; construction of the SDP coefficient arrays is accounted
for in the separate program-construction ledger. -/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.RectangularRidgeTangentWork
open RectangularRidgeSolverCertificate RectangularRidgeTangentParameters
open RealRAM.JacobiIteration (Counted)
variable {d : ℕ} [Nonempty (Fin d)]
local instance ridgeTangentWorkCStar : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
local instance ridgeTangentWorkSpace : NormedSpace ℝ (selfAdjoint (Matrix (Fin d) (Fin d) ℂ)) := inferInstance

def baseRun (P : RectangularRidgeConvexValue.PolynomialSolver)
    (m : ℕ) (hm : 1 ≤ m) (a : Fin d) (H : Matrix (Fin d) (Fin d) ℂ) (θ κ ν : ℝ) : Counted ℝ :=
  RectangularRidgeConvexValue.run P m hm a H emptyFamily emptyFamily_hermitian
    0 Matrix.PosSemidef.zero θ κ ν

theorem baseRun_value (P : RectangularRidgeConvexValue.PolynomialSolver)
    (m : ℕ) (hm : 1 ≤ m) (a : Fin d) (H : Matrix (Fin d) (Fin d) ℂ) (θ κ ν : ℝ) :
    (baseRun P m hm a H θ κ ν).value=baseReport P.solver m hm a H θ κ ν := rfl

def tangentRun (P : RectangularRidgeConvexValue.PolynomialSolver)
    (m : ℕ) (hm : 1 ≤ m) (a : Fin d) (H X : Matrix (Fin d) (Fin d) ℂ) (θ κ R ε : ℝ) : Counted ℝ :=
  RealRAM.MSValueAcceptance.tangent (fun K ν => baseRun P m hm a K θ κ ν) H X κ R ε

theorem tangentRun_value (P : RectangularRidgeConvexValue.PolynomialSolver)
    (m : ℕ) (hm : 1 ≤ m) (a : Fin d)
    (H X : selfAdjoint (Matrix (Fin d) (Fin d) ℂ)) (θ κ R ε : ℝ) :
    (tangentRun P m hm a H X θ κ R ε).value=tangentReport P.solver m hm a H X θ κ R ε := by
  simp only [tangentRun,RealRAM.MSValueAcceptance.tangent,RealRAM.MSValueAcceptance.parameters_value,
    RealRAM.MSValueAcceptance.shift_value,baseRun_value,RealRAM.MSValueAcceptance.slope_value,
    neg_smul]
  rfl

def queryBound (P : RectangularRidgeConvexValue.PolynomialSolver) (d V : ℕ) : ℕ :=
  P.coefficient*(16*(2*d+3)*(d+4)*d^4+(d+4)*d^2+2+V+1)^P.degree

/-- Arithmetic cost of the reused finite routine, with no square-potential
oracle instance in its type. -/
theorem finite_tangent_cost (q : Matrix (Fin d) (Fin d) ℂ → ℝ → Counted ℝ)
    (H X : Matrix (Fin d) (Fin d) ℂ) (κ R ε : ℝ) {Q : ℕ}
    (hq : ∀K, (q K (RectangularRidgeTangentValues.precision κ R ε)).cost≤Q) :
    (RealRAM.MSValueAcceptance.tangent q H X κ R ε).cost≤2*Q+32*d*d+70 := by
  have h1 := hq (H+MSConvexAnchorTangent.spacing κ R ε • X)
  have h2 := hq (H+(-MSConvexAnchorTangent.spacing κ R ε) • X)
  have hp := RealRAM.MSValueAcceptance.parameters_cost κ R ε
  have hs := RealRAM.MSValueAcceptance.slope_cost
    (q (H+MSConvexAnchorTangent.spacing κ R ε • X) (MSConvexAnchorTangent.precision κ R ε)).value
    (q (H+(-MSConvexAnchorTangent.spacing κ R ε) • X) (MSConvexAnchorTangent.precision κ R ε)).value
    (MSConvexAnchorTangent.spacing κ R ε)
  change (q (H+MSConvexAnchorTangent.spacing κ R ε • X)
    (MSConvexAnchorTangent.precision κ R ε)).cost≤Q at h1
  change (q (H+(-MSConvexAnchorTangent.spacing κ R ε) • X)
    (MSConvexAnchorTangent.precision κ R ε)).cost≤Q at h2
  simp only [RealRAM.MSValueAcceptance.tangent,RealRAM.MSValueAcceptance.parameters_value,
    RealRAM.MSValueAcceptance.shift_value,RealRAM.MSValueAcceptance.shift_cost]
  nlinarith

theorem primitive_baseRun_cost (P : RectangularRidgeConvexValue.PolynomialSolver)
    {N : ℕ} (hN : 1≤N) (a : Fin d) (H : Matrix (Fin d) (Fin d) ℂ) (θ κ : ℝ)
    {ν : ℝ} (hν : 0<ν) {V : ℕ} (hV : ν⁻¹≤(V : ℝ)) :
    (baseRun P (RectangularRidgeTuning.depth N d hN) (RectangularRidgeTuning.depth_positive N d hN)
      a H θ κ ν).cost≤queryBound P d V :=
  RectangularRidgeConvexValue.primitive_run_cost_le P hN a H emptyFamily
    emptyFamily_hermitian 0 Matrix.PosSemidef.zero θ κ hν hV

/-- No derivative or accuracy parameter is free in this bound: the requested
precision is the fixed polynomial formula proved for the actual tangent. -/
theorem primitive_tangentRun_cost (P : RectangularRidgeConvexValue.PolynomialSolver)
    {N : ℕ} (hN : 1≤N) (a : Fin d) (H X : Matrix (Fin d) (Fin d) ℂ) (θ : ℝ) :
    (tangentRun P (RectangularRidgeTuning.depth N d hN) (RectangularRidgeTuning.depth_positive N d hN)
      a H X θ (1/(d : ℝ)) (radius ((d+N+2 : ℕ) : ℝ)) tolerance).cost≤
      2*queryBound P d (68400000000*(d+N+2)^5)+32*d*d+70 := by
  have hd : 1≤d := by have := a.isLt; omega
  have hs : (1:ℝ)≤((d+N+2 : ℕ):ℝ) := by exact_mod_cast (by omega : 1≤d+N+2)
  have hd' : (1:ℝ)≤d := by exact_mod_cast hd
  have hds : (d:ℝ)≤((d+N+2 : ℕ):ℝ) := by exact_mod_cast (by omega : d≤d+N+2)
  have hν := RectangularRidgeTangentValues.precision_pos
    (R:=radius ((d+N+2 : ℕ):ℝ)) (by positivity : 0<1/(d : ℝ))
    (by norm_num [tolerance] : 0<tolerance)
  have hi := (fixed_inverse_bounds hs hd' hds).2
  have hcast : (((68400000000*(d+N+2)^5 : ℕ):ℝ))=68400000000*((d+N+2 : ℕ):ℝ)^5 := by push_cast; ring
  have hV : (RectangularRidgeTangentValues.precision (1/(d : ℝ))
      (radius ((d+N+2 : ℕ):ℝ)) tolerance)⁻¹≤((68400000000*(d+N+2)^5 : ℕ):ℝ) := by
    rw [hcast]
    exact hi
  exact finite_tangent_cost _ H X (1/(d : ℝ)) _ _
    (fun K => primitive_baseRun_cost P hN a K θ (1/(d : ℝ)) hν hV)

end MatrixSpencer.RectangularRidgeTangentWork
