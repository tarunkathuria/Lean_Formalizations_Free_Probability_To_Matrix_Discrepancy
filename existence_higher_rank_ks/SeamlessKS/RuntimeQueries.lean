import SeamlessKS.RuntimeStateData
import SeamlessKS.RuntimeBudgets
import MatrixSpencer.RealRAMOwnerSDPPolynomialCost

/-! Counted queries to the actual seamless potential. The only opaque call is
the permitted polynomial affine-SDP solver. All matrices passed to it are
constructed by the primitive circuits in RuntimeStateData, followed by the
proved literal SDP compilation in OwnerSDPSetup. -/
open Matrix Set
open scoped BigOperators
noncomputable section
namespace SeamlessKS.RuntimeQueries
open MatrixSpencer MatrixSpencer.RealRAM
open MatrixSpencer.RealRAM.JacobiIteration (Counted)
open MatrixSpencer.KSPolynomialConvexSolver
open RuntimeStateData
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
attribute [local instance] Classical.propDecidable
variable {N d : ℕ}

/-- Two scalar comparisons and Boolean conjunction per coordinate. -/
def cubeScan (x : Fin N → ℝ) : List (Fin N) → Counted Bool
  | [] => ⟨true,1⟩
  | i::is =>
    let r := cubeScan x is
    ⟨(decide (-1≤x i) && decide (x i≤1)) && r.value,r.cost+12⟩

theorem cubeScan_value (x : Fin N → ℝ) (is : List (Fin N)) :
    (cubeScan x is).value=is.all (fun i => decide (-1≤x i) && decide (x i≤1)) := by
  induction is with
  | nil => rfl
  | cons i is ih => simp [cubeScan,ih]

theorem cubeScan_cost (x : Fin N → ℝ) (is : List (Fin N)) :
    (cubeScan x is).cost=12*is.length+1 := by
  induction is with
  | nil => rfl
  | cons i is ih => simp [cubeScan,ih];omega

def cubeTest (x : Fin N → ℝ) : Counted Bool :=
  let r := cubeScan x (List.finRange N)
  ⟨r.value,r.cost+3*N+1⟩

theorem cubeTest_value (x : Fin N → ℝ) : (cubeTest x).value=decide (x∈ksCube 1) := by
  apply Bool.eq_iff_iff.mpr
  simp only [cubeTest,cubeScan_value,List.all_eq_true,Bool.and_eq_true,decide_eq_true_eq]
  simp only [List.mem_finRange,true_implies,forall_and,ksCube,Set.mem_Icc]
  rfl

theorem cubeTest_cost (x : Fin N → ℝ) : (cubeTest x).cost=15*N+2 := by
  simp [cubeTest,cubeScan_cost];omega

theorem computed_family_isHermitian (v : Fin N → Fin d → ℂ)
    (x : Fin N → ℝ) (ζ : ℝ) (i : Fin N×Fin 4) :
    ((compute v x ζ).value.A i).IsHermitian := by
  rw [compute_A]
  exact (KSSpinSource.family_isHermitian _ (fun i => KSRankOne.atom_isHermitian (v i)) i).submatrix _

theorem computed_covariance_posSemidef (v : Fin N → Fin d → ℂ)
    (x : Fin N → ℝ) (ζ : ℝ) (hx : x∈ksCube 1) :
    (compute v x ζ).value.C.PosSemidef := by
  rw [compute_C]
  apply KSSpinSource.coefficientCovariance_posSemidef
  intro i
  exact Source.weight_nonneg (by norm_num) (abs_le.mpr ⟨hx.1 i,hx.2 i⟩)

variable [Nonempty (Fin d)]

def insideReport (P : PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (x : Fin N → ℝ) (ζ θ ν : ℝ) (hx : x∈ksCube 1) : Counted ℝ :=
  let a := compute v x ζ
  let r := OwnerSDPSetup.ownerReport P (Value.origin (n:=Fin d)) a.value.H a.value.A
    (computed_family_isHermitian v x ζ) a.value.C
    (computed_covariance_posSemidef v x ζ hx) Fintype.card_pos θ ν
  ⟨r.value,a.cost+r.cost⟩

theorem insideReport_value (P : PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (x : Fin N → ℝ) (ζ θ ν : ℝ) (hx : x∈ksCube 1) :
    (insideReport P v x ζ θ ν hx).value=
      Value.report P.solver v 0 θ ζ ν x := by
  simp only [insideReport,OwnerSDPSetup.ownerReport_value,compute_H,compute_A,compute_C,
    Value.report,dif_pos hx,KSConvexValueOracle.reindexedOwnerReport,blockIndex]

/-- The branch is exactly the cube test; outside the cube the mathematical
report is zero and no SDP is solved. -/
def report (P : PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (x : Fin N → ℝ) (ζ θ ν : ℝ) : Counted ℝ :=
  if hx : x∈ksCube 1 then
    let r := insideReport P v x ζ θ ν hx
    ⟨r.value,(cubeTest x).cost+r.cost+2⟩
  else ⟨0,(cubeTest x).cost+2⟩

theorem report_value (P : PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (x : Fin N → ℝ) (ζ θ ν : ℝ) :
    (report P v x ζ θ ν).value=
      Value.report P.solver v 0 θ ζ ν x := by
  by_cases hx : x∈ksCube 1
  · simpa only [report,dif_pos hx] using insideReport_value P v x ζ θ ν hx
  · simp only [report,dif_neg hx,Value.report]

theorem report_accuracy (P : PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (x : Fin N → ℝ) (ζ : ℝ) {θ ν : ℝ} (hx : x∈ksCube 1)
    (hθ : 0<θ) (hν : 0<ν) :
    |(report P v x ζ θ ν).value-
      KSDebitPotential.potential (StatePotential.signedSum v x)
        0 v (SourceTransport.smoothWeights ζ x) θ|≤ν := by
  rw [report_value]
  exact Value.report_accuracy P.solver v _ hθ hν x hx

def programSize (d : ℕ) := 10000*(d+1)^4

theorem programSize_bound :
    dataSize (KSFullManuscriptAffineData.dimension (Value.origin (n:=Fin d)))
      (KSFullManuscriptAffineData.matrixSize (Fin (dimension d)))≤programSize d := by
  unfold dataSize
  rw [KSConvexValueOracle.pencilEntries,KSConvexValueOracle.variableCount]
  change 400*(dimension d)^4+(4*(dimension d)^2-1)+2≤_
  have hh : 4*(dimension d)^2-1≤4*(dimension d)^2 := Nat.sub_le _ _
  calc
    _ ≤ 400*(dimension d)^4+4*(dimension d)^2+2 := by omega
    _ ≤ _ := by simp only [dimension_eq,programSize];ring_nf;omega

/-- A polynomial in the original label count, ambient dimension, and a natural
upper bound V on the reciprocal precision. The solver degree is fixed. -/
def queryBound (P : PolynomialSolver) (N d V : ℕ) : ℕ :=
  (15*N+4)+costBound N d+1000000*(4*N+(d+d)+1)^9+
    P.coefficient*(programSize d+V+1)^P.degree

theorem report_cost (P : PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (x : Fin N → ℝ) (ζ θ : ℝ) {ν : ℝ} (hν : 0<ν)
    {V : ℕ} (hV : ν⁻¹≤(V:ℝ)) :
    (report P v x ζ θ ν).cost≤queryBound P N d V := by
  by_cases hx : x∈ksCube 1
  · have hc := compute_cost v x ζ
    have hr := OwnerSDPSetup.ownerReport_cost_le P (Value.origin (n:=Fin d))
      (compute v x ζ).value.H (compute v x ζ).value.A
      (computed_family_isHermitian v x ζ) (compute v x ζ).value.C
      (computed_covariance_posSemidef v x ζ hx) Fintype.card_pos θ ν hν
      programSize_bound hV
    have hs := OwnerSDPSetup.setupCost_polynomial (Fintype.card (Fin N×Fin 4)) (dimension d)
    simp only [Fintype.card_prod,Fintype.card_fin,dimension_eq] at hr hs
    rw [Nat.mul_comm N 4] at hr hs
    simp only [report,dif_pos hx,insideReport,cubeTest_cost,queryBound]
    omega
  · simp only [report,dif_neg hx,cubeTest_cost,queryBound]
    omega

/-- State queries use exactly the account-free potential at the current coefficients. -/
theorem state_report_accuracy (P : PolynomialSolver) (v : Fin N → Fin d → ℂ)
    {ρ θ ν : ℝ} (s : State.CubeState N ρ) (ζ : ℝ) (hθ : 0<θ) (hν : 0<ν) :
    |(report P v s.coeff ζ θ ν).value-StatePotential.potential v θ ζ s|≤ν :=
  report_accuracy P v s.coeff ζ s.cube hθ hν

/-- The finite-difference value precision has an input-only polynomial cost. -/
theorem hessian_report_cost (P : PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (hd : 0<d) (hp : (∑ i,KSRankOne.atom (v i))=1)
    (x : Fin N → ℝ) :
    (report P v x (Parameters.zeta N) (Input.theta v)
      (Parameters.hessianAccuracy v)).cost≤
        queryBound P N d (RuntimeBudgets.hessianAccuracyInverseCap N d) := by
  apply report_cost P v x _ _ (Parameters.hessianAccuracy_pos v hd hp)
  simpa only [RuntimeBudgets.cast_hessianAccuracyInverseCap] using
    Parameters.hessianAccuracy_inverse_le v hd hp

/-- The local acceptance precision has an input-only polynomial cost. -/
theorem local_report_cost (P : PolynomialSolver) (v : Fin N → Fin d → ℂ)
    (hd : 0<d) (hp : (∑ i,KSRankOne.atom (v i))=1)
    (x : Fin N → ℝ) :
    (report P v x (Parameters.zeta N) (Input.theta v)
      (Parameters.localAccuracy v)).cost≤
        queryBound P N d (RuntimeBudgets.localAccuracyInverseCap N d) := by
  apply report_cost P v x _ _ (Parameters.localAccuracy_pos v hd hp)
  simpa only [RuntimeBudgets.cast_localAccuracyInverseCap] using
    Parameters.localAccuracy_inverse_le v hd hp

end SeamlessKS.RuntimeQueries
