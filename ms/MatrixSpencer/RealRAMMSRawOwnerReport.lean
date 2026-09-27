import MatrixSpencer.RealRAMMSOwnerReport

/-! Total raw owner-SDP compiler for the numerical MS callback. Symmetrizing
each real pencil coefficient makes its symmetry structural on every input.
No Hermitian or PSD predicate is executed. On valid numerical queries this
changes no coefficient, objective, value or accuracy statement. -/
open Matrix
open scoped BigOperators
noncomputable section
namespace MatrixSpencer.RealRAM.MSRawOwnerReport
open JacobiIteration (Counted)
open OwnerSDPSetup OwnerSDPBlocks
open KSFullManuscriptAffineData
variable {ι : Type} [Fintype ι] [DecidableEq ι] {d : ℕ}
set_option maxRecDepth 4096
set_option maxHeartbeats 1500000

def entry (a : Fin d) (k : QueryIndex a) (i j : Fin (matrixSize (Fin d))) :
    Expr (Reg (ι:=ι) (d:=d)) :=
  .div (.add (pencilExpr a k i j) (pencilExpr a k j i)) (.constant 2)

theorem entry_valid (a : Fin d) (v : Reg (ι:=ι) (d:=d)→ℝ) (hd : 0<d)
    (k : QueryIndex a) (i j) : (entry a k i j).Valid v := by
  exact ⟨⟨pencilExpr_valid a v hd k i j,pencilExpr_valid a v hd k j i⟩,
    trivial,by norm_num [Expr.eval]⟩

theorem entry_cost (a : Fin d) (k : QueryIndex a) (i j) :
    (entry (ι:=ι) a k i j).cost≤2*blockBound (Fintype.card ι) d+7 := by
  have h₁ := pencilExpr_cost (ι:=ι) a k i j
  have h₂ := pencilExpr_cost (ι:=ι) a k j i
  simp only [entry,Expr.cost]
  omega

def matrix (a : Fin d) (v : Reg (ι:=ι) (d:=d)→ℝ) (k : QueryIndex a) :=
  Matrix.of (fun i j => (entry a k i j).eval v)

theorem matrix_symmetric (a : Fin d) (v : Reg (ι:=ι) (d:=d)→ℝ) (k : QueryIndex a) :
    (matrix a v k).IsSymm := by
  ext i j
  simp only [matrix,Matrix.transpose_apply,Matrix.of_apply,entry,Expr.eval]
  ring

def data (a : Fin d) (v : Reg (ι:=ι) (d:=d)→ℝ) :
    KSFullManuscriptAffinePSD.Data (dimension a) (matrixSize (Fin d)) where
  constant := matrix a v none
  coefficient k := matrix a v (some k)
  constant_symmetric := matrix_symmetric a v none
  coefficient_symmetric k := matrix_symmetric a v (some k)

theorem matrix_eq (a : Fin d) (H : Matrix (Fin d) (Fin d) ℂ)
    (A : ι→Matrix (Fin d) (Fin d) ℂ) (hA : ∀i,(A i).IsHermitian)
    (C : Matrix ι ι ℝ) (hC : C.PosSemidef) (θ : ℝ) (hd : 0<d) (k : QueryIndex a) :
    matrix a (input H A C θ) k = match k with
      | none => (KSConvexValueOracle.ownerData a A hA C hC hd).constant
      | some k => (KSConvexValueOracle.ownerData a A hA C hC hd).coefficient k := by
  let D := KSConvexValueOracle.ownerData a A hA C hC hd
  have hs : (match k with | none => D.constant | some k => D.coefficient k).IsSymm := by
    cases k
    · exact D.constant_symmetric
    · exact D.coefficient_symmetric _
  ext i j
  have hij := congrFun (congrFun hs i) j
  change (match k with | none => D.constant | some k => D.coefficient k) j i =
    (match k with | none => D.constant | some k => D.coefficient k) i j at hij
  change ((pencilExpr a k i j).eval (input H A C θ)+
    (pencilExpr a k j i).eval (input H A C θ))/(2:ℝ)=_
  rw [pencilExpr_eval _ _ _ _ _ hd,pencilExpr_eval _ _ _ _ _ hd]
  change ((match k with | none => D.constant | some k => D.coefficient k) i j+
    (match k with | none => D.constant | some k => D.coefficient k) j i)/(2:ℝ)=_
  rw [hij]
  ring

theorem data_eq (a : Fin d) (H : Matrix (Fin d) (Fin d) ℂ)
    (A : ι→Matrix (Fin d) (Fin d) ℂ) (hA : ∀i,(A i).IsHermitian)
    (C : Matrix ι ι ℝ) (hC : C.PosSemidef) (θ : ℝ) (hd : 0<d) :
    data a (input H A C θ)=KSConvexValueOracle.ownerData a A hA C hC hd := by
  have hc := matrix_eq a H A hA C hC θ hd none
  have hl := funext (fun k => matrix_eq a H A hA C hC θ hd (some k))
  cases he : data a (input H A C θ) with
  | mk const coeff hs ht =>
    have hc' : const=(KSConvexValueOracle.ownerData a A hA C hC hd).constant := by
      exact (congrArg KSFullManuscriptAffinePSD.Data.constant he).symm.trans hc
    have hl' : coeff=(KSConvexValueOracle.ownerData a A hA C hC hd).coefficient := by
      exact (congrArg KSFullManuscriptAffinePSD.Data.coefficient he).symm.trans hl
    subst const
    subst coeff
    rfl

def pencilCircuit (a : Fin d) :
    Circuit (Reg (ι:=ι) (d:=d)) (QueryIndex a×Fin (matrixSize (Fin d))×Fin (matrixSize (Fin d))) :=
  ⟨fun p => entry a p.1 p.2.1 p.2.2⟩

def compilationCost (a : Fin d) : ℕ :=
  2*((pencilCircuit (ι:=ι) a).cost+(objectiveCircuit (ι:=ι) a).cost)+
    200*(Fintype.card ι+d+1)^4

def setupCost (r d : ℕ) : ℕ :=
  2*((4*d^2+1)*(10*d)^2*(2*blockBound r d+8)+
    (4*d^2+1)*(objectiveBound d+1))+200*(r+d+1)^4

theorem compilationCost_le (a : Fin d) :
    compilationCost (ι:=ι) a≤setupCost (Fintype.card ι) d := by
  have hp : (pencilCircuit (ι:=ι) a).cost≤
      (dimension a+1)*matrixSize (Fin d)^2*(2*blockBound (Fintype.card ι) d+8) := by
    calc
      _ ≤ ∑ _p : QueryIndex a×Fin (matrixSize (Fin d))×Fin (matrixSize (Fin d)),
          (2*blockBound (Fintype.card ι) d+8) := by
        apply Finset.sum_le_sum
        intro p _
        exact Nat.add_le_add_right (entry_cost a p.1 p.2.1 p.2.2) 1
      _ = _ := by simp [QueryIndex,pow_two,Nat.mul_assoc]
  have ho : (objectiveCircuit (ι:=ι) a).cost≤(dimension a+1)*(objectiveBound d+1) := by
    calc
      _ ≤ ∑ _k : QueryIndex a,(objectiveBound d+1) := by
        apply Finset.sum_le_sum
        intro k _
        exact Nat.add_le_add_right (objectiveExpr_cost a k) 1
      _ = _ := by simp [QueryIndex]
  have hdim : dimension a≤4*d^2 := by rw [KSFullManuscriptProgramSize.variableCount]; omega
  have hp' : (pencilCircuit (ι:=ι) a).cost≤
      (4*d^2+1)*(10*d)^2*(2*blockBound (Fintype.card ι) d+8) :=
    hp.trans (by rw [KSFullManuscriptProgramSize.pencilOrder]; gcongr)
  have ho' : (objectiveCircuit (ι:=ι) a).cost≤(4*d^2+1)*(objectiveBound d+1) :=
    ho.trans (by gcongr)
  unfold compilationCost setupCost
  omega

def setup (a : Fin d) (H : Matrix (Fin d) (Fin d) ℂ)
    (A : ι→Matrix (Fin d) (Fin d) ℂ) (C : Matrix ι ι ℝ) (θ : ℝ) : Counted (Query a) :=
  let v := input H A C θ
  ⟨⟨data a v,WithLp.toLp 2 (fun k => (objectiveExpr a (some k)).eval v),
    (objectiveExpr a none).eval v⟩,compilationCost (ι:=ι) a⟩

theorem setup_entry_execution (a : Fin d) (H : Matrix (Fin d) (Fin d) ℂ)
    (A : ι→Matrix (Fin d) (Fin d) ℂ) (C : Matrix ι ι ℝ) (θ : ℝ)
    (hd : 0<d) (k : QueryIndex a) (i j) :
    Expr.Executes (input H A C θ) (entry a k i j)
      (matrix a (input H A C θ) k i j) (entry (ι:=ι) a k i j).cost :=
  Expr.executes_of_valid _ _ (entry_valid a _ hd k i j)

theorem setup_eq (a : Fin d) (H : Matrix (Fin d) (Fin d) ℂ)
    (A : ι→Matrix (Fin d) (Fin d) ℂ) (hA : ∀i,(A i).IsHermitian)
    (C : Matrix ι ι ℝ) (hC : C.PosSemidef) (θ : ℝ) (hd : 0<d) :
    (setup a H A C θ).value=(OwnerSDPSetup.setup a H A hA C hC hd θ).value := by
  have hc : WithLp.toLp 2 (fun k => (objectiveExpr a (some k)).eval (input H A C θ))=
      KSFullManuscriptAffineObjective.coefficient a H θ := by
    ext k
    exact objectiveExpr_eval a H A C θ hd (some k)
  simp only [setup,OwnerSDPSetup.setup,data_eq a H A hA C hC θ hd,hc,
    objectiveExpr_eval a H A C θ hd none]

def report (P : KSPolynomialConvexSolver.PolynomialSolver)
    (H : Matrix (Fin d) (Fin d) ℂ) (A : ι→Matrix (Fin d) (Fin d) ℂ)
    (C : Matrix ι ι ℝ) (θ : ℝ) (hd : 0<d) (ν : ℝ) : Counted ℝ :=
  let q := setup ⟨0,hd⟩ H A C θ
  let r := P.run q.value.data q.value.coefficient q.value.offset ν
  ⟨r.value,q.cost+r.cost⟩

theorem report_value (P : KSPolynomialConvexSolver.PolynomialSolver)
    (H : Matrix (Fin d) (Fin d) ℂ) (A : ι→Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀i,(A i).IsHermitian) (C : Matrix ι ι ℝ) (hC : C.PosSemidef)
    (θ : ℝ) (hd : 0<d) (ν : ℝ) :
    (report P H A C θ hd ν).value=
      KSConvexValueOracle.ownerReport P.solver ⟨0,hd⟩ H A hA C hC hd θ ν := by
  simp only [report,setup_eq _ H A hA C hC θ hd]
  rfl

theorem report_cost (P : KSPolynomialConvexSolver.PolynomialSolver)
    (H : Matrix (Fin d) (Fin d) ℂ) (A : ι→Matrix (Fin d) (Fin d) ℂ)
    (C : Matrix ι ι ℝ) (θ : ℝ) (hd : 0<d) (ν : ℝ) (hν : 0<ν) {S V : ℕ}
    (hS : KSPolynomialConvexSolver.dataSize (dimension (⟨0,hd⟩:Fin d))
      (matrixSize (Fin d))≤S) (hV : ν⁻¹≤(V:ℝ)) :
    (report P H A C θ hd ν).cost≤
      setupCost (Fintype.card ι) d+P.coefficient*(S+V+1)^P.degree := by
  exact Nat.add_le_add (compilationCost_le ⟨0,hd⟩)
    (P.run_cost_le _ _ _ hν hS hV)

def oracle (P : KSPolynomialConvexSolver.PolynomialSolver) : MSConvexOwnerValue.Oracle where
  report H A C θ hd ν := (report P H A C θ hd ν).value
  accuracy := by
    intro ι _ _ d _ H _ A hA C hC θ ν hθ hν hd
    rw [report_value P H A hA C hC θ hd ν]
    exact KSConvexValueOracle.ownerReport_accuracy P.solver ⟨0,hd⟩ H A hA C hC hd hθ hν

end MatrixSpencer.RealRAM.MSRawOwnerReport
