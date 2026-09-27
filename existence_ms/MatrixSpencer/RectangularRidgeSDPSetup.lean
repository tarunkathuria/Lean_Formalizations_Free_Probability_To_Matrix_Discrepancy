import MatrixSpencer.RectangularRidgeSDPObjective
import MatrixSpencer.RealRAMOwnerSDPPolynomialCost

/-! Materialization of every literal affine-SDP scalar coefficient. The
stored arrays are exactly those passed to the finite-LMI solver. The count
sums the actual primitive expression executions and one store per entry. -/
open scoped BigOperators Matrix
noncomputable section
namespace MatrixSpencer.RealRAM.RectangularRidgeSDPEntries
open OwnerSDPBlocks
open DyadicSDPCoordinates DyadicSDPAffineData
open JacobiIteration (Counted)
variable {d : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

abbrev PencilAddress (m : ℕ) (a : Fin d) :=
  QueryIndex m a × Constraint m × Fin (matrixSize (Fin d)) × Fin (matrixSize (Fin d))

def pencilCircuit (m : ℕ) (a : Fin d) :
    Circuit (Reg (ι:=ι) (d:=d)) (PencilAddress m a) :=
  ⟨fun p=>pencilExpr m a p.1 p.2.1 p.2.2.1 p.2.2.2⟩

def objectiveCircuit (m : ℕ) (hm : 1≤m) (a : Fin d) :
    Circuit (Reg (ι:=ι) (d:=d)) (QueryIndex m a) := ⟨objectiveExpr m hm a⟩

/-- The entries are evaluated in finite index order and stored once. -/
def materialize (m : ℕ) (hm : 1≤m) (a : Fin d) (v : Reg (ι:=ι) (d:=d)→ℝ) :
    Counted ((PencilAddress m a → ℝ) × (QueryIndex m a → ℝ)) :=
  ⟨((pencilCircuit m a).eval v,(objectiveCircuit m hm a).eval v),
    (pencilCircuit (ι:=ι) m a).cost+(objectiveCircuit (ι:=ι) m hm a).cost⟩

/-- An explicit factored polynomial; it contains no real magnitude parameter. -/
def setupCost (r m d : ℕ) :=
  ((m+3)*d^2+1)*(2*m+1)*(4*d)^2*(OwnerSDPSetup.blockBound r d+3)+
    ((m+3)*d^2+1)*(objectiveBound m d+1)

theorem materialize_cost_le (m : ℕ) (hm : 1≤m) (a : Fin d) (v : Reg (ι:=ι) (d:=d)→ℝ) :
    (materialize m hm a v).cost≤setupCost (Fintype.card ι) m d := by
  have hp : (pencilCircuit (ι:=ι) m a).cost≤
      (dimension m a+1)*(2*m+1)*(4*d)^2*(OwnerSDPSetup.blockBound (Fintype.card ι) d+3) := by
    calc _≤∑_p:PencilAddress m a, (OwnerSDPSetup.blockBound (Fintype.card ι) d+3) := by
          unfold Circuit.cost
          apply Finset.sum_le_sum
          intro p _
          exact Nat.add_le_add_right (pencilExpr_cost m a p.1 p.2.1 p.2.2.1 p.2.2.2) 1
      _=_ := by simp [PencilAddress, QueryIndex, pow_two,Nat.mul_assoc];ring
  have ho : (objectiveCircuit (ι:=ι) m hm a).cost≤(dimension m a+1)*(objectiveBound m d+1) := by
    calc _≤∑_k:QueryIndex m a,(objectiveBound m d+1) := by
          unfold Circuit.cost
          apply Finset.sum_le_sum
          intro k _
          exact Nat.add_le_add_right (objectiveExpr_cost m hm a k) 1
      _=_ := by simp [QueryIndex]
  have hdim : dimension m a≤(m+3)*d^2 := by rw [dimension_eq];simp only [Fintype.card_fin];omega
  apply Nat.add_le_add (hp.trans ?_) (ho.trans ?_)
  · gcongr
  · gcongr

/-- Every stored matrix coefficient is computed by the displayed primitives. -/
theorem materialize_pencil_execution (m : ℕ) (_hm : 1≤m) (a : Fin d)
    (H : Matrix (Fin d) (Fin d) ℂ) (A : ι→Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀i,(A i).IsHermitian) (C : selfAdjoint (Matrix ι ι ℝ)) (θ : ℝ)
    (k : QueryIndex m a) (b : Constraint m) (i j : Fin (matrixSize (Fin d))) :
    Expr.Executes (input H A C θ) (pencilExpr m a k b i j)
      ((match k with
        | none => (RectangularRidgeSymmetricQueries.data m a A hA C b).constant
        | some k => (RectangularRidgeSymmetricQueries.data m a A hA C b).coefficient k) i j)
      (pencilExpr (ι:=ι) m a k b i j).cost := by
  have h:=Expr.executes_of_valid (input H A C θ) (pencilExpr m a k b i j)
    (pencilExpr_valid m a _ k b i j)
  rw [pencilExpr_eval] at h
  exact h

theorem materialize_objective_execution (m : ℕ) (hm : 1≤m) (a : Fin d)
    (H : Matrix (Fin d) (Fin d) ℂ) (A : ι→Matrix (Fin d) (Fin d) ℂ)
    (C : Matrix ι ι ℝ) (θ : ℝ) (k : QueryIndex m a) :
    Expr.Executes (input H A C θ) (objectiveExpr m hm a k)
      (match k with
        | none => RectangularRidgeAffineSDP.offset m hm a H θ (1/d)
        | some k => RectangularRidgeAffineSDP.coefficient m hm a H θ (1/d) k)
      (objectiveExpr (ι:=ι) m hm a k).cost := by
  have h:=Expr.executes_of_valid (input H A C θ) (objectiveExpr m hm a k)
    (objectiveExpr_valid m hm a _ k)
  rwa [objectiveExpr_eval] at h

theorem materialize_values (m : ℕ) (hm : 1≤m) (a : Fin d)
    (H : Matrix (Fin d) (Fin d) ℂ) (A : ι→Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀i,(A i).IsHermitian) (C : selfAdjoint (Matrix ι ι ℝ)) (θ : ℝ) :
    (∀ k b i j, (materialize m hm a (input H A C θ)).value.1 (k,b,i,j)=
      (match k with
        | none => (RectangularRidgeSymmetricQueries.data m a A hA C b).constant
        | some k => (RectangularRidgeSymmetricQueries.data m a A hA C b).coefficient k) i j) ∧
    (∀ k,(materialize m hm a (input H A C θ)).value.2 k=match k with
        | none => RectangularRidgeAffineSDP.offset m hm a H θ (1/d)
        | some k => RectangularRidgeAffineSDP.coefficient m hm a H θ (1/d) k) :=
  ⟨fun k b i j=>pencilExpr_eval m a H A C θ k b i j,
    fun k=>objectiveExpr_eval m hm a H A C θ k⟩

theorem setupCost_mono {r s m n d e : ℕ} (hr : r≤s) (hm : m≤n) (hd : d≤e) :
    setupCost r m d≤setupCost s n e := by
  unfold setupCost OwnerSDPSetup.blockBound objectiveBound sourceBound productBound
  gcongr

theorem setupCost_polynomial (r m d : ℕ) : setupCost r m d≤1000000*(r+m+d+1)^11 := by
  let t:=r+m+d+1
  have ht : 1≤t := by dsimp [t];omega
  have h0 : 1≤t^11 := one_le_pow₀ ht
  have h1 : t≤t^11 := by simpa using Nat.pow_le_pow_right ht (show 1≤11 by omega)
  have h2 : t^2≤t^11 := Nat.pow_le_pow_right ht (by omega)
  have h3 : t^3≤t^11 := Nat.pow_le_pow_right ht (by omega)
  have h4 : t^4≤t^11 := Nat.pow_le_pow_right ht (by omega)
  have h5 : t^5≤t^11 := Nat.pow_le_pow_right ht (by omega)
  have h6 : t^6≤t^11 := Nat.pow_le_pow_right ht (by omega)
  have h7 : t^7≤t^11 := Nat.pow_le_pow_right ht (by omega)
  have h8 : t^8≤t^11 := Nat.pow_le_pow_right ht (by omega)
  have h9 : t^9≤t^11 := Nat.pow_le_pow_right ht (by omega)
  have h10 : t^10≤t^11 := Nat.pow_le_pow_right ht (by omega)
  apply (setupCost_mono (show r≤t by dsimp [t];omega)
    (show m≤t by dsimp [t];omega) (show d≤t by dsimp [t];omega)).trans
  change setupCost t t t≤1000000*t^11
  unfold setupCost OwnerSDPSetup.blockBound objectiveBound sourceBound productBound
  ring_nf
  omega

/-- Decode the evaluated real coefficient arrays into the solver input. The
symmetry fields follow from entry equality, and perform no numerical test. -/
def materializedData (m : ℕ) (hm : 1≤m) (a : Fin d)
    (H : Matrix (Fin d) (Fin d) ℂ) (A : ι→Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀i,(A i).IsHermitian) (C : selfAdjoint (Matrix ι ι ℝ)) (θ : ℝ)
    (b : Constraint m) : KSFullManuscriptAffinePSD.Data (dimension m a) (matrixSize (Fin d)) where
  constant i j := (materialize m hm a (input H A C θ)).value.1 (none,b,i,j)
  coefficient k i j := (materialize m hm a (input H A C θ)).value.1 (some k,b,i,j)
  constant_symmetric := by
    have he : (fun i j=>(materialize m hm a (input H A C θ)).value.1 (none,b,i,j)) =
        (RectangularRidgeSymmetricQueries.data m a A hA C b).constant := by
      funext i j;exact (materialize_values m hm a H A hA C θ).1 none b i j
    rw [he]
    exact (RectangularRidgeSymmetricQueries.data m a A hA C b).constant_symmetric
  coefficient_symmetric k := by
    have he : (fun i j=>(materialize m hm a (input H A C θ)).value.1 (some k,b,i,j)) =
        (RectangularRidgeSymmetricQueries.data m a A hA C b).coefficient k := by
      funext i j;exact (materialize_values m hm a H A hA C θ).1 (some k) b i j
    rw [he]
    exact (RectangularRidgeSymmetricQueries.data m a A hA C b).coefficient_symmetric k

theorem materializedData_eq (m : ℕ) (hm : 1≤m) (a : Fin d)
    (H : Matrix (Fin d) (Fin d) ℂ) (A : ι→Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀i,(A i).IsHermitian) (C : selfAdjoint (Matrix ι ι ℝ)) (θ : ℝ) :
    materializedData m hm a H A hA C θ=RectangularRidgeSymmetricQueries.data m a A hA C := by
  funext b
  have hc : (materializedData m hm a H A hA C θ b).constant =
      (RectangularRidgeSymmetricQueries.data m a A hA C b).constant := by
    funext i j;exact (materialize_values m hm a H A hA C θ).1 none b i j
  have hl : (materializedData m hm a H A hA C θ b).coefficient =
      (RectangularRidgeSymmetricQueries.data m a A hA C b).coefficient := by
    funext k i j;exact (materialize_values m hm a H A hA C θ).1 (some k) b i j
  generalize materializedData m hm a H A hA C θ b = x at hc hl ⊢
  generalize RectangularRidgeSymmetricQueries.data m a A hA C b = y at hc hl ⊢
  cases x
  cases y
  cases hc
  cases hl
  rfl

def materializedCoefficient (m : ℕ) (hm : 1≤m) (a : Fin d)
    (H : Matrix (Fin d) (Fin d) ℂ) (A : ι→Matrix (Fin d) (Fin d) ℂ)
    (C : Matrix ι ι ℝ) (θ : ℝ) : Space m a :=
  WithLp.toLp 2 (fun k=>(materialize m hm a (input H A C θ)).value.2 (some k))

theorem materializedCoefficient_eq (m : ℕ) (hm : 1≤m) (a : Fin d)
    (H : Matrix (Fin d) (Fin d) ℂ) (A : ι→Matrix (Fin d) (Fin d) ℂ)
    (C : Matrix ι ι ℝ) (θ : ℝ) :
    materializedCoefficient m hm a H A C θ=RectangularRidgeAffineSDP.coefficient m hm a H θ (1/d) := by
  ext k
  exact objectiveExpr_eval m hm a H A C θ (some k)

/-- The solver is called on the computed arrays, and their actual scalar
execution and store cost is charged alongside convex optimization. -/
def report (P : RectangularRidgeConvexValue.PolynomialSolver)
    (m : ℕ) (hm : 1≤m) (a : Fin d) (H : Matrix (Fin d) (Fin d) ℂ)
    (A : ι→Matrix (Fin d) (Fin d) ℂ) (hA : ∀i,(A i).IsHermitian)
    (C : selfAdjoint (Matrix ι ι ℝ)) (θ ν : ℝ) : Counted ℝ :=
  let arrays:=materialize m hm a (input H A C θ)
  let ans:=P.run (materializedData m hm a H A hA C θ)
    (materializedCoefficient m hm a H A C θ) (arrays.value.2 none) ν
  ⟨ans.value,arrays.cost+ans.cost⟩

theorem report_value (P : RectangularRidgeConvexValue.PolynomialSolver)
    (m : ℕ) (hm : 1≤m) (a : Fin d) (H : Matrix (Fin d) (Fin d) ℂ)
    (A : ι→Matrix (Fin d) (Fin d) ℂ) (hA : ∀i,(A i).IsHermitian)
    (C : selfAdjoint (Matrix ι ι ℝ)) (θ ν : ℝ) :
    (report P m hm a H A hA C θ ν).value=
      RectangularRidgeSymmetricQueries.report P.solver m hm a H A hA C θ (1/d) ν := by
  simp only [report,materializedData_eq,materializedCoefficient_eq]
  rw [(materialize_values m hm a H A hA C θ).2 none]
  rfl

theorem report_cost_le (P : RectangularRidgeConvexValue.PolynomialSolver)
    (m : ℕ) (hm : 1≤m) (a : Fin d) (H : Matrix (Fin d) (Fin d) ℂ)
    (A : ι→Matrix (Fin d) (Fin d) ℂ) (hA : ∀i,(A i).IsHermitian)
    (C : selfAdjoint (Matrix ι ι ℝ)) (θ : ℝ) {ν : ℝ} (hν : 0<ν)
    {S V : ℕ} (hS : RectangularRidgeConvexValue.dataSize (Fintype.card (Constraint m))
      (dimension m a) (matrixSize (Fin d))≤S) (hV : ν⁻¹≤(V:ℝ)) :
    (report P m hm a H A hA C θ ν).cost≤
      setupCost (Fintype.card ι) m d+P.coefficient*(S+V+1)^P.degree := by
  apply Nat.add_le_add (materialize_cost_le m hm a _)
  exact P.run_cost_le _ _ _ hν hS hV

/-- A uniform polynomial bound at the exact comparison-chosen depth. -/
theorem primitive_materialize_cost_le {N : ℕ} (hN : 1≤N) (a : Fin d)
    (v : Reg (ι:=ι) (d:=d)→ℝ) :
    (materialize (RectangularRidgeTuning.depth N d hN)
      (RectangularRidgeTuning.depth_positive N d hN) a v).cost≤
      1000000*(Fintype.card ι+2*d+2)^11 := by
  apply (materialize_cost_le _ _ _ _).trans
  apply (setupCost_polynomial _ _ _).trans
  have hm:=RectangularRidgeTuning.depth_le N d hN
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_left
  omega

theorem primitive_report_cost_le (P : RectangularRidgeConvexValue.PolynomialSolver)
    {N : ℕ} (hN : 1≤N) (a : Fin d) (H : Matrix (Fin d) (Fin d) ℂ)
    (A : ι→Matrix (Fin d) (Fin d) ℂ) (hA : ∀i,(A i).IsHermitian)
    (C : selfAdjoint (Matrix ι ι ℝ)) (θ : ℝ) {ν : ℝ} (hν : 0<ν)
    {V : ℕ} (hV : ν⁻¹≤(V:ℝ)) :
    (report P (RectangularRidgeTuning.depth N d hN)
      (RectangularRidgeTuning.depth_positive N d hN) a H A hA C θ ν).cost≤
      1000000*(Fintype.card ι+2*d+2)^11+
        P.coefficient*(16*(2*d+3)*(d+4)*d^4+(d+4)*d^2+2+V+1)^P.degree := by
  apply Nat.add_le_add (primitive_materialize_cost_le hN a _)
  exact P.run_cost_le _ _ _ hν (RectangularRidgeConvexValue.primitive_dataSize_le hN a) hV

end MatrixSpencer.RealRAM.RectangularRidgeSDPEntries
