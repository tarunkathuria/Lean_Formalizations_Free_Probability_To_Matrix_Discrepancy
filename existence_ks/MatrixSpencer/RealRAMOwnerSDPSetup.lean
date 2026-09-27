import MatrixSpencer.RealRAMPreparedSDPChart
import MatrixSpencer.RealRAMOwnerSDPBlocks

/-! Counted preparation of the literal direct owner SDP, followed only by the
explicitly permitted polynomial convex solver. Every real array entry has a
safe primitive execution. Polynomial finite address-table work is included
in the preparation count. -/
open scoped BigOperators Matrix
noncomputable section
namespace MatrixSpencer.RealRAM.OwnerSDPSetup
open OwnerSDPBlocks
open JacobiIteration (Counted)
open KSFullManuscriptAffineData KSFullManuscriptSDPBlockPencil
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] [FiniteEnumeration ι]

abbrev Reg := Registers ι d

def baseDensity (i j : Fin d) : ComplexExpr (Reg (ι:=ι) (d:=d)) :=
  .real (if i=j then .div (.constant 1) (.constant d) else .constant 0)

@[simp] theorem baseDensity_eval (v : Reg (ι:=ι) (d:=d)→ℝ) (hd : 0<d) (i j : Fin d) :
    (baseDensity i j).eval v = (KSFullManuscriptCenterData.densityCenter hd : Matrix (Fin d) (Fin d) ℂ) i j := by
  by_cases h:i=j <;> simp [baseDensity,h,Expr.eval,KSFullManuscriptCenterData.densityCenter,
    KSFullManuscriptStrictFeasible.density,Matrix.one_apply]

theorem baseDensity_valid (v : Reg (ι:=ι) (d:=d)→ℝ) (hd : 0<d) (i j : Fin d) :
    (baseDensity i j).Valid v := by
  apply ComplexExpr.valid_real
  split
  · exact ⟨trivial,trivial,by simp [Expr.eval];exact_mod_cast hd.ne'⟩
  · trivial

theorem baseDensity_cost (i j : Fin d) : (baseDensity (ι:=ι) i j).cost≤4 := by
  unfold baseDensity;split <;> norm_num [ComplexExpr.cost_real,Expr.cost]

def identity (i j : Fin d) : ComplexExpr (Reg (ι:=ι) (d:=d)) := .real (.constant (if i=j then 1 else 0))
@[simp] theorem identity_eval (v : Reg (ι:=ι) (d:=d)→ℝ) (i j : Fin d) :
    (identity i j).eval v = (1 : Matrix (Fin d) (Fin d) ℂ) i j := by
  by_cases h:i=j <;> simp [identity,h,Expr.eval,Matrix.one_apply]

def blockExpr (S Y Z : Fin d→Fin d→ComplexExpr (Reg (ι:=ι) (d:=d))) (full : Bool) :=
  blocks Y (fun _ _=>.zero) (fun _ _=>.zero) (blocks
    (blocks S Z (fun i j=>.conj (Z j i)) (source S)) (fun _ _=>.zero) (fun _ _=>.zero)
    (blocks S Y Y (if full then identity else fun _ _=>.zero)))

theorem blockExpr_eval (H : Matrix (Fin d) (Fin d) ℂ) (A : ι→Matrix (Fin d) (Fin d) ℂ) (C : Matrix ι ι ℝ) (θ : ℝ) (S Y Z : Fin d→Fin d→ComplexExpr (Reg (ι:=ι) (d:=d)))
    (full : Bool) :
    Matrix.of (fun i j=>(blockExpr S Y Z full i j).eval (input H A C θ)) =
      if full then OwnerSDPProgramSize.block A C 0
        (Matrix.of (fun i j=>(S i j).eval (input H A C θ)))
        (Matrix.of (fun i j=>(Y i j).eval (input H A C θ)))
        (Matrix.of (fun i j=>(Z i j).eval (input H A C θ)))
      else OwnerSDPProgramSize.delta A C
        (Matrix.of (fun i j=>(S i j).eval (input H A C θ)))
        (Matrix.of (fun i j=>(Y i j).eval (input H A C θ)))
        (Matrix.of (fun i j=>(Z i j).eval (input H A C θ))) := by
  funext i j
  rcases i with i | ((i | i) | (i | i)) <;>
    rcases j with j | ((j | j) | (j | j)) <;>
    cases full <;>
    simp [blockExpr,blocks,OwnerSDPProgramSize.block,OwnerSDPProgramSize.delta,Matrix.conjTranspose_apply]

theorem blockExpr_valid (S Y Z : Fin d→Fin d→ComplexExpr (Reg (ι:=ι) (d:=d)))
    (v : Reg (ι:=ι) (d:=d)→ℝ) (hS : ∀i j,(S i j).Valid v) (hY : ∀i j,(Y i j).Valid v)
    (hZ : ∀i j,(Z i j).Valid v) (full : Bool) (i j) :
    (blockExpr S Y Z full i j).Valid v := by
  apply blocks_valid _ _ _ _ _ hY (fun _ _=>ComplexExpr.valid_zero _) (fun _ _=>ComplexExpr.valid_zero _)
  apply blocks_valid _ _ _ _ _
  · exact blocks_valid _ _ _ _ _ hS hZ (fun i j=>ComplexExpr.valid_conj (hZ j i)) (source_valid _ _ hS)
  · exact fun _ _=>ComplexExpr.valid_zero _
  · exact fun _ _=>ComplexExpr.valid_zero _
  · apply blocks_valid _ _ _ _ _ hS hY hY
    intro i j
    cases full <;> exact ⟨trivial,trivial⟩

def blockBound (r d : ℕ) := sourceBound r d (4*d+8)+4*d+12

theorem blockExpr_cost (S Y Z : Fin d→Fin d→ComplexExpr (Reg (ι:=ι) (d:=d)))
    (hS : ∀i j,(S i j).cost≤4*d+8) (hY : ∀i j,(Y i j).cost≤4)
    (hZ : ∀i j,(Z i j).cost≤2) (full : Bool) (i j) :
    (blockExpr S Y Z full i j).cost≤blockBound (Fintype.card ι) d := by
  have hs : ∀i j,(S i j).cost≤blockBound (Fintype.card ι) d := fun i j=>(hS i j).trans (by unfold blockBound;omega)
  have hy : ∀i j,(Y i j).cost≤blockBound (Fintype.card ι) d := fun i j=>(hY i j).trans (by unfold blockBound;omega)
  have hz : ∀i j,(Z i j).cost≤blockBound (Fintype.card ι) d := fun i j=>(hZ i j).trans (by unfold blockBound;omega)
  have hzero : 2≤blockBound (Fintype.card ι) d := by unfold blockBound;omega
  unfold blockExpr
  apply blocks_cost Y (fun _ _=>.zero) (fun _ _=>.zero) _ _ hy (fun _ _=>hzero) (fun _ _=>hzero)
  apply blocks_cost _ _ _ _ _
  · apply blocks_cost _ _ _ _ _ hs hz
    · intro i j;rw [ComplexExpr.cost_conj];have h:=hZ j i;unfold blockBound;omega
    · exact fun i j=>(source_cost S _ hS i j).trans (by unfold blockBound;omega)
  · intro _ _;simp [ComplexExpr.cost_zero,blockBound]
  · intro _ _;simp [ComplexExpr.cost_zero,blockBound]
  · apply blocks_cost _ _ _ _ _ hs hy hy
    intro i j
    cases full <;> simp [identity,ComplexExpr.cost_zero,ComplexExpr.cost_real,Expr.cost,blockBound]

def densityExpr (a : Fin d) : Option (Fin (dimension a))→Fin d→Fin d→ComplexExpr (Reg (ι:=ι) (d:=d))
  | none=>baseDensity
  | some k=>SDPChart.density a k

def regularizerExpr (a : Fin d) : Option (Fin (dimension a))→Fin d→Fin d→ComplexExpr (Reg (ι:=ι) (d:=d))
  | none=>fun _ _=>.zero
  | some k=>SDPChart.regularizer a k

def fidelityExpr (a : Fin d) : Option (Fin (dimension a))→Fin d→Fin d→ComplexExpr (Reg (ι:=ι) (d:=d))
  | none=>fun _ _=>.zero
  | some k=>SDPChart.fidelity a k

def pencilExpr (a : Fin d) (k : Option (Fin (dimension a)))
    (i j : Fin (matrixSize (Fin d))) : Expr (Reg (ι:=ι) (d:=d)) :=
  realify (blockExpr (densityExpr a k) (regularizerExpr a k) (fidelityExpr a k) k.isNone)
    (SDPIndexTables.rowAddress i) (SDPIndexTables.rowAddress j)

@[simp] theorem pencilExpr_eval (a : Fin d) (H : Matrix (Fin d) (Fin d) ℂ) (A : ι→Matrix (Fin d) (Fin d) ℂ) (C : Matrix ι ι ℝ) (θ : ℝ) (hd : 0<d)
    (k : Option (Fin (dimension a))) (i j : Fin (matrixSize (Fin d))) :
    (pencilExpr a k i j).eval (input H A C θ) =
      (match k with
       | none=>OwnerSDPProgramSize.constant a A C (KSFullManuscriptCenterData.densityCenter hd) 0 0
       | some k=>OwnerSDPProgramSize.coefficient a A C k) i j := by
  unfold pencilExpr
  simp only [SDPIndexTables.rowAddress_eq]
  rw [realify_eval,blockExpr_eval]
  cases k <;> simp only [densityExpr,regularizerExpr,fidelityExpr,Option.isNone,if_true,if_false,
    Bool.false_eq_true,ComplexExpr.eval_zero,baseDensity_eval _ hd,SDPChart.density_eval,SDPChart.regularizer_eval,SDPChart.fidelity_eval]
  all_goals rfl

theorem pencilExpr_valid (a : Fin d) (v : Reg (ι:=ι) (d:=d)→ℝ) (hd : 0<d)
    (k : Option (Fin (dimension a))) (i j) : (pencilExpr a k i j).Valid v := by
  apply realify_valid
  apply blockExpr_valid
  · intro i j;cases k
    · exact baseDensity_valid _ hd _ _
    · exact SDPChart.density_valid _ _ _ _ _
  · intro i j;cases k
    · exact ComplexExpr.valid_zero _
    · exact SDPChart.regularizer_valid _ _ _ _ _
  · intro i j;cases k
    · exact ComplexExpr.valid_zero _
    · exact SDPChart.fidelity_valid _ _ _ _ _

theorem pencilExpr_cost (a : Fin d) (k : Option (Fin (dimension a))) (i j) :
    (pencilExpr (ι:=ι) a k i j).cost≤blockBound (Fintype.card ι) d+2 := by
  apply realify_cost
  apply blockExpr_cost
  · intro i j;cases k
    · exact (baseDensity_cost _ _).trans (by omega)
    · exact SDPChart.density_cost _ _ _ _
  · intro i j;cases k
    · exact (by norm_num [regularizerExpr,ComplexExpr.cost_zero])
    · exact SDPChart.regularizer_cost _ _ _ _
  · intro i j;cases k
    · exact le_rfl
    · exact le_rfl

def traceExpr (S : Fin d→Fin d→ComplexExpr (Reg (ι:=ι) (d:=d))) : Expr (Reg (ι:=ι) (d:=d)) :=
  finiteSumExpr (fun i=>(S i i).re)

@[simp] theorem traceExpr_eval (S : Fin d→Fin d→ComplexExpr (Reg (ι:=ι) (d:=d))) (v : Reg (ι:=ι) (d:=d)→ℝ) :
    (traceExpr S).eval v = realTrace (Matrix.of (fun i j=>(S i j).eval v)) := by
  simp [traceExpr,finiteSumExpr_eval,realTrace,Matrix.trace,ComplexExpr.eval]

theorem traceExpr_valid (S : Fin d→Fin d→ComplexExpr (Reg (ι:=ι) (d:=d))) (v : Reg (ι:=ι) (d:=d)→ℝ)
    (hS : ∀i j,(S i j).Valid v) : (traceExpr S).Valid v :=
  finiteSumExpr_valid _ _ (fun i=>(hS i i).1)

theorem traceExpr_cost (S : Fin d→Fin d→ComplexExpr (Reg (ι:=ι) (d:=d))) (b : ℕ)
    (hS : ∀i j,(S i j).cost≤b) : (traceExpr S).cost≤d*(b+1)+1 := by
  have h := finiteSumExpr_cost_le (fun i=>(S i i).re) b (fun i=>by
    have h:=hS i i
    dsimp [ComplexExpr.cost] at *
    omega)
  simpa [traceExpr] using h

def objectiveExpr (a : Fin d) (k : Option (Fin (dimension a))) : Expr (Reg (ι:=ι) (d:=d)) :=
  .add (.add (traceExpr (ComplexExpr.matrixMul center (densityExpr a k)))
    (.mul (.constant 2) (traceExpr (fidelityExpr a k))))
    (.mul (.mul (.constant 2) theta) (traceExpr (regularizerExpr a k)))

@[simp] theorem objectiveExpr_eval (a : Fin d)
    (H : Matrix (Fin d) (Fin d) ℂ) (A : ι→Matrix (Fin d) (Fin d) ℂ)
    (C : Matrix ι ι ℝ) (θ : ℝ) (hd : 0<d) (k : Option (Fin (dimension a))) :
    (objectiveExpr a k).eval (input H A C θ) = match k with
    | none=>KSFullManuscriptAffineObjective.offset H θ (KSFullManuscriptCenterData.densityCenter hd) 0
    | some k=>KSFullManuscriptAffineObjective.coefficient a H θ k := by
  cases k <;> simp [objectiveExpr,Expr.eval,traceExpr_eval,ComplexExpr.matrixMul_eval,densityExpr,
    regularizerExpr,fidelityExpr,baseDensity_eval _ hd,KSFullManuscriptAffineObjective.offset,
    KSFullManuscriptSDPIdentity.value,KSFullManuscriptAffineObjective.coefficient,
    KSFullManuscriptAffineObjective.valueLinear]
  · change realTrace (H * (KSFullManuscriptCenterData.densityCenter hd : Matrix (Fin d) (Fin d) ℂ)) +
      2*realTrace (0 : Matrix (Fin d) (Fin d) ℂ)+2*θ*realTrace (0 : Matrix (Fin d) (Fin d) ℂ)=_
    simp
  · rfl

theorem objectiveExpr_valid (a : Fin d) (v : Reg (ι:=ι) (d:=d)→ℝ) (hd : 0<d)
    (k : Option (Fin (dimension a))) : (objectiveExpr a k).Valid v := by
  refine ⟨⟨traceExpr_valid _ _ ?_,⟨trivial,traceExpr_valid _ _ ?_⟩⟩,⟨⟨trivial,trivial⟩,traceExpr_valid _ _ ?_⟩⟩
  · apply ComplexExpr.matrixMul_valid center (densityExpr a k) v (fun _ _=>⟨trivial,trivial⟩)
    intro i j;cases k
    · exact baseDensity_valid _ hd _ _
    · exact SDPChart.density_valid _ _ _ _ _
  · intro i j;cases k
    · exact ComplexExpr.valid_zero _
    · exact SDPChart.fidelity_valid _ _ _ _ _
  · intro i j;cases k
    · exact ComplexExpr.valid_zero _
    · exact SDPChart.regularizer_valid _ _ _ _ _

def objectiveBound (d : ℕ) := d*(productBound d 2 (4*d+8)+1)+20*d+30

theorem objectiveExpr_cost (a : Fin d) (k : Option (Fin (dimension a))) :
    (objectiveExpr (ι:=ι) a k).cost≤objectiveBound d := by
  have hs : ∀i j,(densityExpr (ι:=ι) a k i j).cost≤4*d+8 := by
    intro i j;cases k
    · exact (baseDensity_cost _ _).trans (by omega)
    · exact SDPChart.density_cost _ _ _ _
  have hz : ∀i j,(fidelityExpr (ι:=ι) a k i j).cost≤2 := by intro i j;cases k <;> exact le_rfl
  have hy : ∀i j,(regularizerExpr (ι:=ι) a k i j).cost≤4 := by
    intro i j;cases k
    · exact (by norm_num [regularizerExpr,ComplexExpr.cost_zero])
    · exact SDPChart.regularizer_cost _ _ _ _
  have hp := traceExpr_cost (ComplexExpr.matrixMul center (densityExpr (ι:=ι) a k))
    (productBound d 2 (4*d+8)) (fun i j=>by
      simpa [productBound] using ComplexExpr.matrixMul_cost center (densityExpr (ι:=ι) a k) 2 (4*d+8)
        (fun _ _=>le_rfl) hs i j)
  have hz' := traceExpr_cost _ _ hz
  have hy' := traceExpr_cost _ _ hy
  simp only [objectiveExpr,Expr.cost,theta]
  dsimp [Expr.cost,objectiveBound] at *
  omega

abbrev QueryIndex (a : Fin d) := Option (Fin (dimension a))

def pencilCircuit (a : Fin d) : Circuit (Reg (ι:=ι) (d:=d)) (QueryIndex a×Fin (matrixSize (Fin d))×Fin (matrixSize (Fin d))) :=
  ⟨fun p=>pencilExpr a p.1 p.2.1 p.2.2⟩
def objectiveCircuit (a : Fin d) : Circuit (Reg (ι:=ι) (d:=d)) (QueryIndex a) := ⟨objectiveExpr a⟩

/-- Explicit scalar arrays, including their store operations, plus polynomial
finite routing/table generation for the fixed chart. -/
def compilationCost (a : Fin d) : ℕ :=
  2*((pencilCircuit (ι:=ι) a).cost+(objectiveCircuit (ι:=ι) a).cost)+
    (SDPIndexTables.chartLookup a).cost+(SDPIndexTables.rowLookup d).cost+100*(Fintype.card ι+d+1)^4

/-- A factored natural polynomial, independent of input real magnitudes. -/
def setupCost (r d : ℕ) :=
  2*((4*d^2+1)*(10*d)^2*(blockBound r d+3)+(4*d^2+1)*(objectiveBound d+1))+10000*(r+d+1)^4

structure Query (a : Fin d) where
  data : KSFullManuscriptAffinePSD.Data (dimension a) (matrixSize (Fin d))
  coefficient : KSFullManuscriptAffinePSD.Space (dimension a)
  offset : ℝ

/-- These builders take the two already materialized address arrays. -/
abbrev ChartAddress (a : Fin d) := KSFullManuscriptSDPCoordinates.Index a → ℕ
abbrev RowAddress (d : ℕ) := Fin (matrixSize (Fin d)) → RealIndex (Fin d)

def densityExprWith (a : Fin d) (address : ChartAddress a) :
    Option (Fin (dimension a))→Fin d→Fin d→ComplexExpr (Reg (ι:=ι) (d:=d))
  | none=>baseDensity
  | some k=>PreparedSDPChart.densityWith a address k

def regularizerExprWith (a : Fin d) (address : ChartAddress a) :
    Option (Fin (dimension a))→Fin d→Fin d→ComplexExpr (Reg (ι:=ι) (d:=d))
  | none=>fun _ _=>.zero
  | some k=>PreparedSDPChart.regularizerWith a address k

def fidelityExprWith (a : Fin d) (address : ChartAddress a) :
    Option (Fin (dimension a))→Fin d→Fin d→ComplexExpr (Reg (ι:=ι) (d:=d))
  | none=>fun _ _=>.zero
  | some k=>PreparedSDPChart.fidelityWith a address k

def pencilExprWith (a : Fin d) (address : ChartAddress a) (rows : RowAddress d)
    (k : Option (Fin (dimension a))) (i j : Fin (matrixSize (Fin d))) :
    Expr (Reg (ι:=ι) (d:=d)) :=
  realify (blockExpr (densityExprWith a address k) (regularizerExprWith a address k)
    (fidelityExprWith a address k) k.isNone) (rows i) (rows j)

def objectiveExprWith (a : Fin d) (address : ChartAddress a)
    (k : Option (Fin (dimension a))) : Expr (Reg (ι:=ι) (d:=d)) :=
  .add (.add (traceExpr (ComplexExpr.matrixMul center (densityExprWith a address k)))
    (.mul (.constant 2) (traceExpr (fidelityExprWith a address k))))
    (.mul (.mul (.constant 2) theta) (traceExpr (regularizerExprWith a address k)))

theorem pencilExprWith_on_tables (a : Fin d) (k : Option (Fin (dimension a))) (i j) :
    pencilExprWith (ι:=ι) a (SDPIndexTables.chartLookup a).value
      (SDPIndexTables.rowLookup d).value k i j=pencilExpr a k i j := by
  cases k <;> rfl

theorem objectiveExprWith_on_table (a : Fin d) (k : Option (Fin (dimension a))) :
    objectiveExprWith (ι:=ι) a (SDPIndexTables.chartLookup a).value k=objectiveExpr a k := by
  cases k <;> rfl

/-- The actual arrays passed to the solver are evaluated scalar circuits.
The canonical mathematical SDP is used only to certify their symmetry. -/
def compiledDataWith (a : Fin d) (address : ChartAddress a) (rows : RowAddress d)
    (ha : address=(SDPIndexTables.chartLookup a).value)
    (hr : rows=(SDPIndexTables.rowLookup d).value) (H : Matrix (Fin d) (Fin d) ℂ)
    (A : ι→Matrix (Fin d) (Fin d) ℂ) (hA : ∀i,(A i).IsHermitian)
    (C : Matrix ι ι ℝ) (hC : C.PosSemidef) (hd : 0<d) (θ : ℝ) :
    KSFullManuscriptAffinePSD.Data (dimension a) (matrixSize (Fin d)) where
  constant i j := (pencilExprWith a address rows none i j).eval (input H A C θ)
  coefficient k i j := (pencilExprWith a address rows (some k) i j).eval (input H A C θ)
  constant_symmetric := by
    have he : (fun i j=>(pencilExprWith a address rows none i j).eval (input H A C θ))=
        (KSConvexValueOracle.ownerData a A hA C hC hd).constant := by
      funext i j
      rw [ha,hr,pencilExprWith_on_tables]
      exact pencilExpr_eval a H A C θ hd none i j
    rw [he]
    exact (KSConvexValueOracle.ownerData a A hA C hC hd).constant_symmetric
  coefficient_symmetric k := by
    have he : (fun i j=>(pencilExprWith a address rows (some k) i j).eval (input H A C θ))=
        (KSConvexValueOracle.ownerData a A hA C hC hd).coefficient k := by
      funext i j
      rw [ha,hr,pencilExprWith_on_tables]
      exact pencilExpr_eval a H A C θ hd (some k) i j
    rw [he]
    exact (KSConvexValueOracle.ownerData a A hA C hC hd).coefficient_symmetric k

def compiledData (a : Fin d) (H : Matrix (Fin d) (Fin d) ℂ)
    (A : ι→Matrix (Fin d) (Fin d) ℂ) (hA : ∀i,(A i).IsHermitian)
    (C : Matrix ι ι ℝ) (hC : C.PosSemidef) (hd : 0<d) (θ : ℝ) :
    KSFullManuscriptAffinePSD.Data (dimension a) (matrixSize (Fin d)) :=
  compiledDataWith a (SDPIndexTables.chartLookup a).value
    (SDPIndexTables.rowLookup d).value rfl rfl H A hA C hC hd θ

theorem compiledData_eq (a : Fin d) (H : Matrix (Fin d) (Fin d) ℂ)
    (A : ι→Matrix (Fin d) (Fin d) ℂ) (hA : ∀i,(A i).IsHermitian)
    (C : Matrix ι ι ℝ) (hC : C.PosSemidef) (hd : 0<d) (θ : ℝ) :
    compiledData a H A hA C hC hd θ=KSConvexValueOracle.ownerData a A hA C hC hd := by
  have hc : (compiledData a H A hA C hC hd θ).constant=
      (KSConvexValueOracle.ownerData a A hA C hC hd).constant := by
    funext i j
    exact pencilExpr_eval a H A C θ hd none i j
  have hk : (compiledData a H A hA C hC hd θ).coefficient=
      (KSConvexValueOracle.ownerData a A hA C hC hd).coefficient := by
    funext k i j
    exact pencilExpr_eval a H A C θ hd (some k) i j
  have hext : ∀ D E : KSFullManuscriptAffinePSD.Data (dimension a) (matrixSize (Fin d)),
      D.constant=E.constant → D.coefficient=E.coefficient → D=E := by
    intro D E hD hE
    cases D
    cases E
    simp only [KSFullManuscriptAffinePSD.Data.mk.injEq]
    exact ⟨hD,hE⟩
  exact hext _ _ hc hk

def setup (a : Fin d) (H : Matrix (Fin d) (Fin d) ℂ)
    (A : ι→Matrix (Fin d) (Fin d) ℂ) (hA : ∀i,(A i).IsHermitian)
    (C : Matrix ι ι ℝ) (hC : C.PosSemidef) (hd : 0<d) (θ : ℝ) : Counted (Query a) :=
  let chart:=SDPIndexTables.chartLookup a
  let rows:=SDPIndexTables.rowLookup d
  ⟨⟨compiledDataWith a chart.value rows.value rfl rfl H A hA C hC hd θ,
      WithLp.toLp 2 (fun k=>(objectiveExprWith a chart.value (some k)).eval (input H A C θ)),
      (objectiveExprWith a chart.value none).eval (input H A C θ)⟩,
    2*((pencilCircuit (ι:=ι) a).cost+(objectiveCircuit (ι:=ι) a).cost)+
      chart.cost+rows.cost+100*(Fintype.card ι+d+1)^4⟩

theorem setup_value (a : Fin d) (H : Matrix (Fin d) (Fin d) ℂ)
    (A : ι→Matrix (Fin d) (Fin d) ℂ) (hA : ∀i,(A i).IsHermitian)
    (C : Matrix ι ι ℝ) (hC : C.PosSemidef) (hd : 0<d) (θ : ℝ) :
    (setup a H A hA C hC hd θ).value=
      ⟨KSConvexValueOracle.ownerData a A hA C hC hd,
       KSFullManuscriptAffineObjective.coefficient a H θ,
       KSFullManuscriptAffineObjective.offset H θ (KSFullManuscriptCenterData.densityCenter hd) 0⟩ := by
  have hc : WithLp.toLp 2 (fun k=>(objectiveExpr a (some k)).eval (input H A C θ))=
      KSFullManuscriptAffineObjective.coefficient a H θ := by
    ext k
    exact objectiveExpr_eval a H A C θ hd (some k)
  change Query.mk (compiledData a H A hA C hC hd θ)
    (WithLp.toLp 2 (fun k=>(objectiveExprWith a (SDPIndexTables.chartLookup a).value (some k)).eval (input H A C θ)))
    ((objectiveExprWith a (SDPIndexTables.chartLookup a).value none).eval (input H A C θ)) = _
  simp only [objectiveExprWith_on_table]
  rw [compiledData_eq,hc,objectiveExpr_eval _ _ _ _ _ hd]

/-- Each stored pencil entry in `setup` is the output of safe real primitives. -/
theorem setup_pencil_execution (a : Fin d) (H : Matrix (Fin d) (Fin d) ℂ)
    (A : ι→Matrix (Fin d) (Fin d) ℂ) (hA : ∀i,(A i).IsHermitian)
    (C : Matrix ι ι ℝ) (hC : C.PosSemidef) (hd : 0<d) (θ : ℝ)
    (k : QueryIndex a) (i j) : Expr.Executes (input H A C θ) (pencilExpr a k i j)
      ((match k with
        | none => (setup a H A hA C hC hd θ).value.data.constant
        | some k => (setup a H A hA C hC hd θ).value.data.coefficient k) i j)
      (pencilExpr (ι:=ι) a k i j).cost := by
  have h:=Expr.executes_of_valid (input H A C θ) (pencilExpr a k i j)
    (pencilExpr_valid a _ hd k i j)
  cases k <;> exact h

/-- The affine objective and offset have the same primitive certification. -/
theorem setup_objective_execution (a : Fin d) (H : Matrix (Fin d) (Fin d) ℂ)
    (A : ι→Matrix (Fin d) (Fin d) ℂ) (hA : ∀i,(A i).IsHermitian)
    (C : Matrix ι ι ℝ) (hC : C.PosSemidef) (hd : 0<d) (θ : ℝ)
    (k : QueryIndex a) : Expr.Executes (input H A C θ) (objectiveExpr a k)
      (match k with
        | none => (setup a H A hA C hC hd θ).value.offset
        | some k => (setup a H A hA C hC hd θ).value.coefficient k)
      (objectiveExpr (ι:=ι) a k).cost := by
  have h:=Expr.executes_of_valid (input H A C θ) (objectiveExpr a k)
    (objectiveExpr_valid a _ hd k)
  cases k <;> exact h

theorem compilationCost_le (a : Fin d) : compilationCost (ι:=ι) a≤setupCost (Fintype.card ι) d := by
  have hp : (pencilCircuit (ι:=ι) a).cost≤
      (dimension a+1)*(matrixSize (Fin d))^2*(blockBound (Fintype.card ι) d+3) := by
    calc _≤∑_p:QueryIndex a×Fin (matrixSize (Fin d))×Fin (matrixSize (Fin d)),
        (blockBound (Fintype.card ι) d+3) := by
          unfold Circuit.cost
          apply Finset.sum_le_sum
          intro p _
          exact Nat.add_le_add_right (pencilExpr_cost a p.1 p.2.1 p.2.2) 1
      _=_ := by simp [QueryIndex,pow_two,Nat.mul_assoc]
  have ho : (objectiveCircuit (ι:=ι) a).cost≤(dimension a+1)*(objectiveBound d+1) := by
    calc _≤∑_k:QueryIndex a,(objectiveBound d+1) := by
          unfold Circuit.cost
          apply Finset.sum_le_sum
          intro k _
          exact Nat.add_le_add_right (objectiveExpr_cost a k) 1
      _=_ := by simp [QueryIndex]
  have hdim : dimension a≤4*d^2 := by rw [KSFullManuscriptProgramSize.variableCount];omega
  have hp' : (pencilCircuit (ι:=ι) a).cost≤(4*d^2+1)*(10*d)^2*(blockBound (Fintype.card ι) d+3) :=
    hp.trans (by rw [KSFullManuscriptProgramSize.pencilOrder];gcongr)
  have ho' : (objectiveCircuit (ι:=ι) a).cost≤(4*d^2+1)*(objectiveBound d+1) :=
    ho.trans (by gcongr)
  have ht:=(SDPIndexTables.routing_cost a)
  have hm : (d+1)^4≤(Fintype.card ι+d+1)^4 := by gcongr;omega
  unfold compilationCost setupCost
  omega

theorem setup_cost_le (a : Fin d) (H : Matrix (Fin d) (Fin d) ℂ)
    (A : ι→Matrix (Fin d) (Fin d) ℂ) (hA : ∀i,(A i).IsHermitian)
    (C : Matrix ι ι ℝ) (hC : C.PosSemidef) (hd : 0<d) (θ : ℝ) :
    (setup a H A hA C hC hd θ).cost≤setupCost (Fintype.card ι) d := compilationCost_le a

open KSPolynomialConvexSolver

def ownerReport (P : PolynomialSolver) (a : Fin d) (H : Matrix (Fin d) (Fin d) ℂ)
    (A : ι→Matrix (Fin d) (Fin d) ℂ) (hA : ∀i,(A i).IsHermitian)
    (C : Matrix ι ι ℝ) (hC : C.PosSemidef) (hd : 0<d) (θ ν : ℝ) : Counted ℝ :=
  let q:=setup a H A hA C hC hd θ
  let r:=P.run q.value.data q.value.coefficient q.value.offset ν
  ⟨r.value,q.cost+r.cost⟩

theorem ownerReport_value (P : PolynomialSolver) (a : Fin d) (H : Matrix (Fin d) (Fin d) ℂ)
    (A : ι→Matrix (Fin d) (Fin d) ℂ) (hA : ∀i,(A i).IsHermitian)
    (C : Matrix ι ι ℝ) (hC : C.PosSemidef) (hd : 0<d) (θ ν : ℝ) :
    (ownerReport P a H A hA C hC hd θ ν).value =
      KSConvexValueOracle.ownerReport P.solver a H A hA C hC hd θ ν := by
  dsimp only [ownerReport]
  rw [setup_value]
  rfl

theorem ownerReport_cost_le (P : PolynomialSolver) (a : Fin d) (H : Matrix (Fin d) (Fin d) ℂ)
    (A : ι→Matrix (Fin d) (Fin d) ℂ) (hA : ∀i,(A i).IsHermitian)
    (C : Matrix ι ι ℝ) (hC : C.PosSemidef) (hd : 0<d) (θ ν : ℝ) (hν : 0<ν)
    {S V : ℕ} (hS : dataSize (dimension a) (matrixSize (Fin d))≤S) (hV : ν⁻¹≤(V:ℝ)) :
    (ownerReport P a H A hA C hC hd θ ν).cost≤
      setupCost (Fintype.card ι) d+P.coefficient*(S+V+1)^P.degree := by
  apply Nat.add_le_add (setup_cost_le a H A hA C hC hd θ)
  exact P.run_cost_le _ _ _ hν hS hV

end MatrixSpencer.RealRAM.OwnerSDPSetup
