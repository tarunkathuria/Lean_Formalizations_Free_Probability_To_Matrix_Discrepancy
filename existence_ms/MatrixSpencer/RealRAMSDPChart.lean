import MatrixSpencer.RealRAMComplexArithmetic
import MatrixSpencer.KSFullManuscriptAffineData

/-! The fixed SDP entry chart is generated from zero/one real instructions,
finite diagonal sums, and real signs. Finite index tests address the chart;
they neither inspect nor choose a spectral basis. -/
open scoped BigOperators Matrix
noncomputable section
namespace MatrixSpencer.RealRAM.SDPChart
open KSFullManuscriptSDPCoordinates KSFullManuscriptAffineData
variable {d : ℕ} {ρ : Type*}

def unitExpr (a : Fin d) (k : Fin (dimension a)) (p : Index a) : Expr ρ :=
  .constant (if Fintype.equivFin (Index a) p = k then 1 else 0)

@[simp] theorem unitExpr_eval (a : Fin d) (k : Fin (dimension a)) (p : Index a) (v : ρ→ℝ) :
    (unitExpr a k p).eval v = entries a (unit a k) p := by
  classical
  by_cases h:Fintype.equivFin (Index a) p=k <;> simp [unitExpr,Expr.eval,entries,unit,Pi.single_apply,h,eq_comm]

theorem unitExpr_valid (a : Fin d) (k : Fin (dimension a)) (p : Index a) (v : ρ→ℝ) :
    (unitExpr a k p).Valid v := trivial
@[simp] theorem unitExpr_cost (a : Fin d) (k : Fin (dimension a)) (p : Index a) :
    (unitExpr a k p : Expr ρ).cost=1 := rfl

def embedExpr (a : Fin d) (k : Fin (dimension a)) (p : Fin d×Fin d) : Expr ρ :=
  if h:p≠(a,a) then unitExpr a k (.inl (.inl ⟨p,h⟩)) else .constant 0

def completeExpr (a : Fin d) (k : Fin (dimension a)) (p : Fin d×Fin d) : Expr ρ :=
  .sub (embedExpr a k p) (if p=(a,a) then finiteSumExpr (fun i=>embedExpr a k (i,i)) else .constant 0)

@[simp] theorem embedExpr_eval (a : Fin d) (k : Fin (dimension a)) (p : Fin d×Fin d) (v : ρ→ℝ) :
    (embedExpr a k p).eval v = KSFullManuscriptTraceCoordinates.embed a
      (fun p=>entries a (unit a k) (.inl (.inl p))) p := by
  unfold embedExpr KSFullManuscriptTraceCoordinates.embed
  split <;> simp [Expr.eval]

@[simp] theorem completeExpr_eval (a : Fin d) (k : Fin (dimension a)) (p : Fin d×Fin d) (v : ρ→ℝ) :
    (completeExpr a k p).eval v = KSFullManuscriptTraceCoordinates.complete a
      (fun p=>entries a (unit a k) (.inl (.inl p))) p := by
  unfold completeExpr KSFullManuscriptTraceCoordinates.complete
  split <;> simp [Expr.eval,finiteSumExpr_eval]

theorem embedExpr_valid (a : Fin d) (k : Fin (dimension a)) (p : Fin d×Fin d) (v : ρ→ℝ) :
    (embedExpr a k p).Valid v := by unfold embedExpr;split <;> trivial
@[simp] theorem embedExpr_cost (a : Fin d) (k : Fin (dimension a)) (p : Fin d×Fin d) :
    (embedExpr a k p : Expr ρ).cost=1 := by unfold embedExpr;split <;> rfl

theorem completeExpr_valid (a : Fin d) (k : Fin (dimension a)) (p : Fin d×Fin d) (v : ρ→ℝ) :
    (completeExpr a k p).Valid v := by
  refine ⟨embedExpr_valid _ _ _ _,?_⟩
  split
  · exact finiteSumExpr_valid _ _ (fun i=>embedExpr_valid _ _ _ _)
  · trivial

theorem completeExpr_cost (a : Fin d) (k : Fin (dimension a)) (p : Fin d×Fin d) :
    (completeExpr a k p : Expr ρ).cost≤2*d+3 := by
  unfold completeExpr
  split <;> simp [Expr.cost,finiteSumExpr_cost] <;> omega

def decodeExpr (x : Fin d×Fin d→Expr ρ) (i j : Fin d) : ComplexExpr ρ :=
  if i=j then .real (x (i,i)) else if i<j then ⟨x (i,j),x (j,i)⟩
  else ⟨x (j,i),.sub (.constant 0) (x (i,j))⟩

@[simp] theorem decodeExpr_eval (x : Fin d×Fin d→Expr ρ) (v : ρ→ℝ) (i j : Fin d) :
    (decodeExpr x i j).eval v = KSFullManuscriptHermitianCoordinates.decode (fun p=>(x p).eval v) i j := by
  unfold decodeExpr KSFullManuscriptHermitianCoordinates.decode
  split_ifs <;> apply Complex.ext <;> simp [ComplexExpr.eval,ComplexExpr.real,Expr.eval]

theorem decodeExpr_valid (x : Fin d×Fin d→Expr ρ) (v : ρ→ℝ) (hx : ∀p,(x p).Valid v) (i j : Fin d) :
    (decodeExpr x i j).Valid v := by
  unfold decodeExpr
  split_ifs
  · exact ComplexExpr.valid_real _ _ (hx _)
  · exact ⟨hx _,hx _⟩
  · exact ⟨hx _,⟨trivial,hx _⟩⟩

theorem decodeExpr_cost (x : Fin d×Fin d→Expr ρ) (b : ℕ) (hx : ∀p,(x p).cost≤b) (i j : Fin d) :
    (decodeExpr x i j).cost≤2*b+2 := by
  unfold decodeExpr
  split_ifs <;> simp only [ComplexExpr.cost,ComplexExpr.real,Expr.cost]
  all_goals have h1:=hx (i,i);have h2:=hx (i,j);have h3:=hx (j,i);omega

def density (a : Fin d) (k : Fin (dimension a)) := decodeExpr (ρ:=ρ) (completeExpr a k)
def regularizer (a : Fin d) (k : Fin (dimension a)) :=
  decodeExpr (ρ:=ρ) (fun p=>unitExpr a k (.inl (.inr p)))
def fidelity (a : Fin d) (k : Fin (dimension a)) (i j : Fin d) : ComplexExpr ρ :=
  ⟨unitExpr a k (.inr (.inl (i,j))),unitExpr a k (.inr (.inr (i,j)))⟩

@[simp] theorem density_eval (a : Fin d) (k : Fin (dimension a)) (v : ρ→ℝ) (i j : Fin d) :
    (density a k i j).eval v = (densityLinear a (entries a (unit a k)) : Matrix (Fin d) (Fin d) ℂ) i j := by
  simp only [density,decodeExpr_eval,completeExpr_eval]
  rfl
@[simp] theorem regularizer_eval (a : Fin d) (k : Fin (dimension a)) (v : ρ→ℝ) (i j : Fin d) :
    (regularizer a k i j).eval v = (regularizerLinear a (entries a (unit a k)) : Matrix (Fin d) (Fin d) ℂ) i j := by
  simp only [regularizer,decodeExpr_eval,unitExpr_eval]
  rfl
@[simp] theorem fidelity_eval (a : Fin d) (k : Fin (dimension a)) (v : ρ→ℝ) (i j : Fin d) :
    (fidelity a k i j).eval v = fidelityLinear a (entries a (unit a k)) i j := by
  apply Complex.ext <;> simp [fidelity,ComplexExpr.eval,fidelityLinear]

theorem density_valid (a : Fin d) (k : Fin (dimension a)) (v : ρ→ℝ) (i j : Fin d) :
    (density a k i j).Valid v := decodeExpr_valid _ _ (fun p=>completeExpr_valid _ _ _ _) _ _
theorem regularizer_valid (a : Fin d) (k : Fin (dimension a)) (v : ρ→ℝ) (i j : Fin d) :
    (regularizer a k i j).Valid v := decodeExpr_valid _ _ (fun p=>unitExpr_valid _ _ _ _) _ _
theorem fidelity_valid (a : Fin d) (k : Fin (dimension a)) (v : ρ→ℝ) (i j : Fin d) :
    (fidelity a k i j).Valid v := ⟨trivial,trivial⟩
theorem density_cost (a : Fin d) (k : Fin (dimension a)) (i j : Fin d) :
    (density a k i j : ComplexExpr ρ).cost≤4*d+8 := by
  have h := decodeExpr_cost (ρ:=ρ) (completeExpr a k) (2*d+3) (fun p=>completeExpr_cost a k p) i j
  dsimp [density]
  omega
theorem regularizer_cost (a : Fin d) (k : Fin (dimension a)) (i j : Fin d) :
    (regularizer a k i j : ComplexExpr ρ).cost≤4 := decodeExpr_cost _ 1 (fun p=>le_of_eq (unitExpr_cost _ _ _)) _ _
theorem fidelity_cost (a : Fin d) (k : Fin (dimension a)) (i j : Fin d) :
    (fidelity a k i j : ComplexExpr ρ).cost=2 := rfl

end MatrixSpencer.RealRAM.SDPChart
