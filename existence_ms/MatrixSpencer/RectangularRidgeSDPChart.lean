import MatrixSpencer.RealRAMSDPChart
import MatrixSpencer.DyadicSDPCoordinates

/-! The fixed SDP entry chart is generated from zero/one real instructions,
finite diagonal sums, and real signs. Finite index tests address the chart;
they neither inspect nor choose a spectral basis. -/
open scoped BigOperators Matrix
noncomputable section
namespace MatrixSpencer.RealRAM.RectangularRidgeSDPChart
open DyadicSDPCoordinates
open SDPChart (decodeExpr decodeExpr_eval decodeExpr_valid decodeExpr_cost)
variable {d : ℕ} {ρ : Type*}

def unitExpr (m : ℕ) (a : Fin d) (k : Fin (dimension m a)) (p : Index m a) : Expr ρ :=
  .constant (if Fintype.equivFin (Index m a) p = k then 1 else 0)

@[simp] theorem unitExpr_eval (m : ℕ) (a : Fin d) (k : Fin (dimension m a)) (p : Index m a) (v : ρ→ℝ) :
    (unitExpr m a k p).eval v = entries m a (unit m a k) p := by
  classical
  by_cases h:Fintype.equivFin (Index m a) p=k <;> simp [unitExpr,Expr.eval,entries,unit,h]

theorem unitExpr_valid (m : ℕ) (a : Fin d) (k : Fin (dimension m a)) (p : Index m a) (v : ρ→ℝ) :
    (unitExpr m a k p).Valid v := trivial
@[simp] theorem unitExpr_cost (m : ℕ) (a : Fin d) (k : Fin (dimension m a)) (p : Index m a) :
    (unitExpr m a k p : Expr ρ).cost=1 := rfl

def embedExpr (m : ℕ) (a : Fin d) (k : Fin (dimension m a)) (p : Fin d×Fin d) : Expr ρ :=
  if h:p≠(a,a) then unitExpr m a k (.inl (.inl ⟨p,h⟩)) else .constant 0

def completeExpr (m : ℕ) (a : Fin d) (k : Fin (dimension m a)) (p : Fin d×Fin d) : Expr ρ :=
  .sub (embedExpr m a k p) (if p=(a,a) then finiteSumExpr (fun i=>embedExpr m a k (i,i)) else .constant 0)

@[simp] theorem embedExpr_eval (m : ℕ) (a : Fin d) (k : Fin (dimension m a)) (p : Fin d×Fin d) (v : ρ→ℝ) :
    (embedExpr m a k p).eval v = KSFullManuscriptTraceCoordinates.embed a
      (fun p=>entries m a (unit m a k) (.inl (.inl p))) p := by
  unfold embedExpr KSFullManuscriptTraceCoordinates.embed
  split <;> simp [Expr.eval]

@[simp] theorem completeExpr_eval (m : ℕ) (a : Fin d) (k : Fin (dimension m a)) (p : Fin d×Fin d) (v : ρ→ℝ) :
    (completeExpr m a k p).eval v = KSFullManuscriptTraceCoordinates.complete a
      (fun p=>entries m a (unit m a k) (.inl (.inl p))) p := by
  unfold completeExpr KSFullManuscriptTraceCoordinates.complete
  split <;> simp [Expr.eval,finiteSumExpr_eval]

theorem embedExpr_valid (m : ℕ) (a : Fin d) (k : Fin (dimension m a)) (p : Fin d×Fin d) (v : ρ→ℝ) :
    (embedExpr m a k p).Valid v := by unfold embedExpr;split <;> trivial
@[simp] theorem embedExpr_cost (m : ℕ) (a : Fin d) (k : Fin (dimension m a)) (p : Fin d×Fin d) :
    (embedExpr m a k p : Expr ρ).cost=1 := by unfold embedExpr;split <;> rfl

theorem completeExpr_valid (m : ℕ) (a : Fin d) (k : Fin (dimension m a)) (p : Fin d×Fin d) (v : ρ→ℝ) :
    (completeExpr m a k p).Valid v := by
  refine ⟨embedExpr_valid _ _ _ _ _,?_⟩
  split
  · exact finiteSumExpr_valid _ _ (fun i=>embedExpr_valid _ _ _ _ _)
  · trivial

theorem completeExpr_cost (m : ℕ) (a : Fin d) (k : Fin (dimension m a)) (p : Fin d×Fin d) :
    (completeExpr m a k p : Expr ρ).cost≤2*d+3 := by
  unfold completeExpr
  split <;> simp [Expr.cost,finiteSumExpr_cost] <;> omega

def density (m : ℕ) (a : Fin d) (k : Fin (dimension m a)) := decodeExpr (ρ:=ρ) (completeExpr m a k)
def auxiliary (m : ℕ) (a : Fin d) (r : Fin m) (k : Fin (dimension m a)) :=
  decodeExpr (ρ:=ρ) (fun p=>unitExpr m a k (.inl (.inr (r,p))))
def fidelity (m : ℕ) (a : Fin d) (k : Fin (dimension m a)) (i j : Fin d) : ComplexExpr ρ :=
  ⟨unitExpr m a k (.inr (.inl (i,j))),unitExpr m a k (.inr (.inr (i,j)))⟩

@[simp] theorem density_eval (m : ℕ) (a : Fin d) (k : Fin (dimension m a)) (v : ρ→ℝ) (i j : Fin d) :
    (density m a k i j).eval v = (densityLinear m a (entries m a (unit m a k)) : Matrix (Fin d) (Fin d) ℂ) i j := by
  simp only [density,decodeExpr_eval,completeExpr_eval]
  rfl
@[simp] theorem auxiliary_eval (m : ℕ) (a : Fin d) (r : Fin m) (k : Fin (dimension m a)) (v : ρ→ℝ) (i j : Fin d) :
    (auxiliary m a r k i j).eval v = (auxiliaryLinear m a r (entries m a (unit m a k)) : Matrix (Fin d) (Fin d) ℂ) i j := by
  simp only [auxiliary,decodeExpr_eval,unitExpr_eval]
  rfl
@[simp] theorem fidelity_eval (m : ℕ) (a : Fin d) (k : Fin (dimension m a)) (v : ρ→ℝ) (i j : Fin d) :
    (fidelity m a k i j).eval v = fidelityLinear m a (entries m a (unit m a k)) i j := by
  apply Complex.ext <;> simp [fidelity,ComplexExpr.eval,fidelityLinear]

theorem density_valid (m : ℕ) (a : Fin d) (k : Fin (dimension m a)) (v : ρ→ℝ) (i j : Fin d) :
    (density m a k i j).Valid v := decodeExpr_valid _ _ (fun _p=>completeExpr_valid _ _ _ _ _) _ _
theorem auxiliary_valid (m : ℕ) (a : Fin d) (r : Fin m) (k : Fin (dimension m a)) (v : ρ→ℝ) (i j : Fin d) :
    (auxiliary m a r k i j).Valid v := decodeExpr_valid _ _ (fun _p=>unitExpr_valid _ _ _ _ _) _ _
theorem fidelity_valid (m : ℕ) (a : Fin d) (k : Fin (dimension m a)) (v : ρ→ℝ) (i j : Fin d) :
    (fidelity m a k i j).Valid v := ⟨trivial,trivial⟩
theorem density_cost (m : ℕ) (a : Fin d) (k : Fin (dimension m a)) (i j : Fin d) :
    (density m a k i j : ComplexExpr ρ).cost≤4*d+8 := by
  have h := decodeExpr_cost (ρ:=ρ) (completeExpr m a k) (2*d+3) (fun p=>completeExpr_cost m a k p) i j
  dsimp [density]
  omega
theorem auxiliary_cost (m : ℕ) (a : Fin d) (r : Fin m) (k : Fin (dimension m a)) (i j : Fin d) :
    (auxiliary m a r k i j : ComplexExpr ρ).cost≤4 := decodeExpr_cost _ 1 (fun _p=>le_of_eq (unitExpr_cost _ _ _ _)) _ _
theorem fidelity_cost (m : ℕ) (a : Fin d) (k : Fin (dimension m a)) (i j : Fin d) :
    (fidelity m a k i j : ComplexExpr ρ).cost=2 := rfl

end MatrixSpencer.RealRAM.RectangularRidgeSDPChart
