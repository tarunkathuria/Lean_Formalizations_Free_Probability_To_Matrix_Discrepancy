import MatrixSpencer.RealRAMSDPChart

/-! SDP chart expressions built from an already materialized address array.
The array is an explicit argument to every constructor. In particular these
constructors do not invoke a sorting or reverse-lookup routine. The caller
prepares the array once and stores it before generating scalar expressions. -/
namespace MatrixSpencer.RealRAM.PreparedSDPChart
open KSFullManuscriptSDPCoordinates KSFullManuscriptAffineData
variable {d : ℕ} {ρ : Type*}

/-- Read the stored chart address, compare it with the requested coordinate,
and emit the corresponding rational constant. -/
def unitExpr (a : Fin d) (address : Index a → ℕ)
    (k : Fin (dimension a)) (p : Index a) : Expr ρ :=
  .constant (if address p = k.val then 1 else 0)

def embedExpr (a : Fin d) (address : Index a → ℕ)
    (k : Fin (dimension a)) (p : Fin d × Fin d) : Expr ρ :=
  if h : p≠(a,a) then unitExpr a address k (.inl (.inl ⟨p,h⟩)) else .constant 0

def completeExpr (a : Fin d) (address : Index a → ℕ)
    (k : Fin (dimension a)) (p : Fin d × Fin d) : Expr ρ :=
  .sub (embedExpr a address k p)
    (if p=(a,a) then finiteSumExpr (fun i => embedExpr a address k (i,i)) else .constant 0)

def densityWith (a : Fin d) (address : Index a → ℕ) (k : Fin (dimension a)) :=
  SDPChart.decodeExpr (ρ:=ρ) (completeExpr a address k)

def regularizerWith (a : Fin d) (address : Index a → ℕ) (k : Fin (dimension a)) :=
  SDPChart.decodeExpr (ρ:=ρ) (fun p => unitExpr a address k (.inl (.inr p)))

def fidelityWith (a : Fin d) (address : Index a → ℕ)
    (k : Fin (dimension a)) (i j : Fin d) : ComplexExpr ρ :=
  ⟨unitExpr a address k (.inr (.inl (i,j))),
    unitExpr a address k (.inr (.inr (i,j)))⟩

/-- Substitution of the one prepared array produces exactly the certified
chart syntax. These equalities are about expressions, before evaluation. -/
@[simp] theorem unitExpr_eq (a : Fin d) (k : Fin (dimension a)) (p : Index a) :
    unitExpr (ρ:=ρ) a (SDPIndexTables.chartLookup a).value k p =
      SDPChart.unitExpr a k p := rfl

@[simp] theorem embedExpr_eq (a : Fin d) (k : Fin (dimension a)) (p : Fin d × Fin d) :
    embedExpr (ρ:=ρ) a (SDPIndexTables.chartLookup a).value k p =
      SDPChart.embedExpr a k p := rfl

@[simp] theorem completeExpr_eq (a : Fin d) (k : Fin (dimension a)) (p : Fin d × Fin d) :
    completeExpr (ρ:=ρ) a (SDPIndexTables.chartLookup a).value k p =
      SDPChart.completeExpr a k p := rfl

@[simp] theorem densityWith_on_table (a : Fin d) (k : Fin (dimension a)) :
    densityWith (ρ:=ρ) a (SDPIndexTables.chartLookup a).value k = SDPChart.density a k := rfl

@[simp] theorem regularizerWith_on_table (a : Fin d) (k : Fin (dimension a)) :
    regularizerWith (ρ:=ρ) a (SDPIndexTables.chartLookup a).value k = SDPChart.regularizer a k := rfl

@[simp] theorem fidelityWith_on_table (a : Fin d) (k : Fin (dimension a)) :
    fidelityWith (ρ:=ρ) a (SDPIndexTables.chartLookup a).value k = SDPChart.fidelity a k := rfl

end MatrixSpencer.RealRAM.PreparedSDPChart
