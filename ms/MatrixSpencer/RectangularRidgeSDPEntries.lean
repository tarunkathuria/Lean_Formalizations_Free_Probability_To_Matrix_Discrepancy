import MatrixSpencer.RectangularRidgeSDPChart
import MatrixSpencer.RealRAMOwnerSDPSetup
import MatrixSpencer.RectangularRidgeSymmetricQueries

/-! Literal ridge-SDP array entries compiled from safe real arithmetic. The
covariance source is a double sum in its entries. The dyadic chain changes
only finite addressing; the ridge is the fixed rational weight `1/d`. -/
open scoped BigOperators Matrix
noncomputable section
namespace MatrixSpencer.RealRAM.RectangularRidgeSDPEntries
open OwnerSDPBlocks
open DyadicSDPCoordinates DyadicSDPAffineData
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
abbrev Reg := Registers ι d
abbrev QueryIndex (m : ℕ) (a : Fin d) := Option (Fin (dimension m a))

def densityExpr (m : ℕ) (a : Fin d) : QueryIndex m a → Fin d → Fin d → ComplexExpr (Reg (ι:=ι) (d:=d))
  | none => OwnerSDPSetup.baseDensity
  | some k => RectangularRidgeSDPChart.density m a k

def chainExpr (m : ℕ) (a : Fin d) (k : QueryIndex m a) :
    Fin (m+1) → Fin d → Fin d → ComplexExpr (Reg (ι:=ι) (d:=d)) :=
  Fin.cases (match k with | none => OwnerSDPSetup.identity | some _ => fun _ _ => .zero)
    (fun r => match k with | none => fun _ _ => .zero | some k => RectangularRidgeSDPChart.auxiliary m a r k)

def fidelityExpr (m : ℕ) (a : Fin d) : QueryIndex m a → Fin d → Fin d → ComplexExpr (Reg (ι:=ι) (d:=d))
  | none => fun _ _ => .zero
  | some k => RectangularRidgeSDPChart.fidelity m a k

@[simp] theorem densityExpr_eval (m : ℕ) (a : Fin d) (v : Reg (ι:=ι) (d:=d)→ℝ)
    (k : QueryIndex m a) (i j : Fin d) :
    (densityExpr m a k i j).eval v = (match k with
      | none => (DyadicOwnerSDP.center a : Matrix (Fin d) (Fin d) ℂ)
      | some k => densityLinear m a (entries m a (unit m a k))) i j := by
  cases k with
  | none =>
    rw [densityExpr, OwnerSDPSetup.baseDensity_eval v (Nat.zero_lt_of_lt a.isLt)]
    simp [DyadicOwnerSDP.center,KSFullManuscriptCenterData.densityCenter,KSFullManuscriptStrictFeasible.density,maximallyMixed]
  | some k => exact RectangularRidgeSDPChart.density_eval m a k v i j

@[simp] theorem chainExpr_eval (m : ℕ) (a : Fin d) (v : Reg (ι:=ι) (d:=d)→ℝ)
    (k : QueryIndex m a) (r : Fin (m+1)) (i j : Fin d) :
    (chainExpr m a k r i j).eval v = (match k with
      | none => chain m a 0 r
      | some k => chainLinear m a r (entries m a (unit m a k))) i j := by
  refine Fin.cases ?_ (fun r => ?_) r
  · cases k <;> simp [chainExpr, chain, chainLinear]
  · cases k <;> simp [chainExpr, chain, chainLinear]

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem fidelityExpr_eval (m : ℕ) (a : Fin d) (v : Reg (ι:=ι) (d:=d)→ℝ)
    (k : QueryIndex m a) (i j : Fin d) :
    (fidelityExpr m a k i j).eval v = (match k with
      | none => 0
      | some k => fidelityLinear m a (entries m a (unit m a k))) i j := by
  cases k <;> simp [fidelityExpr]

theorem densityExpr_valid (m : ℕ) (a : Fin d) (v : Reg (ι:=ι) (d:=d)→ℝ)
    (k : QueryIndex m a) (i j : Fin d) : (densityExpr m a k i j).Valid v := by
  cases k
  · exact OwnerSDPSetup.baseDensity_valid v (Nat.zero_lt_of_lt a.isLt) i j
  · exact RectangularRidgeSDPChart.density_valid _ _ _ _ _ _

omit [Fintype ι] [DecidableEq ι] in
theorem chainExpr_valid (m : ℕ) (a : Fin d) (v : Reg (ι:=ι) (d:=d)→ℝ)
    (k : QueryIndex m a) (r : Fin (m+1)) (i j : Fin d) : (chainExpr m a k r i j).Valid v := by
  refine Fin.cases ?_ (fun r => ?_) r
  · cases k <;> exact ⟨trivial,trivial⟩
  · cases k
    · exact ⟨trivial,trivial⟩
    · exact RectangularRidgeSDPChart.auxiliary_valid _ _ _ _ _ _ _

omit [Fintype ι] [DecidableEq ι] in
theorem fidelityExpr_valid (m : ℕ) (a : Fin d) (v : Reg (ι:=ι) (d:=d)→ℝ)
    (k : QueryIndex m a) (i j : Fin d) : (fidelityExpr m a k i j).Valid v := by
  cases k <;> exact ⟨trivial,trivial⟩

theorem densityExpr_cost (m : ℕ) (a : Fin d) (k : QueryIndex m a) (i j : Fin d) :
    (densityExpr (ι:=ι) m a k i j).cost ≤ 4*d+8 := by
  cases k
  · exact (OwnerSDPSetup.baseDensity_cost i j).trans (by omega)
  · exact RectangularRidgeSDPChart.density_cost _ _ _ _ _

omit [Fintype ι] [DecidableEq ι] in
theorem chainExpr_cost (m : ℕ) (a : Fin d) (k : QueryIndex m a) (r : Fin (m+1)) (i j : Fin d) :
    (chainExpr (ι:=ι) m a k r i j).cost ≤ 4 := by
  refine Fin.cases ?_ (fun r => ?_) r
  · cases k <;> simp [chainExpr, OwnerSDPSetup.identity, ComplexExpr.cost_real, ComplexExpr.cost_zero, Expr.cost]
  · cases k
    · norm_num [chainExpr, ComplexExpr.cost_zero]
    · exact RectangularRidgeSDPChart.auxiliary_cost _ _ _ _ _ _

omit [Fintype ι] [DecidableEq ι] in
theorem fidelityExpr_cost (m : ℕ) (a : Fin d) (k : QueryIndex m a) (i j : Fin d) :
    (fidelityExpr (ι:=ι) m a k i j).cost ≤ 2 := by cases k <;> exact le_rfl

def blockExpr (m : ℕ) (S : Fin d→Fin d→ComplexExpr (Reg (ι:=ι) (d:=d)))
    (X : Fin (m+1)→Fin d→Fin d→ComplexExpr (Reg (ι:=ι) (d:=d)))
    (Z : Fin d→Fin d→ComplexExpr (Reg (ι:=ι) (d:=d))) :
    Constraint m → (Fin d⊕Fin d) → (Fin d⊕Fin d) → ComplexExpr (Reg (ι:=ι) (d:=d)) :=
  Sum.elim (fun _ => blocks S Z (fun i j=>.conj (Z j i)) (source S))
    (Sum.elim (fun j => blocks S (X j.succ) (X j.succ) (X j.castSucc))
      (fun j => blocks (X j.succ) (fun _ _=>.zero) (fun _ _=>.zero) (fun _ _=>.zero)))

theorem blockExpr_eval (m : ℕ) (H : Matrix (Fin d) (Fin d) ℂ)
    (A : ι→Matrix (Fin d) (Fin d) ℂ) (C : Matrix ι ι ℝ) (θ : ℝ)
    (S : Fin d→Fin d→ComplexExpr (Reg (ι:=ι) (d:=d)))
    (X : Fin (m+1)→Fin d→Fin d→ComplexExpr (Reg (ι:=ι) (d:=d)))
    (Z : Fin d→Fin d→ComplexExpr (Reg (ι:=ι) (d:=d))) (b : Constraint m) (i j) :
    (blockExpr m S X Z b i j).eval (input H A C θ) = block A C m
      (Matrix.of (fun i j=>(S i j).eval (input H A C θ)))
      (fun r=>Matrix.of (fun i j=>(X r i j).eval (input H A C θ)))
      (Matrix.of (fun i j=>(Z i j).eval (input H A C θ))) b i j := by
  rcases b with u | (r|r) <;> cases i <;> cases j <;>
    simp [blockExpr,blocks,block,Matrix.conjTranspose_apply]

theorem blockExpr_valid (m : ℕ) (v : Reg (ι:=ι) (d:=d)→ℝ)
    (S : Fin d→Fin d→ComplexExpr (Reg (ι:=ι) (d:=d)))
    (X : Fin (m+1)→Fin d→Fin d→ComplexExpr (Reg (ι:=ι) (d:=d)))
    (Z : Fin d→Fin d→ComplexExpr (Reg (ι:=ι) (d:=d)))
    (hS : ∀i j,(S i j).Valid v) (hX : ∀r i j,(X r i j).Valid v)
    (hZ : ∀i j,(Z i j).Valid v) (b : Constraint m) (i j) :
    (blockExpr m S X Z b i j).Valid v := by
  rcases b with u | (r|r)
  · exact blocks_valid _ _ _ _ _ hS hZ (fun i j=>ComplexExpr.valid_conj (hZ j i)) (source_valid _ _ hS) i j
  · exact blocks_valid _ _ _ _ _ hS (hX _) (hX _) (hX _) i j
  · exact blocks_valid (X r.succ) (fun _ _=>.zero) (fun _ _=>.zero) (fun _ _=>.zero) v (hX _) (fun _ _=>⟨trivial,trivial⟩)
      (fun _ _=>⟨trivial,trivial⟩) (fun _ _=>⟨trivial,trivial⟩) i j

theorem blockExpr_cost (m : ℕ)
    (S : Fin d→Fin d→ComplexExpr (Reg (ι:=ι) (d:=d)))
    (X : Fin (m+1)→Fin d→Fin d→ComplexExpr (Reg (ι:=ι) (d:=d)))
    (Z : Fin d→Fin d→ComplexExpr (Reg (ι:=ι) (d:=d)))
    (hS : ∀i j,(S i j).cost≤4*d+8) (hX : ∀r i j,(X r i j).cost≤4)
    (hZ : ∀i j,(Z i j).cost≤2) (b : Constraint m) (i j) :
    (blockExpr m S X Z b i j).cost≤OwnerSDPSetup.blockBound (Fintype.card ι) d := by
  let B:=OwnerSDPSetup.blockBound (Fintype.card ι) d
  have hs : ∀i j,(S i j).cost≤B := fun i j=>(hS i j).trans (by dsimp [B,OwnerSDPSetup.blockBound];omega)
  have hx : ∀r i j,(X r i j).cost≤B := fun r i j=>(hX r i j).trans (by dsimp [B,OwnerSDPSetup.blockBound];omega)
  have hz : ∀i j,(Z i j).cost≤B := fun i j=>(hZ i j).trans (by dsimp [B,OwnerSDPSetup.blockBound];omega)
  have hzero : 2≤B := by dsimp [B,OwnerSDPSetup.blockBound];omega
  rcases b with u | (r|r)
  · apply blocks_cost _ _ _ _ B hs hz
    · intro i j;rw [ComplexExpr.cost_conj];have h:=hZ j i;dsimp [B,OwnerSDPSetup.blockBound];omega
    · exact fun i j=>(source_cost S _ hS i j).trans (by dsimp [B,OwnerSDPSetup.blockBound];omega)
  · exact blocks_cost _ _ _ _ B hs (hx _) (hx _) (hx _) i j
  · exact blocks_cost (X r.succ) (fun _ _=>.zero) (fun _ _=>.zero) (fun _ _=>.zero) B (hx _) (fun _ _=>hzero) (fun _ _=>hzero) (fun _ _=>hzero) i j

def pencilExpr (m : ℕ) (a : Fin d) (k : QueryIndex m a) (b : Constraint m)
    (i j : Fin (matrixSize (Fin d))) : Expr (Reg (ι:=ι) (d:=d)) :=
  realify (blockExpr m (densityExpr m a k) (chainExpr m a k) (fidelityExpr m a k) b)
    ((Fintype.equivFin (RealIndex (Fin d))).symm i)
    ((Fintype.equivFin (RealIndex (Fin d))).symm j)

theorem pencilExpr_eval (m : ℕ) (a : Fin d) (H : Matrix (Fin d) (Fin d) ℂ)
    (A : ι→Matrix (Fin d) (Fin d) ℂ) (C : Matrix ι ι ℝ) (θ : ℝ)
    (k : QueryIndex m a) (b : Constraint m) (i j : Fin (matrixSize (Fin d))) :
    (pencilExpr m a k b i j).eval (input H A C θ) = (match k with
      | none => constant m a A C (DyadicOwnerSDP.center a) b
      | some k => finiteLinear m a A C b (unit m a k)) i j := by
  simp only [pencilExpr,realify_eval]
  have he := funext (fun i=>funext (fun j=>blockExpr_eval m H A C θ
    (densityExpr m a k) (chainExpr m a k) (fidelityExpr m a k) b i j))
  rw [he]
  cases k <;> simp only [densityExpr_eval,chainExpr_eval,fidelityExpr_eval]
  all_goals rfl

theorem pencilExpr_valid (m : ℕ) (a : Fin d) (v : Reg (ι:=ι) (d:=d)→ℝ)
    (k : QueryIndex m a) (b : Constraint m) (i j : Fin (matrixSize (Fin d))) :
    (pencilExpr m a k b i j).Valid v :=
  realify_valid _ v (blockExpr_valid m v _ _ _ (densityExpr_valid m a v k)
    (chainExpr_valid m a v k) (fidelityExpr_valid m a v k) b) _ _

theorem pencilExpr_cost (m : ℕ) (a : Fin d) (k : QueryIndex m a) (b : Constraint m)
    (i j : Fin (matrixSize (Fin d))) :
    (pencilExpr (ι:=ι) m a k b i j).cost≤OwnerSDPSetup.blockBound (Fintype.card ι) d+2 :=
  realify_cost _ _ (blockExpr_cost m _ _ _ (densityExpr_cost m a k)
    (chainExpr_cost m a k) (fidelityExpr_cost m a k) b) _ _

end MatrixSpencer.RealRAM.RectangularRidgeSDPEntries
