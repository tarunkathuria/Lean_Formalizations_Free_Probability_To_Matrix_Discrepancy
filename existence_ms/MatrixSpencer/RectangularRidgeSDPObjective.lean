import MatrixSpencer.RectangularRidgeSDPEntries

/-! Safe primitive compilation of the actual affine objective, including
`θ 2^m/(2^m−1)` by repeated doubling and the ridge coefficient `2/d`. -/
open scoped BigOperators Matrix
noncomputable section
namespace MatrixSpencer.RealRAM.RectangularRidgeSDPEntries
open OwnerSDPBlocks
open OwnerSDPSetup (traceExpr traceExpr_eval traceExpr_valid traceExpr_cost)
open DyadicSDPCoordinates
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

private def powerExpr {ρ : Type*} : ℕ → Expr ρ
  | 0 => .constant 1
  | m+1 => .mul (powerExpr m) (.constant 2)

private theorem powerExpr_eval {ρ : Type*} (m : ℕ) (v : ρ→ℝ) :
    (powerExpr m).eval v = (2:ℝ)^m := by
  induction m with
  | zero => simp [powerExpr,Expr.eval]
  | succ m ih => simp [powerExpr,Expr.eval,ih,pow_succ]

private theorem powerExpr_valid {ρ : Type*} (m : ℕ) (v : ρ→ℝ) : (powerExpr m).Valid v := by
  induction m with
  | zero => trivial
  | succ m ih => exact ⟨ih,trivial⟩

private theorem powerExpr_cost {ρ : Type*} (m : ℕ) : (powerExpr (ρ:=ρ) m).cost=2*m+1 := by
  induction m with
  | zero => rfl
  | succ m ih => simp [powerExpr,Expr.cost,ih];omega

def chainWeightExpr (m : ℕ) : Expr (Reg (ι:=ι) (d:=d)) :=
  .div (.mul theta (powerExpr m)) (.sub (powerExpr m) (.constant 1))

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem chainWeightExpr_eval (m : ℕ) (H : Matrix (Fin d) (Fin d) ℂ)
    (A : ι→Matrix (Fin d) (Fin d) ℂ) (C : Matrix ι ι ℝ) (θ : ℝ) :
    (chainWeightExpr m).eval (input H A C θ)=θ*(2:ℝ)^m/((2:ℝ)^m-1) := by
  simp [chainWeightExpr,Expr.eval,powerExpr_eval,theta,input]

omit [Fintype ι] [DecidableEq ι] in
theorem chainWeightExpr_valid (m : ℕ) (hm : 1≤m) (v : Reg (ι:=ι) (d:=d)→ℝ) :
    (chainWeightExpr m).Valid v := by
  refine ⟨⟨trivial,powerExpr_valid m v⟩,⟨powerExpr_valid m v,trivial⟩,?_⟩
  simp only [Expr.eval,powerExpr_eval,Rat.cast_one,sub_ne_zero]
  exact ne_of_gt (one_lt_pow₀ (by norm_num) (by omega))

omit [Fintype ι] [DecidableEq ι] in
theorem chainWeightExpr_cost (m : ℕ) : (chainWeightExpr (ι:=ι) (d:=d) m).cost=4*m+7 := by
  simp [chainWeightExpr,Expr.cost,powerExpr_cost,theta];omega

def ridgeWeightExpr : Expr (Reg (ι:=ι) (d:=d)) := .div (.constant 2) (.constant d)

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem ridgeWeightExpr_eval (v : Reg (ι:=ι) (d:=d)→ℝ) :
    ridgeWeightExpr.eval v=2*(1/(d:ℝ)) := by simp [ridgeWeightExpr,Expr.eval,div_eq_mul_inv]

omit [Fintype ι] [DecidableEq ι] in
theorem ridgeWeightExpr_valid (a : Fin d) (v : Reg (ι:=ι) (d:=d)→ℝ) :
    ridgeWeightExpr.Valid v := by
  refine ⟨trivial,trivial,?_⟩
  simp only [Expr.eval,Rat.cast_natCast]
  exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt a.isLt))

def objectiveExpr (m : ℕ) (hm : 1≤m) (a : Fin d) (k : QueryIndex m a) :
    Expr (Reg (ι:=ι) (d:=d)) :=
  .add (.add (.add (traceExpr (ComplexExpr.matrixMul center (densityExpr m a k)))
    (.mul (.constant 2) (traceExpr (fidelityExpr m a k))))
    (.mul (chainWeightExpr m) (traceExpr (chainExpr m a k (Fin.last m)))))
    (.mul ridgeWeightExpr (traceExpr (chainExpr m a k ⟨1,by omega⟩)))

@[simp] theorem objectiveExpr_eval (m : ℕ) (hm : 1≤m) (a : Fin d)
    (H : Matrix (Fin d) (Fin d) ℂ) (A : ι→Matrix (Fin d) (Fin d) ℂ)
    (C : Matrix ι ι ℝ) (θ : ℝ) (k : QueryIndex m a) :
    (objectiveExpr m hm a k).eval (input H A C θ) = match k with
    | none => RectangularRidgeAffineSDP.offset m hm a H θ (1/d)
    | some k => RectangularRidgeAffineSDP.coefficient m hm a H θ (1/d) k := by
  cases k <;> simp only [objectiveExpr,Expr.eval,traceExpr_eval,
    ComplexExpr.matrixMul_eval,center_eval,densityExpr_eval,fidelityExpr_eval,
    chainWeightExpr_eval,chainExpr_eval,ridgeWeightExpr_eval,Rat.cast_ofNat]
  · rfl
  · rfl

theorem objectiveExpr_valid (m : ℕ) (hm : 1≤m) (a : Fin d)
    (v : Reg (ι:=ι) (d:=d)→ℝ) (k : QueryIndex m a) :
    (objectiveExpr m hm a k).Valid v := by
  refine ⟨⟨⟨traceExpr_valid _ _ ?_,⟨trivial,traceExpr_valid _ _ ?_⟩⟩,
    ⟨chainWeightExpr_valid m hm v,traceExpr_valid _ _ ?_⟩⟩,
    ⟨ridgeWeightExpr_valid a v,traceExpr_valid _ _ ?_⟩⟩
  · exact ComplexExpr.matrixMul_valid center _ v (fun _ _=>⟨trivial,trivial⟩)
      (densityExpr_valid m a v k)
  · exact fidelityExpr_valid m a v k
  · exact chainExpr_valid m a v k _
  · exact chainExpr_valid m a v k _

def objectiveBound (m d : ℕ) := d*(productBound d 2 (4*d+8)+1)+20*d+4*m+40

theorem objectiveExpr_cost (m : ℕ) (hm : 1≤m) (a : Fin d) (k : QueryIndex m a) :
    (objectiveExpr (ι:=ι) m hm a k).cost≤objectiveBound m d := by
  have hp := traceExpr_cost (ComplexExpr.matrixMul center (densityExpr (ι:=ι) m a k))
    (productBound d 2 (4*d+8)) (fun i j=>by
      simpa [productBound] using ComplexExpr.matrixMul_cost center (densityExpr (ι:=ι) m a k) 2 (4*d+8)
        (fun _ _=>le_rfl) (densityExpr_cost m a k) i j)
  have hz := traceExpr_cost _ _ (fidelityExpr_cost (ι:=ι) m a k)
  have hx := traceExpr_cost _ _ (chainExpr_cost (ι:=ι) m a k (Fin.last m))
  have hr := traceExpr_cost _ _ (chainExpr_cost (ι:=ι) m a k (⟨1,by omega⟩:Fin (m+1)))
  simp only [objectiveExpr,Expr.cost,chainWeightExpr_cost,ridgeWeightExpr]
  dsimp [Expr.cost,objectiveBound] at *
  omega

end MatrixSpencer.RealRAM.RectangularRidgeSDPEntries
