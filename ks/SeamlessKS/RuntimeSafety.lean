import SeamlessKS.RuntimeDirection

/-! The scalar divisions and roots used in finite differences
have actual primitive execution witnesses at the computed tolerances. EVD has its own explicit primitive rule. -/
open Matrix
open scoped BigOperators
noncomputable section
namespace SeamlessKS.RuntimeSafety
open MatrixSpencer MatrixSpencer.RealRAM
open SeamlessKS.Parameters
variable {N d : ℕ}

def stencilRegisters (v : Fin N → Fin d → ℂ) (a b c e : ℝ) : Fin 5 → ℝ :=
  ![a,b,c,e,queryStep v]

/-- Values returned by the solver may be arbitrary real scalars here;
validity of the numerical formulas follows from the computed scales. -/
structure Safe (v : Fin N → Fin d → ℂ) : Prop where
  diagonal : ∀ a b c e, FullHessian.diagonalExpr.Valid (stencilRegisters v a b c e)
  mixed : ∀ a b c e, FullHessian.mixedExpr.Valid (stencilRegisters v a b c e)
  weighted : ∀ q : Fin 3 → ℝ, FullHessian.weightedExpr.Valid q
  spectral : ∀ m (A : Matrix (Fin m) (Fin m) ℝ), A.IsSymm →
    ExactEVD.Executes A (ExactEVD.compute A).value (ExactEVD.compute A).cost

theorem safe (v : Fin N → Fin d → ℂ) (hd : 0<d)
    (hp : ∑ i,KSRankOne.atom (v i)=1) : Safe v where
  diagonal a b c e := FullHessian.diagonalExpr_valid _ (queryStep_pos v hd hp).ne'
  mixed a b c e := FullHessian.mixedExpr_valid _ (queryStep_pos v hd hp).ne'
  weighted := FullHessian.weightedExpr_valid
  spectral _ A hA := ExactEVD.compute_execution A hA

theorem stencil_execution (v : Fin N → Fin d → ℂ) (hd : 0<d)
    (hp : ∑ i,KSRankOne.atom (v i)=1) (a b c e : ℝ) :
    Expr.Executes (stencilRegisters v a b c e) FullHessian.diagonalExpr
      (FullHessian.diagonalExpr.eval (stencilRegisters v a b c e)) FullHessian.diagonalExpr.cost ∧
    Expr.Executes (stencilRegisters v a b c e) FullHessian.mixedExpr
      (FullHessian.mixedExpr.eval (stencilRegisters v a b c e)) FullHessian.mixedExpr.cost :=
  ⟨Expr.executes_of_valid _ _ ((safe v hd hp).diagonal a b c e),
    Expr.executes_of_valid _ _ ((safe v hd hp).mixed a b c e)⟩

end SeamlessKS.RuntimeSafety
