import RadialKS.RuntimeWalk
import SeamlessKS.RuntimeSafety

/-! Execution witnesses for all newly introduced scalar and spectral recipes.
The Householder frame is computed using scalar arithmetic, a sign comparison,
and safe division. The only spectral primitive is the original exact EVD. -/
open Matrix
open scoped BigOperators
noncomputable section
namespace RadialKS.RuntimeSafety
open MatrixSpencer MatrixSpencer.RealRAM
open RadialBasis (Space)
open FrameArithmetic
variable {N d : ℕ}

structure Safe (v : Fin N → Fin d → ℂ) : Prop where
  stencil : SeamlessKS.RuntimeSafety.Safe v
  norm : ∀ m (z : Space m),
    Expr.Executes (WithLp.ofLp z) (normExpr m) ‖z‖ (4*m+2)
  zeroTest : ∀ m (z : Space m), (normExpr m).eval (WithLp.ofLp z)=0 ↔ z=0
  signValue : ∀ m (q : Space (m+1)), signProgram.run ![q 0,0] 1=RadialBasis.sign q
  normalize : ∀ m (z : Space (m+1)), z≠0 → ∀i,
    Expr.Executes (WithLp.ofLp z) (normalizedExpr (m+1) i)
      (Frame.unitVector z i) (4*(m+1)+4)
  sign : ∀ m (q : Space (m+1)),
    Program.Executes signProgram ![q 0,0] (signProgram.run ![q 0,0]) 5
  normal : ∀ m (z : Space (m+1)), z≠0 → ∀i,
    Expr.Executes (normalInput (Frame.unitVector z)) (normalExpr m i)
      (FrameArithmetic.normal z i) 3
  reflect : ∀ m (z : Space (m+1)), z≠0 → ∀i j,
    Expr.Executes (WithLp.ofLp (FrameArithmetic.normal z)) (reflectionExpr (m+1) i j)
      ((if i=j then 1 else 0)-2*FrameArithmetic.normal z i*FrameArithmetic.normal z j/‖FrameArithmetic.normal z‖^2)
      (4*(m+1)+9)
  multiply : ∀ m n p (A : Matrix (Fin m) (Fin n) ℝ) (B : Matrix (Fin n) (Fin p) ℝ) i j,
    Expr.Executes (matrixInput A B) ((matrixMulCircuit m n p).output (i,j))
      ((RuntimeMatrix.product A B).value i j) (4*n+1)
  compressed : ∀ m (R : FullHessian.Report m) (z : Space m) t,
    let H := FullHessian.matrix R t
    let K := FullHessian.weighted (fun _ => 1) H.value
    let U := RuntimeFrame.compute z
    let L := RuntimeMatrix.product U.valueᵀ K.value
    let B := RuntimeMatrix.product L.value U.value
    SeamlessKS.ExactEVD.Executes B.value (SeamlessKS.ExactEVD.compute B.value).value
      (SeamlessKS.ExactEVD.compute B.value).cost
  compare : ∀ p m,
    Program.Executes RuntimeMotion.choiceProgram (RuntimeMotion.choiceInput p m)
      (RuntimeMotion.choiceProgram.run (RuntimeMotion.choiceInput p m)) 5
  compareValue : ∀ p m,
    RuntimeMotion.choiceProgram.run (RuntimeMotion.choiceInput p m) 2 =
      if DeterministicRun.choosePlus p m then 1 else 0
  move : ∀ (x : Fin N → ℝ) (g : Space N) t i,
    Expr.Executes (RuntimeMotion.movementInput (x i) t (g i)) RuntimeMotion.movementExpr
      ((RuntimeMotion.movement x g t).value i) 5

theorem safe (v : Fin N → Fin d → ℂ) (hd : 0<d)
    (hp : ∑i,KSRankOne.atom (v i)=1) : Safe v where
  stencil := SeamlessKS.RuntimeSafety.safe v hd hp
  norm _ z := FrameArithmetic.norm_execution z
  zeroTest _ z := FrameArithmetic.zero_test z
  signValue _ q := FrameArithmetic.signProgram_value q
  normalize _ z hz := (FrameArithmetic.scalar_execution z hz).1
  sign _ q := FrameArithmetic.signProgram_execution q
  normal _ z hz := (FrameArithmetic.scalar_execution z hz).2.1
  reflect _ z hz := (FrameArithmetic.scalar_execution z hz).2.2
  multiply _ _ _ A B i j := RuntimeMatrix.product_entry_execution A B i j
  compressed _ R z t := RuntimeDirection.spectral_execution R z t
  compare p m := RuntimeMotion.choiceProgram_execution p m
  compareValue p m := RuntimeMotion.choiceProgram_value p m
  move x g t i := RuntimeMotion.movement_execution x g t i

end RadialKS.RuntimeSafety
