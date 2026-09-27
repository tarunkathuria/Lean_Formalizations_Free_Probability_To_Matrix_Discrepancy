import MatrixSpencer.KSEighthCountedMovement
import MatrixSpencer.KSEighthCountedCovariance

/-! Primitive scalar witnesses for the coordinate and stencil arithmetic
charged in the counted eighth pipeline. The square-root and division domains
are proved on the actual cube and positive controller parameters. -/
open Matrix Set
open scoped BigOperators
noncomputable section
namespace MatrixSpencer.KSEighthCountedScalarExecution
open RealRAM
variable {N m : ℕ}

def faceExpr : Expr (Fin 2) :=
  .add (.input 0) (.mul (.sqrt (.sub (.constant 1) (.mul (.input 0) (.input 0)))) (.input 1))

theorem square_le_one {a : ℝ} (ha : |a|≤1/8) : a*a≤1 := by
  have h := (abs_le.mp ha)
  nlinarith

theorem face_execution {x : Fin N → ℝ} (hx : x∈ksCube (1/8))
    (z : KSEighthFacePotential.Space x) (i : Fin N) :
    Expr.Executes ![x i,KSEighthLiveEnumeration.extend x z i] faceExpr
      ((KSEighthCountedHessian.face x z).value i) faceExpr.cost ∧ faceExpr.cost≤20 := by
  have hs := square_le_one (abs_le.mpr ⟨hx.1 i,hx.2 i⟩)
  have hv : faceExpr.Valid ![x i,KSEighthLiveEnumeration.extend x z i] := by
    simp [faceExpr,Expr.Valid,Expr.eval]
    linarith
  constructor
  · convert Expr.executes_of_valid _ faceExpr hv using 1 <;>
      simp [faceExpr,Expr.eval,KSEighthCountedHessian.face,pow_two]
  · norm_num [faceExpr,Expr.cost]

def physicalExpr : Expr (Fin 3) :=
  .mul (.mul (.sqrt (.sub (.constant 1) (.mul (.input 0) (.input 0)))) (.input 1))
    (.sqrt (.sub (.constant 1) (.mul (.input 2) (.input 2))))

theorem physical_execution {x : Fin N → ℝ} (hx : x∈ksCube (1/8))
    (Q : Matrix (Fin (KSEighthLiveEnumeration.count x)) (Fin (KSEighthLiveEnumeration.count x)) ℝ)
    (i j : Fin (KSEighthLiveEnumeration.count x)) :
    Expr.Executes ![KSEighthManuscriptMovement.livePoint x i,Q i j,KSEighthManuscriptMovement.livePoint x j]
      physicalExpr ((KSEighthCountedMovement.physical x Q).value i j) physicalExpr.cost ∧
      physicalExpr.cost≤25 := by
  have hi := square_le_one (abs_le.mpr ⟨hx.1 (KSEighthLiveEnumeration.liveEquiv x i),
    hx.2 (KSEighthLiveEnumeration.liveEquiv x i)⟩)
  have hj := square_le_one (abs_le.mpr ⟨hx.1 (KSEighthLiveEnumeration.liveEquiv x j),
    hx.2 (KSEighthLiveEnumeration.liveEquiv x j)⟩)
  have hv : physicalExpr.Valid ![KSEighthManuscriptMovement.livePoint x i,Q i j,
      KSEighthManuscriptMovement.livePoint x j] := by
    simp [physicalExpr,Expr.Valid,Expr.eval,KSEighthManuscriptMovement.livePoint]
    constructor <;> linarith
  constructor
  · convert Expr.executes_of_valid _ physicalExpr hv using 1 <;>
      simp [physicalExpr,Expr.eval,KSEighthCountedMovement.physical,pow_two]
  · norm_num [physicalExpr,Expr.cost]

def unsignedExpr : Expr (Fin 3) := .mul (.sqrt (.mul (.input 0) (.input 1))) (.input 2)

theorem unsigned_execution (P : Matrix (Fin m) (Fin m) ℝ) (hP : P.PosSemidef) (j i : Fin m) :
    Expr.Executes ![(m:ℝ),(KSEighthCountedMovement.factor P).value.1 j,
      (KSEighthCountedMovement.factor P).value.2 j i] unsignedExpr
      (KSEighthManuscriptSampler.unsigned P j i) unsignedExpr.cost ∧ unsignedExpr.cost≤10 := by
  have hv : unsignedExpr.Valid ![(m:ℝ),(KSEighthCountedMovement.factor P).value.1 j,
      (KSEighthCountedMovement.factor P).value.2 j i] := by
    simp only [unsignedExpr,Expr.Valid,Expr.eval,Matrix.cons_val,Matrix.cons_val_zero,
      Matrix.cons_val_one,KSEighthCountedMovement.factor_pivot]
    exact ⟨⟨⟨trivial,trivial⟩,mul_nonneg (Nat.cast_nonneg m) (KSEighthManuscriptLDL.pivot_nonneg hP j)⟩,trivial⟩
  constructor
  · convert Expr.executes_of_valid _ unsignedExpr hv using 1 <;>
      simp [unsignedExpr,Expr.eval,KSEighthCountedMovement.factor_pivot,
        KSEighthCountedMovement.factor_column,KSEighthManuscriptSampler.unsigned]
  · norm_num [unsignedExpr,Expr.cost]

def stencilExpr : Expr (Fin 5) :=
  .div (.add (.sub (.sub (.input 0) (.input 1)) (.input 2)) (.input 3))
    (.mul (.constant 4) (.mul (.input 4) (.input 4)))

theorem stencil_execution (pp pm mp mm t : ℝ) (ht : 0<t) :
    Expr.Executes ![pp,pm,mp,mm,t] stencilExpr ((pp-pm-mp+mm)/(4*t^2)) stencilExpr.cost ∧
      stencilExpr.cost≤30 := by
  have hv : stencilExpr.Valid ![pp,pm,mp,mm,t] := by
    simp [stencilExpr,Expr.Valid,Expr.eval,ne_of_gt ht]
  constructor
  · convert Expr.executes_of_valid _ stencilExpr hv using 1 <;> simp [stencilExpr,Expr.eval,pow_two]
  · norm_num [stencilExpr,Expr.cost]

def proposalExpr : Expr (Fin 3) := .add (.input 0) (.mul (.input 1) (.input 2))

theorem proposal_execution (x h u : ℝ) :
    Expr.Executes ![x,h,u] proposalExpr (x+h*u) proposalExpr.cost ∧ proposalExpr.cost≤10 := by
  exact ⟨Expr.executes_of_valid _ _ (by simp [proposalExpr,Expr.Valid]),by norm_num [proposalExpr,Expr.cost]⟩

end MatrixSpencer.KSEighthCountedScalarExecution
