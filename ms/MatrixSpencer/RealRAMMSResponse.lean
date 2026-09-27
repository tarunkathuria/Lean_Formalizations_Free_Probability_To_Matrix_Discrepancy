import MatrixSpencer.RealRAMMSCleanup
import MatrixSpencer.MSManuscriptGammaMatrix

/-! Counted finite-difference reconstruction and top-response direction. Value
queries arrive as counted evaluations on already formed input matrices; this
module charges covariance probes, polarization, scalar arithmetic and actual
finite Jacobi selection. The query implementation is supplied separately. -/
open Matrix
open scoped BigOperators
noncomputable section
namespace MatrixSpencer.RealRAM.MSResponse
open JacobiIteration (Counted Mat)
attribute [local instance] Classical.propDecidable
set_option maxRecDepth 4096
variable {k : ℕ}
abbrev Space (k : ℕ) := EuclideanSpace ℝ (Fin k)

abbrev ShaveInput (k : ℕ) := (Fin k×Fin k) ⊕ (Fin k ⊕ Unit)
def shaveInput (C : Mat k) (u : Space k) (s : ℝ) : ShaveInput k → ℝ :=
  Sum.elim (fun ij=>C ij.1 ij.2) (Sum.elim (WithLp.ofLp u) (fun _=>s))
def shaveExpr (ij : Fin k×Fin k) : Expr (ShaveInput k) :=
  .sub (.input (.inl ij)) (.mul (.input (.inr (.inr ())))
    (.mul (.input (.inr (.inl ij.1))) (.input (.inr (.inl ij.2)))))
def shaveCircuit (k : ℕ) : Circuit (ShaveInput k) (Fin k×Fin k) := ⟨shaveExpr⟩
def shave (C : Mat k) (s : ℝ) (u : Space k) : Counted (Mat k) :=
  ⟨fun i j=>(shaveCircuit k).eval (shaveInput C u s) (i,j),
    (shaveCircuit k).cost+10*(k+1)^2⟩
@[simp] theorem shave_value (C : Mat k) (s : ℝ) (u : Space k) :
    (shave C s u).value=C-s • realRankOne (WithLp.ofLp u) := by
  ext i j
  simp [shave,shaveCircuit,Circuit.eval,shaveExpr,shaveInput,Expr.eval,
    realRankOne,Matrix.vecMulVec_apply,Matrix.smul_apply,smul_eq_mul]
theorem shave_execution (C : Mat k) (s : ℝ) (u : Space k) (ij : Fin k×Fin k) :
    Expr.Executes (shaveInput C u s) (shaveExpr ij)
      ((C-s • realRankOne (WithLp.ofLp u)) ij.1 ij.2) 7 := by
  have hv : (shaveExpr ij).Valid (shaveInput C u s) := by simp [shaveExpr,Expr.Valid]
  simpa [shaveExpr,Expr.eval,Expr.cost,shaveInput,realRankOne,Matrix.vecMulVec_apply,
    Matrix.smul_apply,smul_eq_mul] using Expr.executes_of_valid _ _ hv
@[simp] theorem shave_cost (C : Mat k) (s : ℝ) (u : Space k) :
    (shave C s u).cost≤18*(k+1)^2 := by
  simp [shave,shaveCircuit,Circuit.cost,shaveExpr,Expr.cost]
  nlinarith

def slopeExpr : Expr (Fin 3) := .div (.sub (.input 0) (.input 1)) (.input 2)
def probe (q : Mat k → Counted ℝ) (C : Mat k) (s : ℝ) (u : Space k) : Counted ℝ :=
  let c0:=shave C 0 u
  let cs:=shave C s u
  let r0:=q c0.value
  let rs:=q cs.value
  ⟨slopeExpr.eval ![r0.value,rs.value,s],c0.cost+cs.cost+r0.cost+rs.cost+10⟩

theorem probe_value (q : Mat k → Counted ℝ) (C : Mat k) (s : ℝ) (u : Space k) :
    (probe q C s u).value=MSManuscriptGammaDifference.negativeSlope
      (fun a=>(q (C-a • realRankOne (WithLp.ofLp u))).value) s := by
  simp [probe,shave_value,slopeExpr,Expr.eval,MSManuscriptGammaDifference.negativeSlope]

theorem slope_execution (x y s : ℝ) (hs : s≠0) :
    Expr.Executes ![x,y,s] slopeExpr ((x-y)/s) 5 := by
  have hv : slopeExpr.Valid ![x,y,s] := by simp [slopeExpr,Expr.Valid,Expr.eval,hs]
  simpa [slopeExpr,Expr.eval,Expr.cost] using Expr.executes_of_valid _ _ hv

theorem probe_cost (q : Mat k → Counted ℝ) (C : Mat k) (s : ℝ) (u : Space k)
    (Q : ℕ) (h0 : (q C).cost≤Q)
    (hs : (q (C-s • realRankOne (WithLp.ofLp u))).cost≤Q) :
    (probe q C s u).cost≤2*Q+46*(k+1)^2 := by
  have hc0:=shave_cost C 0 u
  have hcs:=shave_cost C s u
  dsimp only [probe]
  simp only [shave_value,zero_smul,sub_zero]
  have h1 : 1≤(k+1)^2 := Nat.one_le_pow _ _ (by omega)
  omega

/-- Basis/mixed-vector construction uses only constants, comparisons and
sqrt(2). The worst case charge includes all k coordinate stores. -/
def basis (i : Fin k) : Counted (Space k) :=
  ⟨WithLp.toLp 2 (fun a=>if a=i then 1 else 0),4*k+2⟩
def mixed (i j : Fin k) : Counted (Space k) :=
  ⟨WithLp.toLp 2 (fun a=>(1/Real.sqrt 2)*((if a=i then 1 else 0)+(if a=j then 1 else 0))),12*k+10⟩
@[simp] theorem basis_value (i : Fin k) : (basis i).value=MSManuscriptGammaMatrix.basis i := by
  ext a
  simp [basis,MSManuscriptGammaMatrix.basis,EuclideanSpace.single_apply]
@[simp] theorem mixed_value (i j : Fin k) : (mixed i j).value=MSManuscriptGammaMatrix.mixed i j := by
  ext a
  simp [mixed,MSManuscriptGammaMatrix.mixed,MSManuscriptGammaMatrix.basis,EuclideanSpace.single_apply]

def reconstructEntry (q : Space k → Counted ℝ) (i j : Fin k) : Counted ℝ :=
  if i=j then
    let u:=basis i
    let r:=q u.value
    ⟨r.value,u.cost+r.cost+3⟩
  else
    let u:=mixed i j
    let v:=basis i
    let w:=basis j
    let a:=q u.value
    let b:=q v.value
    let c:=q w.value
    ⟨a.value-(b.value+c.value)/2,u.cost+v.cost+w.cost+a.cost+b.cost+c.cost+10⟩

theorem reconstructEntry_value (q : Space k → Counted ℝ) (i j : Fin k) :
    (reconstructEntry q i j).value=
      MSManuscriptGammaMatrix.reconstruct (fun u=>(q u).value) i j := by
  simp only [reconstructEntry,MSManuscriptGammaMatrix.reconstruct]
  split_ifs <;> simp only [basis_value,mixed_value]

theorem reconstructEntry_cost (q : Space k → Counted ℝ) (i j : Fin k) (Q : ℕ)
    (hq : ∀u,‖u‖=1→(q u).cost≤Q) :
    (reconstructEntry q i j).cost≤3*Q+30*(k+1) := by
  have hi:=hq _ (MSManuscriptGammaMatrix.basis_norm i)
  have hj:=hq _ (MSManuscriptGammaMatrix.basis_norm j)
  unfold reconstructEntry
  split_ifs with hij
  · simp only [basis_value]
    dsimp only [basis]
    omega
  · have hm:=hq _ (MSManuscriptGammaMatrix.mixed_norm i j hij)
    simp only [basis_value,mixed_value]
    dsimp only [basis,mixed]
    omega

def reconstruct (q : Space k → Counted ℝ) : Counted (Mat k) :=
  ⟨fun i j=>(reconstructEntry q i j).value,
    (∑i,∑j,(reconstructEntry q i j).cost)+10*(k+1)^2⟩
theorem reconstruct_value (q : Space k → Counted ℝ) :
    (reconstruct q).value=MSManuscriptGammaMatrix.reconstruct (fun u=>(q u).value) := by
  ext i j
  exact reconstructEntry_value q i j

theorem reconstruct_cost (q : Space k → Counted ℝ) (Q : ℕ)
    (hq : ∀u,‖u‖=1→(q u).cost≤Q) :
    (reconstruct q).cost≤3*k^2*Q+40*(k+1)^3 := by
  have h:=Finset.sum_le_sum (fun i (_ : i∈Finset.univ)=>
    Finset.sum_le_sum (fun j (_ : j∈Finset.univ)=>reconstructEntry_cost q i j Q hq))
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at h
  dsimp only [reconstruct]
  nlinarith

end MatrixSpencer.RealRAM.MSResponse
