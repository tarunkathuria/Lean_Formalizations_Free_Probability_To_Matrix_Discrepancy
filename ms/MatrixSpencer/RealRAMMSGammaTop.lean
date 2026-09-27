import MatrixSpencer.RealRAMMSResponse
import MatrixSpencer.MSManuscriptSupportedPaid

/-! Concrete top-response selection, paid cuts and physical-owner materialization.
The candidate is the actual finite Jacobi output on minus the response. Its
Rayleigh value and stopping comparison are real scalar computations. -/
open Matrix
open scoped BigOperators
noncomputable section
namespace MatrixSpencer.RealRAM.MSGammaTop
open JacobiIteration (Counted Mat)
open MSResponse (Space)
open MSManuscriptSupportedOwner (Owner)
attribute [local instance] Classical.propDecidable
set_option maxRecDepth 4096
variable {k N : ℕ}

def negativeExpr (ij : Fin k×Fin k) : Expr (Fin k×Fin k) :=
  .sub (.constant 0) (.input ij)
def negative (G : Mat k) : Counted (Mat k) :=
  ⟨fun i j=>(negativeExpr (i,j)).eval (JacobiIteration.entries G),6*k^2+1⟩
@[simp] theorem negative_value (G : Mat k) : (negative G).value= -G := by
  ext i j
  simp [negative,negativeExpr,Expr.eval,JacobiIteration.entries]

def rayleighExpr : Expr ((Fin k×Fin k) ⊕ Fin k) :=
  Expr.sumList (List.ofFn (fun i : Fin k => Expr.sumList (List.ofFn (fun j : Fin k =>
    .mul (.input (.inr i)) (.mul (.input (.inl (i,j))) (.input (.inr j)))))))
def rayleighInput (G : Mat k) (u : Space k) : ((Fin k×Fin k) ⊕ Fin k) → ℝ :=
  Sum.elim (JacobiIteration.entries G) (WithLp.ofLp u)

theorem rayleighExpr_eval (G : Mat k) (u : Space k) :
    rayleighExpr.eval (rayleighInput G u)=KSRayleighAccuracy.realRayleigh G u := by
  rw [KSRayleighAccuracy.realRayleigh_eq_quadratic]
  simp [rayleighExpr,Expr.eval_sumList,List.map_ofFn,List.sum_ofFn,Expr.eval,
    rayleighInput,JacobiIteration.entries,Matrix.mulVec,dotProduct,Finset.mul_sum,mul_assoc]

theorem rayleighExpr_valid (G : Mat k) (u : Space k) :
    rayleighExpr.Valid (rayleighInput G u) := by
  apply Expr.valid_sumList
  intro e he
  obtain ⟨i,rfl⟩:=List.mem_ofFn.mp he
  apply Expr.valid_sumList
  intro f hf
  obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hf
  simp [Expr.Valid]

theorem rayleighExpr_cost : (rayleighExpr (k:=k)).cost=6*k^2+2*k+1 := by
  simp [rayleighExpr,Expr.cost_sumList,List.map_ofFn,List.sum_ofFn,Expr.cost]
  ring

def rayleigh (G : Mat k) (u : Space k) : Counted ℝ :=
  ⟨rayleighExpr.eval (rayleighInput G u),(rayleighExpr (k:=k)).cost+10*(k+1)^2⟩
@[simp] theorem rayleigh_value (G : Mat k) (u : Space k) :
    (rayleigh G u).value=KSRayleighAccuracy.realRayleigh G u := rayleighExpr_eval G u

theorem rayleigh_execution (G : Mat k) (u : Space k) :
    Expr.Executes (rayleighInput G u) rayleighExpr
      (KSRayleighAccuracy.realRayleigh G u) (6*k^2+2*k+1) := by
  simpa only [rayleighExpr_eval,rayleighExpr_cost] using
    Expr.executes_of_valid _ _ (rayleighExpr_valid G u)

theorem rayleigh_cost (G : Mat k) (u : Space k) :
    (rayleigh G u).cost≤20*(k+1)^2 := by
  dsimp only [rayleigh]
  rw [rayleighExpr_cost]
  nlinarith

def toleranceExpr : Expr Unit := .div (.input ()) (.constant 64)
def thresholdExpr : Expr Unit := .div (.mul (.constant 15) (.input ())) (.constant 16)
@[simp] theorem tolerance_eval (t : ℝ) : toleranceExpr.eval (fun _=>t)=t/64 := by
  norm_num [toleranceExpr,Expr.eval]
@[simp] theorem threshold_eval (t : ℝ) : thresholdExpr.eval (fun _=>t)=15*t/16 := by
  norm_num [thresholdExpr,Expr.eval]

def top (G : Mat k) (t : ℝ) (cap : ℕ) (hk : 0<k) : Counted (Option (Space k)) :=
  let A:=negative G
  let u:=JacobiRayleigh.output A.value (toleranceExpr.eval (fun _=>t)) cap hk
  let q:=rayleigh G u.value
  ⟨if q.value≤thresholdExpr.eval (fun _=>t) then none else some u.value,
    A.cost+u.cost+q.cost+30⟩

theorem top_value (G : Mat k) (t : ℝ) (cap : ℕ) (hk : 0<k)
    (hcap : KSJacobiIteration.denominator k*KSJacobiStep.offDiagonalEnergy (-G)/(t/64)^2≤cap) :
    (top G t cap hk).value=
      if MSManuscriptGammaTop.stop G t hk then none else some (MSManuscriptGammaTop.vector G t hk) := by
  simp only [top,negative_value,tolerance_eval,JacobiRayleigh.output_value _ _ _ _ hcap,
    rayleigh_value,threshold_eval,MSManuscriptGammaTop.stop,MSManuscriptGammaTop.value,
    MSManuscriptGammaTop.vector,Bool.coe_iff_coe,decide_eq_true_eq]

theorem top_cost (G : Mat k) (t : ℝ) (cap : ℕ) (hk : 0<k) :
    (top G t cap hk).cost≤700*(cap+1)*(k+1)^3 := by
  have hu:=JacobiRayleigh.output_cost (negative G).value (toleranceExpr.eval (fun _=>t)) cap hk
  have hq:=rayleigh_cost G
    (JacobiRayleigh.output (negative G).value (toleranceExpr.eval (fun _=>t)) cap hk).value
  have hp2 : (k+1)^2≤(k+1)^3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hk2 : k^2≤(k+1)^3 := (Nat.pow_le_pow_left (Nat.le_succ k) 2).trans hp2
  have h1 : 1≤(k+1)^3 := Nat.one_le_pow _ _ (by omega)
  have hm : (k+1)^3≤(cap+1)*(k+1)^3 := by nlinarith
  dsimp only [top,negative]
  dsimp only [negative] at hu hq
  nlinarith

/-- Every call made by preparation uses a certified unit vector; replacing
its normalization by one is therefore an exact algebraic implementation. -/
def paid (O : Owner N) (α : ℝ) (u : Space O.dim) : Counted (Owner N) :=
  let s:=MSResponse.shave O.matrix α u
  ⟨{dim:=O.dim,frame:=O.frame,matrix:=s.value},s.cost+4*(N+O.dim+1)^2+3⟩

theorem paid_value (O : Owner N) (α : ℝ) (u : Space O.dim) (hu : ‖u‖=1) :
    (paid O α u).value=MSManuscriptSupportedOwner.paid O α (WithLp.ofLp u) := by
  simp only [paid,MSResponse.shave_value,MSManuscriptSupportedOwner.paid,
    MSManuscriptPaidStep.cut,MSManuscriptPaidStep.unitRank_of_norm_one u hu]

theorem paid_cost (O : Owner N) (α : ℝ) (u : Space O.dim) :
    (paid O α u).cost≤25*(N+O.dim+1)^2 := by
  have h:=MSResponse.shave_cost O.matrix α u
  have hd : (O.dim+1)^2≤(N+O.dim+1)^2 := Nat.pow_le_pow_left (by omega) _
  have h1 : 1≤(N+O.dim+1)^2 := Nat.one_le_pow _ _ (by omega)
  dsimp only [paid]
  omega

def physical (O : Owner N) : Counted (Mat N) :=
  let a:=MSCleanup.multiply O.frame O.matrix
  let b:=MSCleanup.multiply a.value O.frameᵀ
  ⟨b.value,a.cost+b.cost+4*N*O.dim+3⟩
@[simp] theorem physical_value (O : Owner N) : (physical O).value=O.physical := by
  simp only [physical,MSCleanup.multiply_value,MSManuscriptSupportedOwner.Owner.physical]

theorem physical_cost (O : Owner N) : (physical O).cost≤220*(N+O.dim+1)^3 := by
  have ha:=MSCleanup.multiply_cost O.frame O.matrix
  have hb:=MSCleanup.multiply_cost (MSCleanup.multiply O.frame O.matrix).value O.frameᵀ
  have ha' : N+O.dim+O.dim+1≤2*(N+O.dim+1) := by omega
  have hb' : N+O.dim+N+1≤2*(N+O.dim+1) := by omega
  have h1 : 1≤(N+O.dim+1)^3 := Nat.one_le_pow _ _ (by omega)
  have hprod : N*O.dim≤(N+O.dim+1)^3 := by
    have h:=Nat.mul_le_mul (show N≤N+O.dim+1 by omega) (show O.dim≤N+O.dim+1 by omega)
    nlinarith [Nat.zero_le ((N+O.dim+1)^2)]
  have ha2:=ha.trans (Nat.mul_le_mul_left 12 (Nat.pow_le_pow_left ha' 3))
  have hb2:=hb.trans (Nat.mul_le_mul_left 12 (Nat.pow_le_pow_left hb' 3))
  dsimp only [physical]
  nlinarith

end MatrixSpencer.RealRAM.MSGammaTop
