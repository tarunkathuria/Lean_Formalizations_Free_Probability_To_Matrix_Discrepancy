import MatrixSpencer.RealRAMMSSampling
import SimpleMS.CountedHighProjection
import SimpleMS.ProjectionComputation
import MatrixSpencer.MSManuscriptNumericalCoordinateStep
import MatrixSpencer.MSManuscriptOwnerAdvance

/-! Computed frozen-label constraints, guarded scalar short scans and the
matched covariance withdrawal, including both rectangular matrix products. -/
open Matrix
open scoped BigOperators
noncomputable section
namespace MatrixSpencer.RealRAM.MSCovariance
open JacobiIteration (Counted Mat)
open MSResponse (Space)
open MSManuscriptSupportedOwner (Owner)
attribute [local instance] Classical.propDecidable
variable {N : ℕ}
set_option maxRecDepth 4096

def frozen (x : Space N) : List (Fin N) → Counted (List (Fin N))
  | []=>⟨[],1⟩
  | i::is=>let t:=frozen x is
           ⟨if IsSign (x i) then i::t.value else t.value,t.cost+12⟩

theorem frozen_value (x : Space N) (is : List (Fin N)) :
    (frozen x is).value=is.filter (fun i=>decide (i∈frozenCoordinates x)) := by
  induction is with
  | nil=>rfl
  | cons i is ih=>simp only [frozen,ih,List.filter_cons,decide_eq_true_eq,mem_frozenCoordinates]

theorem frozen_cost (x : Space N) (is : List (Fin N)) :
    (frozen x is).cost=12*is.length+1 := by
  induction is with
  | nil=>rfl
  | cons i is ih=>simp [frozen,ih];omega

def constraints (x : Space N) : Counted (List (Fin N → ℝ)) :=
  let f:=frozen x (List.finRange N)
  ⟨f.value.map (fun i=>(MSCleanupScan.coordinate i).value)++[WithLp.ofLp x],
    f.cost+f.value.length*(4*N+5)+6*N+5⟩

theorem constraints_value (x : Space N) :
    (constraints x).value=MSManuscriptNumericalEpochShort.constraints (frozenCoordinates x) x := by
  simp only [constraints,frozen_value,MSCleanupScan.coordinate_value,
    MSManuscriptNumericalEpochShort.constraints,MSManuscriptNumericalEpochShort.frozenLabels]

theorem constraints_length (x : Space N) : (constraints x).value.length≤N+1 := by
  rw [constraints_value,MSManuscriptNumericalEpochShort.length_constraints]
  have hf : (frozenCoordinates x).card≤N := by simpa using Finset.card_le_univ (frozenCoordinates x)
  omega

theorem constraints_cost (x : Space N) : (constraints x).cost≤30*(N+1)^2 := by
  have hf:=frozen_cost x (List.finRange N)
  simp only [List.length_finRange] at hf
  have hl : (frozen x (List.finRange N)).value.length≤N := by
    rw [frozen_value]
    exact (List.length_filter_le _ _).trans_eq List.length_finRange
  dsimp only [constraints]
  nlinarith

def scan (C : Mat N) : List (Fin N → ℝ) → Counted (Mat N)
  | []=>⟨C,1⟩
  | u::us=>let s:=MSCleanupScan.short C u
           let t:=scan s.value us
           ⟨t.value,s.cost+t.cost+3⟩

theorem scan_value (C : Mat N) (us : List (Fin N → ℝ)) :
    (scan C us).value=MSManuscriptNumericalEpochShort.applyConstraints C us := by
  induction us generalizing C with
  | nil=>rfl
  | cons u us ih=>simp only [scan,MSCleanupScan.short_value,ih,
    MSManuscriptNumericalEpochShort.applyConstraints]

theorem scan_cost (C : Mat N) (us : List (Fin N → ℝ)) :
    (scan C us).cost≤60*us.length*(N+1)^4+1 := by
  induction us generalizing C with
  | nil=>simp [scan]
  | cons u us ih=>
    have hs:=MSCleanupScan.short_cost C u
    have ht:=ih (MSCleanupScan.short C u).value
    have h1 : 1≤(N+1)^4 := Nat.one_le_pow _ _ (by omega)
    dsimp only [scan,List.length_cons]
    nlinarith

def covariance (C : Mat N) (x : Space N) : Counted (Mat N) :=
  let high := SimpleMS.CountedHighProjection.value C
  let cs := constraints x
  let q := scan high.value cs.value
  ⟨(1/2:ℝ) • q.value,high.cost+cs.cost+q.cost+4*N^2+3⟩

theorem covariance_value (C : Mat N) (x : Space N) :
    (covariance C x).value=MSManuscriptNumericalCoordinateStep.covariance C x := by
  simp only [covariance,scan_value,constraints_value,SimpleMS.CountedHighProjection.value_value]
  exact (SimpleMS.ProjectionComputation.flatCovariance_eq_half_epoch_high C (frozenCoordinates x) x).symm

theorem covariance_cost (C : Mat N) (x : Space N) :
    (covariance C x).cost≤1000*(N+1)^5 := by
  have hh := SimpleMS.CountedHighProjection.value_cost C
  have hc:=constraints_cost x
  have hs:=scan_cost (SimpleMS.CountedHighProjection.value C).value (constraints x).value
  have hl:=constraints_length x
  have hs' : (scan (SimpleMS.CountedHighProjection.value C).value (constraints x).value).cost≤60*(N+1)^5+1 := by
    calc _≤60*(N+1)*(N+1)^4+1 := hs.trans (by gcongr)
         _=_ := by ring
  have hp : (N+1)^2≤(N+1)^5 := Nat.pow_le_pow_right (by omega) (by omega)
  have h3 : (N+1)^3≤(N+1)^5 := Nat.pow_le_pow_right (by omega) (by omega)
  have h2 : N^2≤(N+1)^5 := (Nat.pow_le_pow_left (by omega) 2).trans hp
  have h1 : 1≤(N+1)^5 := Nat.one_le_pow _ _ (by omega)
  dsimp only [covariance]
  omega

def withdrawExpr : Expr (Fin 3) :=
  .sub (.input 0) (.mul (.mul (.input 2) (.input 2)) (.input 1))
@[simp] theorem withdraw_eval (a b h : ℝ) : withdrawExpr.eval ![a,b,h]=a-h^2*b := by
  norm_num [withdrawExpr,Expr.eval,Matrix.cons_val_two,pow_two]

def advance (O : Owner N) (Q : Mat N) (h : ℝ) : Counted (Owner N) :=
  let a:=MSCleanup.multiply O.frameᵀ Q
  let b:=MSCleanup.multiply a.value O.frame
  ⟨{dim:=O.dim,frame:=O.frame,
    matrix:=fun i j=>withdrawExpr.eval ![O.matrix i j,b.value i j,h]},
    a.cost+b.cost+20*(N+O.dim+1)^2+3⟩

theorem advance_value (O : Owner N) (Q : Mat N) (h : ℝ) :
    (advance O Q h).value=MSManuscriptOwnerAdvance.advance O Q h := by
  simp only [advance,MSCleanup.multiply_value,withdraw_eval,
    MSManuscriptOwnerAdvance.advance,MSManuscriptSupportedMovement.reduced]
  rfl

theorem advance_cost (O : Owner N) (Q : Mat N) (h : ℝ) :
    (advance O Q h).cost≤220*(N+O.dim+1)^3 := by
  have ha:=MSCleanup.multiply_cost O.frameᵀ Q
  have hb:=MSCleanup.multiply_cost (MSCleanup.multiply O.frameᵀ Q).value O.frame
  have ha' : O.dim+N+N+1≤2*(N+O.dim+1) := by omega
  have hb' : O.dim+N+O.dim+1≤2*(N+O.dim+1) := by omega
  have ha2:=ha.trans (Nat.mul_le_mul_left 12 (Nat.pow_le_pow_left ha' 3))
  have hb2:=hb.trans (Nat.mul_le_mul_left 12 (Nat.pow_le_pow_left hb' 3))
  have hp : (N+O.dim+1)^2≤(N+O.dim+1)^3 := Nat.pow_le_pow_right (by omega) (by omega)
  have h1 : 1≤(N+O.dim+1)^3 := Nat.one_le_pow _ _ (by omega)
  dsimp only [advance]
  nlinarith

theorem withdraw_execution (a b h : ℝ) :
    Expr.Executes ![a,b,h] withdrawExpr (a-h^2*b) 7 := by
  have hv : withdrawExpr.Valid ![a,b,h] := by simp [withdrawExpr,Expr.Valid]
  have he:=Expr.executes_of_valid _ _ hv
  rw [withdraw_eval] at he
  exact he

end MatrixSpencer.RealRAM.MSCovariance
