import MatrixSpencer.RealRAMMSCleanupScan
import MatrixSpencer.RealRAMJacobiRayleigh
import MatrixSpencer.MSManuscriptSupportedOwner

/-! Counted scalar implementation of the stored-support cleanup. The actual
matrix-dependent Jacobi count is computed by a bounded comparison loop;
rotations, Schur deletions, retained-label lookup and rectangular frame
multiplication are all charged. The supplied natural cap bounds that loop. -/
open Matrix
open scoped BigOperators
noncomputable section
namespace MatrixSpencer.RealRAM.MSCleanup
open JacobiIteration (Counted Mat)
open MSManuscriptSupportedOwner (Owner)
attribute [local instance] Classical.propDecidable
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
variable {N k : ℕ}

def multiply {a b c : ℕ} (A : Matrix (Fin a) (Fin b) ℝ)
    (B : Matrix (Fin b) (Fin c) ℝ) : Counted (Matrix (Fin a) (Fin c) ℝ) :=
  ⟨fun i j => (matrixMulCircuit a b c).eval (matrixInput A B) (i,j),
    (matrixMulCircuit a b c).cost+6*(a+b+c+1)^2⟩

@[simp] theorem multiply_value {a b c : ℕ} (A : Matrix (Fin a) (Fin b) ℝ)
    (B : Matrix (Fin b) (Fin c) ℝ) : (multiply A B).value=A*B := by
  ext i j
  exact matrixMulCircuit_eval A B i j

theorem multiply_cost {a b c : ℕ} (A : Matrix (Fin a) (Fin b) ℝ)
    (B : Matrix (Fin b) (Fin c) ℝ) : (multiply A B).cost≤12*(a+b+c+1)^3 := by
  have h:=matrixMulCircuit_cost_polynomial a b c
  have hp : (a+b+c+1)^2≤(a+b+c+1)^3 := Nat.pow_le_pow_right (by omega) (by omega)
  dsimp only [multiply]
  omega

def toleranceExpr : Expr (Fin 2) :=
  .div (.input 1) (.mul (.constant 16) (.add (.input 0) (.constant 1)))
@[simp] theorem tolerance_eval (k : ℕ) (δ : ℝ) :
    toleranceExpr.eval ![(k:ℝ),δ]=MSManuscriptCleanupParameters.tolerance k δ := by
  norm_num [toleranceExpr,Expr.eval,MSManuscriptCleanupParameters.tolerance]
theorem tolerance_execution (k : ℕ) (δ : ℝ) :
    Expr.Executes ![(k:ℝ),δ] toleranceExpr
      (MSManuscriptCleanupParameters.tolerance k δ) 7 := by
  have hv : toleranceExpr.Valid ![(k:ℝ),δ] := by
    simp only [toleranceExpr,Expr.Valid,Expr.eval]
    norm_num
    positivity
  have h:=Expr.executes_of_valid ![(k:ℝ),δ] toleranceExpr hv
  rw [tolerance_eval] at h
  exact h

def assembled (O : Owner N) (R U S : Mat O.dim) (ls : List (Fin O.dim)) : Owner N where
  dim := ls.length
  frame := (multiply O.frame (U.submatrix id (fun i : Fin ls.length => ls.get i))).value
  matrix := S.submatrix (fun i : Fin ls.length => ls.get i) (fun i : Fin ls.length => ls.get i)

def clean (O : Owner N) (δ : ℝ) (cap : ℕ) : Counted (Owner N) :=
  let τ:=toleranceExpr.eval ![(O.dim:ℝ),δ]
  let n:=JacobiRayleigh.budget O.matrix τ cap
  let j:=JacobiIteration.diagonalize O.matrix n.value
  let s:=MSCleanupScan.scan j.value.matrix δ O.dim
  let ls:=MSCleanupScan.labels j.value.matrix δ (List.finRange O.dim)
  let m:=multiply O.frame (j.value.basis.submatrix id (fun i : Fin ls.value.length => ls.value.get i))
  ⟨assembled O j.value.matrix j.value.basis s.value ls.value,
    n.cost+j.cost+s.cost+ls.cost+m.cost+30*(N+O.dim+1)^3+20⟩

/-- Explicit lookup lemma for the original retained-coordinate equivalence. -/
theorem equiv_value (G : Mat k) (δ : ℝ)
    (i : Fin (MSManuscriptCleanupCoordinates.count G δ)) :
    (MSManuscriptCleanupCoordinates.equiv G δ i).val=
      (MSManuscriptCleanupCoordinates.labels G δ).get i := rfl

theorem clean_value (O : Owner N) (δ : ℝ) (cap : ℕ)
    (hcap : KSJacobiIteration.denominator O.dim*KSJacobiStep.offDiagonalEnergy O.matrix/
      (MSManuscriptCleanupParameters.tolerance O.dim δ)^2≤cap) :
    (clean O δ cap).value=MSManuscriptSupportedOwner.clean O δ := by
  simp only [clean,tolerance_eval,JacobiRayleigh.budget_value O.matrix _ cap hcap]
  obtain ⟨hR,hU⟩:=JacobiIteration.diagonalize_actual O.matrix
    (KSJacobiIteration.iterationCount O.matrix (MSManuscriptCleanupParameters.tolerance O.dim δ))
  simp only [hR,hU,MSCleanupScan.scan_value,MSCleanupScan.labels_value]
  unfold assembled MSManuscriptSupportedOwner.clean
  simp only [multiply_value]
  congr 1

/-- The cleanup's full cost is polynomial even when every stored direction is
removed. Indexed list lookups are charged by their worst-case list length. -/
theorem clean_cost (O : Owner N) (δ : ℝ) (cap : ℕ) :
    (clean O δ cap).cost≤2000*(cap+1)*(N+O.dim+1)^5 := by
  let τ:=toleranceExpr.eval ![(O.dim:ℝ),δ]
  let n:=JacobiRayleigh.budget O.matrix τ cap
  let j:=JacobiIteration.diagonalize O.matrix n.value
  let ls:=MSCleanupScan.labels j.value.matrix δ (List.finRange O.dim)
  have hn : n.value≤cap := by
    dsimp only [n,JacobiRayleigh.budget]
    rw [JacobiRayleigh.ceilLoop_value]
    exact min_le_left _ _
  have hnC:=JacobiRayleigh.budget_cost O.matrix τ cap
  have hjC: j.cost≤510*(cap+1)*(O.dim+1)^3 :=
    (JacobiIteration.diagonalize_cost O.matrix n.value).trans (by gcongr)
  have hsC:=MSCleanupScan.scan_cost j.value.matrix δ O.dim
  have hlC : ls.cost=9*O.dim+1 := by
    simpa only [ls,List.length_finRange] using
      MSCleanupScan.labels_cost j.value.matrix δ (List.finRange O.dim)
  have hlen : ls.value.length≤O.dim := by
    rw [show ls.value=(List.finRange O.dim).filter (fun i=>decide (3*δ≤j.value.matrix i i)) from
      MSCleanupScan.labels_value _ _ _]
    exact (List.length_filter_le _ _).trans_eq List.length_finRange
  have hmC:=multiply_cost O.frame (j.value.basis.submatrix id
    (fun i : Fin ls.value.length => ls.value.get i))
  let t:=N+O.dim+1
  have ht : 1≤t := by dsimp [t];omega
  have hk : O.dim+1≤t := by dsimp [t];omega
  have hk' : O.dim≤t := by omega
  have hn1 : 1≤cap+1 := by omega
  have hp2 : t^2≤t^5 := Nat.pow_le_pow_right ht (by omega)
  have hp3 : t^3≤t^5 := Nat.pow_le_pow_right ht (by omega)
  have hp1 : t≤t^5 := by simpa only [pow_one] using Nat.pow_le_pow_right ht (show 1≤5 by omega)
  have hpow : 1≤t^5 := Nat.one_le_pow _ _ ht
  have hk25 : (O.dim+1)^2≤t^5 := (Nat.pow_le_pow_left hk 2).trans hp2
  have hnC' : n.cost≤20*t^5+8*cap+30 := by dsimp only [n]; omega
  have hjC' : j.cost≤510*(cap+1)*t^5 := hjC.trans
    (Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left hk 3).trans hp3))
  have hsC' : (MSCleanupScan.scan j.value.matrix δ O.dim).cost≤77*t^5 := by
    have hkk : O.dim*(O.dim+1)^4≤t^5 := by
      calc _≤t*t^4 := Nat.mul_le_mul hk' (Nat.pow_le_pow_left hk 4)
           _=t^5 := by ring
    have hk2 : O.dim^2≤t^5 := (Nat.pow_le_pow_left hk' 2).trans hp2
    nlinarith
  have hmC' : (multiply O.frame (j.value.basis.submatrix id
      (fun i : Fin ls.value.length => ls.value.get i))).cost≤96*t^5 := by
    have hside : N+O.dim+ls.value.length+1≤2*t := by dsimp [t];omega
    calc _≤12*(2*t)^3 := hmC.trans (by gcongr)
         _≤96*t^5 := by nlinarith
  change n.cost+j.cost+(MSCleanupScan.scan j.value.matrix δ O.dim).cost+ls.cost+
    (multiply O.frame (j.value.basis.submatrix id
      (fun i : Fin ls.value.length => ls.value.get i))).cost+30*t^3+20≤2000*(cap+1)*t^5
  have hcap : cap≤(cap+1)*t^5 := (Nat.le_succ cap).trans (by simpa using Nat.mul_le_mul_left (cap+1) hpow)
  have htp : t^5≤(cap+1)*t^5 := by simpa using Nat.mul_le_mul_right (t^5) hn1
  rw [hlC]
  nlinarith

end MatrixSpencer.RealRAM.MSCleanup
