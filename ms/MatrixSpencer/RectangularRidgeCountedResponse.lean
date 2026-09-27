import MatrixSpencer.RectangularRidgeSDPSetup
import MatrixSpencer.RectangularRidgeResponseScalars
import MatrixSpencer.RectangularRidgeSolverPreparation
import MatrixSpencer.RealRAMMSOwnerReport
import MatrixSpencer.RealRAMMSResponse

/-! Actual counted finite-value response reconstruction. All stored-family
mixing, covariance shaves, polarization, and literal SDP array construction
are charged. The numerical scalars come from their explicit comparison scan
and safe real expressions. -/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.RectangularRidgeCountedResponse
open RealRAM
open RealRAM.JacobiIteration (Counted Mat)
open RectangularRidgePreparationData MSManuscriptSupportedOwner
open RectangularRidgeNumericalOptimizerFloor RectangularRidgeNumericalParameters
variable {N k d : ℕ} [Nonempty (Fin d)]
local instance ridgeCountedResponseCStar : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
set_option maxHeartbeats 800000

def symmetrizeExpr (i j : Fin k) : Expr (Fin k×Fin k) :=
  .div (.add (.input (i,j)) (.input (j,i))) (.constant 2)

theorem symmetrizeExpr_eval (C : Mat k) (i j : Fin k) :
    (symmetrizeExpr i j).eval (fun p=>C p.1 p.2)=
      (selfAdjointPart ℝ C : Mat k) i j := by
  simp [symmetrizeExpr,Expr.eval,selfAdjointPart_apply_coe,Matrix.add_apply,
    Matrix.smul_apply,Matrix.star_apply,smul_eq_mul,invOf_eq_inv,div_eq_mul_inv,mul_comm]

def symmetrize (C : Mat k) : Counted (selfAdjoint (Mat k)) :=
  ⟨selfAdjointPart ℝ C,∑i:Fin k,∑j:Fin k,((symmetrizeExpr i j).cost+1)⟩

theorem symmetrize_execution (C : Mat k) (i j : Fin k) :
    Expr.Executes (fun p=>C p.1 p.2) (symmetrizeExpr i j)
      (((symmetrize C).value : Mat k) i j) 5 := by
  have hv : (symmetrizeExpr i j).Valid (fun p=>C p.1 p.2) := by
    norm_num [symmetrizeExpr,Expr.Valid,Expr.eval]
  have hh:=Expr.executes_of_valid _ _ hv
  simpa only [symmetrizeExpr_eval] using hh

theorem symmetrize_cost (C : Mat k) : (symmetrize C).cost=6*k^2 := by
  simp [symmetrize,symmetrizeExpr,Expr.cost,pow_two,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]

private theorem symmetrize_shave (C : selfAdjoint (Mat k)) (u : MSResponse.Space k) (s : ℝ) :
    selfAdjointPart ℝ ((C:Mat k)-s • realRankOne (WithLp.ofLp u))=
      C-s • hermitianRankOne (WithLp.ofLp u) := by
  have h : IsSelfAdjoint ((C:Mat k)-s • realRankOne (WithLp.ofLp u)) :=
    (C-s • hermitianRankOne (WithLp.ofLp u)).property
  exact h.selfAdjointPart_apply ℝ

def query (S : RectangularRidgeConvexValue.PolynomialSolver) (m : ℕ) (hm : 1≤m)
    (a : Fin d) (H : Matrix (Fin d) (Fin d) ℂ) (A : Fin k→Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀i,(A i).IsHermitian) (θ ν : ℝ) (C : Mat k) : Counted ℝ :=
  let c:=symmetrize C
  let r:=RealRAM.RectangularRidgeSDPEntries.report S m hm a H A hA c.value θ ν
  ⟨r.value,c.cost+r.cost⟩

theorem query_value (S : RectangularRidgeConvexValue.PolynomialSolver) (m : ℕ) (hm : 1≤m)
    (a : Fin d) (H : Matrix (Fin d) (Fin d) ℂ) (A : Fin k→Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀i,(A i).IsHermitian) (θ ν : ℝ) (C : Mat k) :
    (query S m hm a H A hA θ ν C).value=
      RectangularRidgeSymmetricQueries.report S.solver m hm a H A hA (selfAdjointPart ℝ C) θ (1/d) ν :=
  RealRAM.RectangularRidgeSDPEntries.report_value S m hm a H A hA _ θ ν

private theorem probe_value (S : RectangularRidgeConvexValue.PolynomialSolver) (m : ℕ) (hm : 1≤m)
    (a : Fin d) (H : Matrix (Fin d) (Fin d) ℂ) (A : Fin k→Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀i,(A i).IsHermitian) (θ ν s : ℝ) (C : selfAdjoint (Mat k)) (u : MSResponse.Space k) :
    (MSResponse.probe (query S m hm a H A hA θ ν) C s u).value=
      RectangularRidgeSolverGamma.probe S.solver m hm a H A hA C θ (1/d) s ν u := by
  rw [MSResponse.probe_value]
  simp only [query_value,symmetrize_shave]
  rfl

def response (S : RectangularRidgeConvexValue.PolynomialSolver) (a : Fin d)
    (P : Parameters N d) (hP : P.Valid) (O : Owner N) : Counted (Mat O.dim) :=
  let fam:=MSOwnerReport.family P.atoms O.frame
  let hfam : ∀i,(fam.value i).IsHermitian := by
    rw [MSOwnerReport.family_value]
    exact mixFamily_isHermitian _ _ hP.1
  let t:=RectangularRidgeResponseScalars.compute N d
  let c:=symmetrize O.matrix
  let q:=query S (depth P) (RectangularRidgeTuning.depth_positive N d P.count_pos)
    a P.center fam.value hfam t.value.weight t.value.accuracy
  let r:=MSResponse.reconstruct (MSResponse.probe q c.value t.value.spacing)
  ⟨r.value,fam.cost+t.cost+c.cost+r.cost+5⟩

theorem response_value (S : RectangularRidgeConvexValue.PolynomialSolver) (a : Fin d)
    (P : Parameters N d) (hP : P.Valid) (O : Owner N) :
    (response S a P hP O).value=RectangularRidgeSolverPreparation.value S.solver a P hP O := by
  simp only [response,MSResponse.reconstruct_value]
  simp_rw [probe_value]
  simp only [MSOwnerReport.family_value,
    RectangularRidgeResponseScalars.compute_value P.count_pos P.rectangular]
  rfl

def valueInverse (N d : ℕ) : ℕ := 2^346*(d+N+2)^64
def programSize (d : ℕ) : ℕ := 16*(2*d+3)*(d+4)*d^4+(d+4)*d^2+2
def queryBudget (S : RectangularRidgeConvexValue.PolynomialSolver) (N d : ℕ) : ℕ :=
  6*N^2+1000000*(N+2*d+2)^11+S.coefficient*(programSize d+valueInverse N d+1)^S.degree

theorem accuracy_inverse (N d : ℕ) : (valueAccuracy (size d N))⁻¹=(valueInverse N d:ℝ) := by
  simp only [valueAccuracy,small,big,size,valueInverse,one_div,inv_inv,
    Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_add]

private theorem query_cost (S : RectangularRidgeConvexValue.PolynomialSolver) (a : Fin d)
    (P : Parameters N d) (hP : P.Valid) (A : Fin k→Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀i,(A i).IsHermitian) (hk : k≤N) (C : Mat k) :
    (query S (depth P) (RectangularRidgeTuning.depth_positive N d P.count_pos)
      a P.center A hA (theta P) (valueAccuracy (size d N)) C).cost≤queryBudget S N d := by
  have hr:=RealRAM.RectangularRidgeSDPEntries.primitive_report_cost_le S P.count_pos
    a P.center A hA (selfAdjointPart ℝ C) (theta P)
    (small_pos (by linarith [size_one_le P]) 346 64) (le_of_eq (accuracy_inverse N d))
  have hc:=symmetrize_cost C
  simp only [Fintype.card_fin] at hr
  change (symmetrize C).cost+_≤_
  rw [hc]
  have hm : 1000000*(k+2*d+2)^11≤1000000*(N+2*d+2)^11 := by gcongr
  have hk2 : 6*k^2≤6*N^2 := by gcongr
  dsimp [queryBudget,programSize]
  dsimp only [depth,symmetrize,valueAccuracy] at *
  omega

def responseBudget (S : RectangularRidgeConvexValue.PolynomialSolver) (N d : ℕ) : ℕ :=
  8*d+900+6*N^2*queryBudget S N d+2000*(2*N+d+2)^4

theorem response_cost (S : RectangularRidgeConvexValue.PolynomialSolver) (a : Fin d)
    (P : Parameters N d) (hP : P.Valid) (O : Owner N) (hO : State O) :
    (response S a P hP O).cost≤responseBudget S N d := by
  let fam:=MSOwnerReport.family P.atoms O.frame
  let hfam : ∀i,(fam.value i).IsHermitian := by rw [MSOwnerReport.family_value];exact mixFamily_isHermitian _ _ hP.1
  let t:=RectangularRidgeResponseScalars.compute N d
  let c:=symmetrize O.matrix
  let q:=query S (depth P) (RectangularRidgeTuning.depth_positive N d P.count_pos)
    a P.center fam.value hfam t.value.weight t.value.accuracy
  have hq : ∀C,(q C).cost≤queryBudget S N d := by
    intro C
    dsimp [q,t]
    rw [RectangularRidgeResponseScalars.compute_value P.count_pos P.rectangular]
    exact query_cost S a P hP fam.value hfam hO.2.2 C
  have hp : ∀u,‖u‖=1→(MSResponse.probe q c.value t.value.spacing u).cost≤
      2*queryBudget S N d+46*(O.dim+1)^2 := fun u _=>MSResponse.probe_cost _ _ _ _ _ (hq _) (hq _)
  have hr:=MSResponse.reconstruct_cost (MSResponse.probe q c.value t.value.spacing) _ hp
  have ht:=RectangularRidgeResponseScalars.compute_cost (d:=d) P.count_pos
  have hc:=symmetrize_cost O.matrix
  have hf:=MSOwnerReport.family_cost P.atoms O.frame
  let B:=2*N+d+2
  have hdim:=hO.2.2
  have hB : 1≤B := by dsimp [B];omega
  have hfamily : fam.cost≤20*B^4 := by
    calc _=O.dim*d*d*(8*N+4)+1 := hf
         _≤B*B*B*(12*B)+1 := by gcongr <;> dsimp [B] <;> omega
         _≤20*B^4 := by nlinarith [one_le_pow₀ hB (n:=4)]
  have hp2 : O.dim^2*(O.dim+1)^2≤B^4 := by
    calc _≤B^2*B^2 := by gcongr <;> dsimp [B] <;> omega
         _=_ := by ring
  have hp3 : (O.dim+1)^3≤B^4 :=
    (Nat.pow_le_pow_left (by dsimp [B];omega) 3).trans (Nat.pow_le_pow_right hB (by omega))
  have hd2 : O.dim^2≤N^2 := Nat.pow_le_pow_left hdim 2
  have hmul:=Nat.mul_le_mul_right (6*queryBudget S N d) hd2
  change fam.cost+t.cost+c.cost+(MSResponse.reconstruct (MSResponse.probe q c.value t.value.spacing)).cost+5≤_
  dsimp [responseBudget]
  dsimp [c] at *
  rw [hc]
  have h1:=one_le_pow₀ hB (n:=4)
  have hn2 : N^2≤B^4 := (Nat.pow_le_pow_left (by dsimp [B];omega) 2).trans
    (Nat.pow_le_pow_right hB (by omega))
  dsimp only [t] at *
  change _≤8*d+900+6*N^2*queryBudget S N d+2000*B^4
  nlinarith

end MatrixSpencer.RectangularRidgeCountedResponse
