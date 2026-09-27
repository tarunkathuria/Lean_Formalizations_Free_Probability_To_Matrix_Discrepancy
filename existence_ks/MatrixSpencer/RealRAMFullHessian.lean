import MatrixSpencer.RealRAMJacobiIteration
import MatrixSpencer.KSFullManuscriptHessian

/-!
# Counted primitive evaluation of the actual full-cube Hessian stencil

Every query point, scalar stencil combination, and weighted matrix entry is
evaluated by a scalar circuit. The counted report callback is explicit and
its cost is included at every call. The actual report implementation and its
uniform domain-dependent cost bound belong to the value-query layer.
-/

open Matrix
open scoped BigOperators
noncomputable section
namespace MatrixSpencer.RealRAM.FullHessian
open JacobiIteration (Counted)
open KSNumericalHessian (Space coordinate)
attribute [local instance] Classical.propDecidable
variable {m : ℕ}

def pointCircuit (i j : Fin m) (a b : ℚ) : Circuit Unit (Fin m) where
  output k := .mul (.input ())
    (.add (.constant (if k = i then a else 0)) (.constant (if k = j then b else 0)))

def point (i j : Fin m) (a b : ℚ) (t : ℝ) : Counted (Space m) :=
  ⟨WithLp.toLp 2 ((pointCircuit i j a b).eval (fun _ => t)),
    (pointCircuit i j a b).cost+8*m+1⟩

theorem point_value (i j : Fin m) (a b : ℚ) (t : ℝ) :
    (point i j a b t).value = t • ((a : ℝ) • coordinate i+(b : ℝ) • coordinate j) := by
  ext k
  simp [point,pointCircuit,Circuit.eval,Expr.eval,coordinate,Pi.single_apply]
  split_ifs <;> simp_all <;> ring

theorem point_primitive (i j : Fin m) (a b : ℚ) (t : ℝ) (k : Fin m) :
    Expr.Executes (fun _ : Unit => t) ((pointCircuit i j a b).output k)
      ((point i j a b t).value k) 5 := by
  exact Expr.executes_of_valid _ _ ⟨trivial,⟨trivial,trivial⟩⟩

theorem point_cost (i j : Fin m) (a b : ℚ) (t : ℝ) :
    (point i j a b t).cost = 14*m+1 := by
  simp [point,pointCircuit,Circuit.cost,Expr.cost]
  omega

theorem point_norm (i j : Fin m) (a b : ℚ) (t : ℝ)
    (ha : |(a : ℝ)| ≤ 1) (hb : |(b : ℝ)| ≤ 1) : ‖(point i j a b t).value‖ ≤ 2*|t| := by
  rw [point_value,norm_smul,Real.norm_eq_abs]
  have hi : ‖coordinate i‖ = 1 := by simp [coordinate,EuclideanSpace.norm_single]
  have hj : ‖coordinate j‖ = 1 := by simp [coordinate,EuclideanSpace.norm_single]
  have h := norm_add_le ((a : ℝ) • coordinate i) ((b : ℝ) • coordinate j)
  simp only [norm_smul,Real.norm_eq_abs,hi,hj,mul_one] at h
  have hh := mul_le_mul_of_nonneg_left (show ‖(a : ℝ) • coordinate i+(b : ℝ) • coordinate j‖ ≤ 2 by linarith) (abs_nonneg t)
  nlinarith

abbrev Report (m : ℕ) := Space m → Counted ℝ

def query (R : Report m) (i j : Fin m) (a b : ℚ) (t : ℝ) : Counted ℝ :=
  let p := point i j a b t
  let r := R p.value
  ⟨r.value,p.cost+r.cost+2⟩

theorem query_cost (R : Report m) {Q : ℕ} (t : ℝ)
    (hQ : ∀ z, ‖z‖ ≤ 2*|t| → (R z).cost ≤ Q)
    (i j : Fin m) (a b : ℚ) (ha : |(a : ℝ)| ≤ 1) (hb : |(b : ℝ)| ≤ 1) :
    (query R i j a b t).cost ≤ Q+14*m+3 := by
  have h := hQ _ (point_norm i j a b t ha hb)
  dsimp only [query]
  rw [point_cost]
  omega

def diagonalExpr : Expr (Fin 5) :=
  .div (.add (.sub (.input 0) (.mul (.constant 2) (.input 1))) (.input 2))
    (.mul (.input 4) (.input 4))

def mixedExpr : Expr (Fin 5) :=
  .div (.add (.sub (.sub (.input 0) (.input 1)) (.input 2)) (.input 3))
    (.mul (.constant 4) (.mul (.input 4) (.input 4)))

theorem diagonalExpr_valid (v : Fin 5 → ℝ) (ht : v 4 ≠ 0) : diagonalExpr.Valid v := by
  simp [diagonalExpr,Expr.Valid,Expr.eval,ht]

theorem mixedExpr_valid (v : Fin 5 → ℝ) (ht : v 4 ≠ 0) : mixedExpr.Valid v := by
  simp [mixedExpr,Expr.Valid,Expr.eval,ht]

def entry (R : Report m) (t : ℝ) (i j : Fin m) : Counted ℝ :=
  if i = j then
    let p := query R i i 1 0 t
    let z := R 0
    let n := query R i i (-1) 0 t
    let v : Fin 5 → ℝ := ![p.value,z.value,n.value,0,t]
    ⟨diagonalExpr.eval v,p.cost+z.cost+n.cost+diagonalExpr.cost+3*m+8⟩
  else
    let pp := query R i j 1 1 t
    let pm := query R i j 1 (-1) t
    let mp := query R i j (-1) 1 t
    let mm := query R i j (-1) (-1) t
    let v : Fin 5 → ℝ := ![pp.value,pm.value,mp.value,mm.value,t]
    ⟨mixedExpr.eval v,pp.cost+pm.cost+mp.cost+mm.cost+mixedExpr.cost+8⟩

theorem entry_value (R : Report m) (t : ℝ) (i j : Fin m) :
    (entry R t i j).value = KSFullManuscriptHessian.matrixReport (fun z => (R z).value) 0 t i j := by
  by_cases hij : i = j
  · subst j
    rw [KSFullManuscriptHessian.diagonal_queries]
    simp [entry,query,point_value,diagonalExpr,Expr.eval,pow_two]
  · rw [KSFullManuscriptHessian.offDiagonal_queries _ _ _ hij]
    simp only [entry,if_neg hij,query,point_value,mixedExpr,Expr.eval]
    norm_num
    have hpp : t • (coordinate i+coordinate j) = t • coordinate i+t • coordinate j := smul_add _ _ _
    have hpm : t • (coordinate i-coordinate j) = t • coordinate i-t • coordinate j := smul_sub _ _ _
    have hmp : t • (-coordinate i+coordinate j) = -(t • coordinate i)+t • coordinate j := by simp [smul_add]
    have hmm : t • (-coordinate i-coordinate j) = -(t • coordinate i)-t • coordinate j := by simp [smul_sub]
    simp [hpp,hpm,hmp,hmm,zero_add,zero_sub,pow_two,sub_eq_add_neg,Matrix.cons_val]

theorem entry_cost (R : Report m) {Q : ℕ} (t : ℝ)
    (hQ : ∀ z, ‖z‖ ≤ 2*|t| → (R z).cost ≤ Q) (i j : Fin m) :
    (entry R t i j).cost ≤ 4*Q+100*(m+1) := by
  have h0 := hQ 0 (by simp)
  have hq (i j : Fin m) (a b : ℚ) (ha : |(a : ℝ)| ≤ 1) (hb : |(b : ℝ)| ≤ 1) :=
    query_cost R t hQ i j a b ha hb
  by_cases hij : i = j
  · have hp := hq i i 1 0 (by norm_num) (by norm_num)
    have hn := hq i i (-1) 0 (by norm_num) (by norm_num)
    simp only [entry,if_pos hij]
    dsimp [diagonalExpr,Expr.cost]
    omega
  · have hpp := hq i j 1 1 (by norm_num) (by norm_num)
    have hpm := hq i j 1 (-1) (by norm_num) (by norm_num)
    have hmp := hq i j (-1) 1 (by norm_num) (by norm_num)
    have hmm := hq i j (-1) (-1) (by norm_num) (by norm_num)
    simp only [entry,if_neg hij]
    dsimp [mixedExpr,Expr.cost]
    omega

def matrix (R : Report m) (t : ℝ) : Counted (Matrix (Fin m) (Fin m) ℝ) :=
  ⟨fun i j => (entry R t i j).value, (∑i,∑j,(entry R t i j).cost)+6*m^2+1⟩

theorem matrix_value (R : Report m) (t : ℝ) :
    (matrix R t).value = KSFullManuscriptHessian.matrixReport (fun z => (R z).value) 0 t := by
  ext i j
  exact entry_value R t i j

theorem matrix_cost (R : Report m) {Q : ℕ} (t : ℝ)
    (hQ : ∀ z, ‖z‖ ≤ 2*|t| → (R z).cost ≤ Q) :
    (matrix R t).cost ≤ m^2*(4*Q+100*(m+1)+6)+1 := by
  have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => entry_cost R t hQ i j))
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at h
  dsimp [matrix]
  nlinarith

def weightedExpr : Expr (Fin 3) :=
  .div (.mul (.mul (.input 0) (.input 1)) (.input 2)) (.constant 2)

theorem weightedExpr_valid (v : Fin 3 → ℝ) : weightedExpr.Valid v := by
  simp [weightedExpr,Expr.Valid,Expr.eval]

def weighted (w : Fin m → ℝ) (A : Matrix (Fin m) (Fin m) ℝ) :
    Counted (Matrix (Fin m) (Fin m) ℝ) :=
  ⟨fun i j => weightedExpr.eval ![w i,A i j,w j],m^2*(weightedExpr.cost+5)+1⟩

theorem weighted_value (w : Fin m → ℝ) (A : Matrix (Fin m) (Fin m) ℝ) :
    (weighted w A).value = KSFullManuscriptHessian.weighted w A := by
  ext i j
  simp [weighted,weightedExpr,Expr.eval,KSFullManuscriptHessian.weighted]

theorem weighted_cost (w : Fin m → ℝ) (A : Matrix (Fin m) (Fin m) ℝ) :
    (weighted w A).cost = 12*m^2+1 := by
  simp [weighted,weightedExpr,Expr.cost]
  ring

end MatrixSpencer.RealRAM.FullHessian
