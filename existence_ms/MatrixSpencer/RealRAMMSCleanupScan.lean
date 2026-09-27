import MatrixSpencer.RealRAMLDLResiduals
import MatrixSpencer.RealRAMJacobiIteration
import MatrixSpencer.MSManuscriptSchurCleanup

/-! Primitive counted implementation of the original fixed-diagonal Schur
cleanup scan. Every Schur update executes the guarded scalar-short program;
selection tests use the original diagonal, not a newly changed residual. -/
open Matrix
noncomputable section
namespace MatrixSpencer.RealRAM.MSCleanupScan
open JacobiIteration (Counted Mat)
attribute [local instance] Classical.propDecidable
variable {d : ℕ}

def shortInput (G : Mat d) (u : Fin d → ℝ) : ScalarShort.Registers d → ℝ :=
  Sum.elim (ScalarShort.input G u) (fun _ => 0)

def short (G : Mat d) (u : Fin d → ℝ) : Counted (Mat d) :=
  let w := (ScalarShort.program d).run (shortInput G u)
  ⟨fun i j => w (.inr (i,j)),
    (ScalarShort.program d).cost (shortInput G u)+10*(d+1)^2⟩

theorem short_value (G : Mat d) (u : Fin d → ℝ) :
    (short G u).value=MSManuscriptNumericalShort.short G u := by
  ext i j
  exact ScalarShort.program_output (shortInput G u) (i,j)

theorem short_execution (G : Mat d) (u : Fin d → ℝ) :
    Program.Executes (ScalarShort.program d) (shortInput G u)
      ((ScalarShort.program d).run (shortInput G u))
      ((ScalarShort.program d).cost (shortInput G u)) :=
  Program.executes_of_safe _ _ (ScalarShort.program_safe _)

theorem short_cost (G : Mat d) (u : Fin d → ℝ) :
    (short G u).cost≤56*(d+1)^4 := by
  have h:=((ScalarShort.program d).cost_le_bound (shortInput G u)).trans
    (ScalarShort.program_bound d)
  have hp : (d+1)^2≤(d+1)^4 := Nat.pow_le_pow_right (by omega) (by omega)
  dsimp only [short]
  omega

def coordinate (j : Fin d) : Counted (Fin d → ℝ) :=
  ⟨fun i => if j=i then 1 else 0,4*d+1⟩

theorem coordinate_value (j : Fin d) : (coordinate j).value=Pi.single j 1 := by
  funext i
  simp [coordinate,Pi.single_apply,eq_comm]

def schur (G : Mat d) (j : Fin d) : Counted (Mat d) :=
  let u:=coordinate j
  let s:=short G u.value
  ⟨s.value,u.cost+s.cost+2⟩

theorem schur_value (G : Mat d) (j : Fin d) :
    (schur G j).value=KSEighthManuscriptLDL.schur G j := by
  simp only [schur,coordinate_value,short_value,LDLResiduals.short_single,
    MSManuscriptNumericalLDL.schur_eq]

theorem schur_cost (G : Mat d) (j : Fin d) : (schur G j).cost≤64*(d+1)^4 := by
  have h:=short_cost G (coordinate j).value
  have hd : d≤(d+1)^4 := by nlinarith [Nat.zero_le (d^2),Nat.zero_le (d^3),Nat.zero_le (d^4)]
  have h1 : 1≤(d+1)^4 := Nat.one_le_pow _ _ (by omega)
  dsimp only [schur,coordinate] at h ⊢
  omega

/-- One multiplication computes the threshold before the diagonal comparison. -/
def thresholdExpr : Expr Unit := .mul (.constant 3) (.input ())
@[simp] theorem threshold_eval (δ : ℝ) : thresholdExpr.eval (fun _ => δ)=3*δ := by
  norm_num [thresholdExpr,Expr.eval]
theorem threshold_execution (δ : ℝ) :
    Expr.Executes (fun _ => δ) thresholdExpr (3*δ) 3 := by
  simpa [thresholdExpr,Expr.cost] using
    Expr.executes_of_valid (fun _ => δ) thresholdExpr (by simp [thresholdExpr,Expr.Valid])

def scan (G : Mat d) (δ : ℝ) : ℕ → Counted (Mat d)
  | 0 => ⟨G,2*d^2+1⟩
  | j+1 =>
    let previous:=scan G δ j
    if hj : j<d then
      if G ⟨j,hj⟩ ⟨j,hj⟩ < thresholdExpr.eval (fun _ => δ) then
        let s:=schur previous.value ⟨j,hj⟩
        ⟨s.value,previous.cost+s.cost+10⟩
      else ⟨previous.value,previous.cost+10⟩
    else ⟨previous.value,previous.cost+2⟩

theorem scan_value (G : Mat d) (δ : ℝ) (j : ℕ) :
    (scan G δ j).value=MSManuscriptSchurCleanup.runScan G δ j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [scan,MSManuscriptSchurCleanup.runScan,threshold_eval]
    split_ifs <;> simp only [schur_value,ih]

theorem scan_cost (G : Mat d) (δ : ℝ) (j : ℕ) :
    (scan G δ j).cost≤2*d^2+1+j*(74*(d+1)^4) := by
  induction j with
  | zero => simp [scan]
  | succ j ih =>
    have h1 : 1≤(d+1)^4 := Nat.one_le_pow _ _ (by omega)
    simp only [scan]
    split_ifs with hj hc
    · have hs:=schur_cost (scan G δ j).value ⟨j,hj⟩
      dsimp only
      nlinarith
    · dsimp only; nlinarith
    · dsimp only; nlinarith

def labels (G : Mat d) (δ : ℝ) : List (Fin d) → Counted (List (Fin d))
  | [] => ⟨[],1⟩
  | i::is =>
    let t:=labels G δ is
    ⟨if thresholdExpr.eval (fun _ => δ)≤G i i then i::t.value else t.value,t.cost+9⟩

theorem labels_value (G : Mat d) (δ : ℝ) (is : List (Fin d)) :
    (labels G δ is).value=is.filter (fun i => decide (3*δ≤G i i)) := by
  induction is with
  | nil => rfl
  | cons i is ih => simp [labels,ih]; split_ifs <;> simp_all

theorem labels_cost (G : Mat d) (δ : ℝ) (is : List (Fin d)) :
    (labels G δ is).cost=9*is.length+1 := by
  induction is with
  | nil => rfl
  | cons i is ih => simp [labels,ih];omega

end MatrixSpencer.RealRAM.MSCleanupScan
