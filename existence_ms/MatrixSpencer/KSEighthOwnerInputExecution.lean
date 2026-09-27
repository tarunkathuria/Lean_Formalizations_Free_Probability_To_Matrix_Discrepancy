import MatrixSpencer.KSEighthOwnerInputSetup

/-! Primitive input-entry witnesses and the counted owner-mask scan. The mask
is materialized before a report, with a finite membership search for each
original label; no set-membership or owner arithmetic oracle is charged. -/
open Set Matrix
open scoped BigOperators
noncomputable section
namespace MatrixSpencer.KSEighthOwnerInputExecution
open RealRAM RealRAM.JacobiIteration KSEighthOwnerInputSetup
variable {N d : ℕ}
attribute [local instance] Classical.propDecidable

theorem H_entry_execution (v : Fin N → Fin d → ℂ) (x : Fin N → ℝ) (j k : Fin (d+d)) :
    let e := lifted (N:=N) (KSEighthNumericalValue.blockIndex d j) (KSEighthNumericalValue.blockIndex d k)
    Expr.Executes (input v x) e.re ((H v x).value j k).re e.re.cost ∧
    Expr.Executes (input v x) e.im ((H v x).value j k).im e.im.cost := by
  dsimp
  exact ⟨Expr.executes_of_valid _ _ (lifted_valid (input v x) _ _).1,
    Expr.executes_of_valid _ _ (lifted_valid (input v x) _ _).2⟩

theorem A_entry_execution (v : Fin N → Fin d → ℂ) (x : Fin N → ℝ) (a : Fin N × Bool) (j k : Fin (d+d)) :
    let e := family a (KSEighthNumericalValue.blockIndex d j) (KSEighthNumericalValue.blockIndex d k)
    Expr.Executes (input v x) e.re ((A v x).value a j k).re e.re.cost ∧
    Expr.Executes (input v x) e.im ((A v x).value a j k).im e.im.cost := by
  dsimp
  exact ⟨Expr.executes_of_valid _ _ (family_valid (input v x) a _ _).1,
    Expr.executes_of_valid _ _ (family_valid (input v x) a _ _).2⟩

def membership (i : Fin N) : List (Fin N) → Counted Bool
  | [] => ⟨false,1⟩
  | j::js => if i=j then ⟨true,4⟩ else
      let r := membership i js
      ⟨r.value,r.cost+6⟩
theorem membership_value (i : Fin N) (js : List (Fin N)) :
    (membership i js).value=decide (i∈js) := by
  induction js with
  | nil => simp [membership]
  | cons j js ih => by_cases h:i=j <;> simp [membership,h,ih]
theorem membership_cost (i : Fin N) (js : List (Fin N)) :
    (membership i js).cost≤6*js.length+1 := by
  induction js with
  | nil => rfl
  | cons j js ih =>
    simp only [membership,List.length_cons]
    split_ifs <;> dsimp <;> omega

def ownerExpr : Expr Unit :=
  .mul (.constant 64) (.sub (.constant 1) (.mul (.input ()) (.input ())))
theorem ownerExpr_value (x : ℝ) : ownerExpr.eval (fun _=>x)=64*(1-x^2) := by
  simp [ownerExpr,Expr.eval,pow_two]
theorem ownerExpr_execution (x : ℝ) :
    Expr.Executes (fun _=>x) ownerExpr (64*(1-x^2)) ownerExpr.cost ∧ ownerExpr.cost≤8 := by
  rw [←ownerExpr_value]
  exact ⟨Expr.executes_of_valid _ _ (by simp [ownerExpr,Expr.Valid]),by norm_num [ownerExpr,Expr.cost]⟩

def mask (L : Finset (Fin N)) (x : Fin N → ℝ) : Counted (Fin N → ℝ) :=
  let m := fun i=>membership i L.toList
  ⟨fun i=>if (m i).value then ownerExpr.eval (fun _=>x i) else 0,
    (∑i,((m i).cost+ownerExpr.cost+8))+20*N+1⟩
theorem mask_value (L : Finset (Fin N)) (x : Fin N → ℝ) :
    (mask L x).value=KSPotentialModels.maskedOwners 64 L x := by
  funext i
  simp [mask,membership_value,ownerExpr_value,KSPotentialModels.maskedOwners,KSPotentialModels.naturalOwners]
theorem mask_cost (L : Finset (Fin N)) (x : Fin N → ℝ) : (mask L x).cost≤100*(N+1)^2 := by
  have hL : L.toList.length≤N := by
    simpa only [Finset.length_toList,Fintype.card_fin] using L.card_le_univ
  have hs : (∑i,((membership i L.toList).cost+ownerExpr.cost+8))≤N*(6*N+17) := by
    calc
      _ ≤ ∑_i : Fin N,(6*N+17) := by
        apply Finset.sum_le_sum
        intro i _
        have h := membership_cost i L.toList
        have he := (ownerExpr_execution (x i)).2
        omega
      _ = _ := by simp
  dsimp only [mask]
  nlinarith

end MatrixSpencer.KSEighthOwnerInputExecution
