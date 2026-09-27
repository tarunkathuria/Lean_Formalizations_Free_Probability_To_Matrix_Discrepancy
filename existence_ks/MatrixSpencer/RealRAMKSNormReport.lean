import MatrixSpencer.RealRAMJacobiRayleigh
import MatrixSpencer.KSJacobiPolynomialBounds
import MatrixSpencer.KSFullManuscriptAcceptance

/-! Primitive arithmetic for the full-cube walk's final norm report. The
Jacobi budget is computed by the bounded scalar counter, and the actual
diagonal scan evaluates absolute values by square roots of squares. -/
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.RealRAM.KSNormReport
open JacobiIteration (Counted Mat)
attribute [local instance] Classical.propDecidable
variable {N d m : ℕ}

def absExpr : Expr Unit := .sqrt (.mul (.input ()) (.input ()))

theorem absExpr_eval (x : ℝ) : absExpr.eval (fun _ => x)=|x| := by
  simp [absExpr,Expr.eval,← pow_two,Real.sqrt_sq_eq_abs]

theorem absExpr_primitive (x : ℝ) :
    Expr.Executes (fun _ => x) absExpr |x| 4 := by
  have h : absExpr.Valid (fun _ => x) := by
    exact ⟨⟨trivial,trivial⟩,mul_self_nonneg x⟩
  have he := Expr.executes_of_valid _ _ h
  rw [absExpr_eval] at he
  exact he

def scan (A : Mat m) : List (Fin m) → Counted (Option (Fin m))
  | [] => ⟨none,1⟩
  | i::is =>
    let t := scan A is
    match t.value with
    | none => ⟨some i,t.cost+2⟩
    | some j =>
      ⟨if absExpr.eval (fun _ => A j j)≤absExpr.eval (fun _ => A i i)
        then some i else some j,t.cost+11⟩

theorem scan_value (A : Mat m) (is : List (Fin m)) :
    (scan A is).value=KSJacobiIteration.maxScan (fun i => |A i i|) is := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    simp only [scan,KSJacobiIteration.maxScan,ih]
    cases KSJacobiIteration.maxScan (fun i => |A i i|) is <;> simp only [absExpr_eval]

theorem scan_cost (A : Mat m) (is : List (Fin m)) :
    (scan A is).cost≤11*is.length+1 := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    simp only [scan,List.length_cons]
    cases (scan A is).value <;> dsimp <;> omega

def maximum (A : Mat m) : Counted ℝ :=
  let s := scan A (List.finRange m)
  ⟨match s.value with
    | none => 0
    | some i => absExpr.eval (fun _ => A i i),s.cost+3*m+6⟩

theorem maximum_value (A : Mat m) : (maximum A).value=KSJacobiNorm.maxAbsDiagonal A := by
  simp only [maximum,scan_value,KSJacobiNorm.maxAbsDiagonal]
  cases KSJacobiIteration.maxScan (fun i => |A i i|) (List.finRange m) <;>
    simp only [absExpr_eval]

theorem maximum_cost (A : Mat m) : (maximum A).cost≤14*m+7 := by
  have h := scan_cost A (List.finRange m)
  simp only [List.length_finRange] at h
  dsimp only [maximum]
  omega

def report (A : Mat m) (τ : ℝ) (cap : ℕ) : Counted ℝ :=
  let n := JacobiRayleigh.budget A τ cap
  let s := JacobiIteration.diagonalize A n.value
  let r := maximum s.value.matrix
  ⟨r.value,n.cost+s.cost+r.cost+3⟩

theorem budget_argument_valid (A : Mat m) {τ : ℝ} (hτ : τ≠0) :
    JacobiRayleigh.budgetExpr.Valid
      ![(m:ℝ),JacobiRayleigh.energyExpr.eval (JacobiIteration.entries A),τ] := by
  simp [JacobiRayleigh.budgetExpr,Expr.Valid,Expr.eval,hτ]

theorem report_value (A : Mat m) (τ : ℝ) (cap : ℕ)
    (hcap : KSJacobiIteration.denominator m*KSJacobiStep.offDiagonalEnergy A/τ^2≤cap) :
    (report A τ cap).value=KSJacobiNorm.maxAbsDiagonal (KSJacobiRayleigh.finalMatrix A τ) := by
  simp only [report,JacobiRayleigh.budget_value A τ cap hcap,maximum_value]
  rw [(JacobiIteration.diagonalize_actual A (KSJacobiIteration.iterationCount A τ)).1]
  rfl

theorem report_cost (A : Mat m) (τ : ℝ) (cap : ℕ) :
    (report A τ cap).cost≤600*(cap+1)*(m+1)^3 := by
  have hn : (JacobiRayleigh.budget A τ cap).value≤cap := by
    simp only [JacobiRayleigh.budget,JacobiRayleigh.ceilLoop_value]
    exact min_le_left _ _
  have h1 := JacobiRayleigh.budget_cost A τ cap
  have h2 := JacobiIteration.diagonalize_cost A (JacobiRayleigh.budget A τ cap).value
  have h3 := maximum_cost (JacobiIteration.diagonalize A (JacobiRayleigh.budget A τ cap).value).value.matrix
  have h2' : (JacobiIteration.diagonalize A (JacobiRayleigh.budget A τ cap).value).cost≤
      510*(cap+1)*(m+1)^3 := h2.trans (by gcongr)
  dsimp only [report]
  have hc : 1≤cap+1 := by omega
  have hp : 1≤(m+1)^3 := one_le_pow₀ (by omega)
  have hs : 20*(m+1)^2+14*m+40≤80*(m+1)^3 := by nlinarith
  have hmul := Nat.mul_le_mul_left (80*(m+1)^3) hc
  have hcap : cap≤(cap+1)*(m+1)^3 :=
    (Nat.le_succ cap).trans (by simpa using Nat.mul_le_mul_left (cap+1) hp)
  nlinarith

theorem center_norm_le (v : Fin N → Fin d → ℂ)
    (hp : (∑i,KSRankOne.atom (v i))=1) (x : Fin N → ℝ)
    (hx : ∀ i, |x i|≤1) : ‖KSPotentialModels.center (fun i => KSRankOne.atom (v i)) x‖≤(N:ℝ) := by
  unfold KSPotentialModels.center
  calc
    _ ≤ ∑ i, ‖x i • KSRankOne.atom (v i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin N, (1:ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul,Real.norm_eq_abs]
      exact (mul_le_mul (hx i) (KSManuscriptInputBudgetBounds.atom_norm_le_one v hp i)
        (norm_nonneg _) zero_le_one).trans_eq (by norm_num)
    _ = _ := by simp

theorem realification_entries (A : Matrix (Fin d) (Fin d) ℂ) {V : ℝ}
    (hA : ‖A‖≤V) (i j : Fin (d+d)) : |KSComplexTraceSqrt.realificationFin A i j|≤V := by
  have hre (k l : Fin d) := (Complex.abs_re_le_norm (A k l)).trans
    ((KSObjectiveValueBound.entry_norm_le A k l).trans hA)
  have him (k l : Fin d) := (Complex.abs_im_le_norm (A k l)).trans
    ((KSObjectiveValueBound.entry_norm_le A k l).trans hA)
  change |KSComplexTraceSqrt.realification A (finSumFinEquiv.symm i)
    (finSumFinEquiv.symm j)|≤V
  cases finSumFinEquiv.symm i <;> cases finSumFinEquiv.symm j <;>
    simp only [KSComplexTraceSqrt.realification_inl_inl,
      KSComplexTraceSqrt.realification_inl_inr,KSComplexTraceSqrt.realification_inr_inl,
      KSComplexTraceSqrt.realification_inr_inr,abs_neg] <;> first | apply hre | apply him

def normCap (N d : ℕ) : ℕ := KSJacobiPolynomialBounds.jacobi (d+d) N (4*N)

theorem norm_cap (v : Fin N → Fin d → ℂ) (hd : 0<d)
    (hp : (∑i,KSRankOne.atom (v i))=1) (x : Fin N → ℝ) (hx : ∀ i, |x i|≤1) :
    let A := KSComplexTraceSqrt.realificationFin
      (KSPotentialModels.center (fun i => KSRankOne.atom (v i)) x)
    KSJacobiIteration.denominator (d+d)*KSJacobiStep.offDiagonalEnergy A/
      (Real.sqrt (KSEighthManuscriptPreprocess.epsilon v)/4)^2≤(normCap N d:ℝ) := by
  apply KSJacobiPolynomialBounds.ceiling_input_le _ le_rfl
    (realification_entries _ (center_norm_le v hp x hx)) (by positivity)
  have h := KSManuscriptScaleBounds.inverse_delta_le v hd hp
  simp only [div_eq_mul_inv,_root_.mul_inv_rev,inv_inv,Nat.cast_mul,Nat.cast_ofNat]
  nlinarith

abbrev ComplexEntries (d : ℕ) := Fin d × Fin d × Bool

def complexEntries (A : Matrix (Fin d) (Fin d) ℂ) : ComplexEntries d → ℝ :=
  fun p => if p.2.2 then (A p.1 p.2.1).im else (A p.1 p.2.1).re

def realificationExpr (i j : Fin (d+d)) : Expr (ComplexEntries d) :=
  match finSumFinEquiv.symm i,finSumFinEquiv.symm j with
  | .inl k,.inl l => .input (k,l,false)
  | .inl k,.inr l => .sub (.constant 0) (.input (k,l,true))
  | .inr k,.inl l => .input (k,l,true)
  | .inr k,.inr l => .input (k,l,false)

theorem realificationExpr_eval (A : Matrix (Fin d) (Fin d) ℂ) (i j : Fin (d+d)) :
    (realificationExpr i j).eval (complexEntries A)=KSComplexTraceSqrt.realificationFin A i j := by
  change _=KSComplexTraceSqrt.realification A (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)
  unfold realificationExpr
  cases finSumFinEquiv.symm i <;> cases finSumFinEquiv.symm j <;>
    simp [Expr.eval,complexEntries,KSComplexTraceSqrt.realification]

theorem realificationExpr_valid (A : Matrix (Fin d) (Fin d) ℂ) (i j : Fin (d+d)) :
    (realificationExpr i j).Valid (complexEntries A) := by
  unfold realificationExpr
  cases finSumFinEquiv.symm i <;> cases finSumFinEquiv.symm j <;> trivial

theorem realificationExpr_cost (i j : Fin (d+d)) : (realificationExpr i j).cost≤3 := by
  unfold realificationExpr
  cases finSumFinEquiv.symm i <;> cases finSumFinEquiv.symm j <;> norm_num [Expr.cost]

def realificationCircuit : Circuit (ComplexEntries d) (Fin (d+d) × Fin (d+d)) where
  output p := realificationExpr p.1 p.2

def realify (A : Matrix (Fin d) (Fin d) ℂ) : Counted (Mat (d+d)) :=
  ⟨fun i j => realificationCircuit.eval (complexEntries A) (i,j),
    (realificationCircuit (d := d)).cost+20*(d+d)^2+1⟩

theorem realify_value (A : Matrix (Fin d) (Fin d) ℂ) :
    (realify A).value=KSComplexTraceSqrt.realificationFin A := by
  ext i j
  exact realificationExpr_eval A i j

theorem realify_cost (A : Matrix (Fin d) (Fin d) ℂ) :
    (realify A).cost≤24*(d+d)^2+1 := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun (p : Fin (d+d) × Fin (d+d)) _ =>
    Nat.add_le_add_right (realificationExpr_cost (d := d) p.1 p.2) 1)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,
    smul_eq_mul] at h
  dsimp only [realify,Circuit.cost,realificationCircuit]
  nlinarith

def complexReport (A : Matrix (Fin d) (Fin d) ℂ) (δ : ℝ) (cap : ℕ) : Counted ℝ :=
  let B := realify A
  let r := report B.value (δ/4) cap
  ⟨r.value,B.cost+r.cost+5⟩

theorem complexReport_value (A : Matrix (Fin d) (Fin d) ℂ) (δ : ℝ) (cap : ℕ)
    (hcap : KSJacobiIteration.denominator (d+d)*
      KSJacobiStep.offDiagonalEnergy (KSComplexTraceSqrt.realificationFin A)/(δ/4)^2≤cap) :
    (complexReport A δ cap).value=KSFullManuscriptAcceptance.normReport A δ := by
  simp only [complexReport,realify_value,report_value _ _ _ hcap,
    KSFullManuscriptAcceptance.normReport]

theorem complexReport_cost (A : Matrix (Fin d) (Fin d) ℂ) (δ : ℝ) (cap : ℕ) :
    (complexReport A δ cap).cost≤700*(cap+1)*(d+d+1)^3 := by
  have h1 := realify_cost A
  have h2 := report_cost (realify A).value (δ/4) cap
  have hsmall : 24*(d+d)^2+6≤100*(d+d+1)^3 := by
    have hpow := Nat.pow_le_pow_right (show 0<d+d+1 by omega) (show 2≤3 by omega)
    have hone : 1≤(d+d+1)^2 := one_le_pow₀ (by omega)
    calc
      _ ≤ 24*(d+d+1)^2+6 := Nat.add_le_add_right
        (Nat.mul_le_mul_left 24 (Nat.pow_le_pow_left (Nat.le_succ (d+d)) 2)) 6
      _ ≤ 30*(d+d+1)^2 := by omega
      _ ≤ 30*(d+d+1)^3 := Nat.mul_le_mul_left 30 hpow
      _ ≤ _ := by omega
  have hmul := Nat.mul_le_mul_left (100*(d+d+1)^3) (show 1≤cap+1 by omega)
  dsimp only [complexReport]
  nlinarith

def signScan (x : Fin N → ℝ) : List (Fin N) → Counted Bool
  | [] => ⟨true,1⟩
  | i::is =>
    let r := signScan x is
    ⟨(decide (x i=1)||decide (x i= -1))&&r.value,r.cost+9⟩

theorem signScan_value (x : Fin N → ℝ) (is : List (Fin N)) :
    (signScan x is).value=is.all (fun i => decide (x i=1)||decide (x i= -1)) := by
  induction is with
  | nil => rfl
  | cons i is ih => simp only [signScan,List.all_cons,ih]

theorem signScan_cost (x : Fin N → ℝ) (is : List (Fin N)) :
    (signScan x is).cost=9*is.length+1 := by
  induction is with
  | nil => rfl
  | cons i is ih => simp only [signScan,List.length_cons,ih]; omega

def thresholdExpr : Expr Unit :=
  .mul (.mul (.constant 8)
    (.add (.mul (.constant 16) (.sqrt (.constant 2))) (.constant 5))) (.input ())

theorem thresholdExpr_eval (δ : ℝ) : thresholdExpr.eval (fun _ => δ)=
    8*KSFullManuscriptParameters.signingScale*δ := by
  simp [thresholdExpr,Expr.eval,KSFullManuscriptParameters.signingScale]

theorem thresholdExpr_valid (δ : ℝ) : thresholdExpr.Valid (fun _ => δ) := by
  norm_num [thresholdExpr,Expr.Valid,Expr.eval]

/-- The matrix formation cost is supplied by the separately counted signed
center circuit. The rest of the final acceptance test is evaluated here. -/
def acceptance (x : Fin N → ℝ) (A : Counted (Matrix (Fin d) (Fin d) ℂ))
    (δ : ℝ) (cap : ℕ) : Counted Bool :=
  let s := signScan x (List.finRange N)
  let r := complexReport A.value δ cap
  ⟨s.value&&decide (r.value≤thresholdExpr.eval (fun _ => δ)),
    A.cost+s.cost+r.cost+thresholdExpr.cost+3*N+4⟩

theorem acceptance_value (x : Fin N → ℝ) (A : Counted (Matrix (Fin d) (Fin d) ℂ))
    (δ : ℝ) (cap : ℕ)
    (hcap : KSJacobiIteration.denominator (d+d)*
      KSJacobiStep.offDiagonalEnergy (KSComplexTraceSqrt.realificationFin A.value)/(δ/4)^2≤cap) :
    (acceptance x A δ cap).value=(
      (List.finRange N).all (fun i => decide (x i=1)||decide (x i= -1)) &&
      decide (KSFullManuscriptAcceptance.normReport A.value δ≤
        8*KSFullManuscriptParameters.signingScale*δ)) := by
  simp only [acceptance,signScan_value,complexReport_value _ _ _ hcap,thresholdExpr_eval]

theorem acceptance_cost (x : Fin N → ℝ) (A : Counted (Matrix (Fin d) (Fin d) ℂ))
    (δ : ℝ) (cap : ℕ) : (acceptance x A δ cap).cost≤
      A.cost+700*(cap+1)*(d+d+1)^3+12*N+20 := by
  have h1 := signScan_cost x (List.finRange N)
  have h2 := complexReport_cost A.value δ cap
  simp only [List.length_finRange] at h1
  dsimp only [acceptance,thresholdExpr,Expr.cost]
  omega

end MatrixSpencer.RealRAM.KSNormReport
