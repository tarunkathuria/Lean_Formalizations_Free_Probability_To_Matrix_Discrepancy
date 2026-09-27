import MatrixSpencer.RealRAMFullHessian
import MatrixSpencer.RealRAMCeiling

/-! A counted Rayleigh output, including formation of the Jacobi budget,
bounded scalar ceiling computation, the actual rotations, the final diagonal
scan, and basis-column extraction. The supplied cap bounds the ceiling loop;
it does not replace the actual matrix-dependent rotation budget. -/
open Matrix
open scoped BigOperators
noncomputable section
namespace MatrixSpencer.RealRAM.JacobiRayleigh
open JacobiIteration (Counted Mat)
attribute [local instance] Classical.propDecidable
variable {m : ℕ}

def ceilLoop (x : ℝ) : ℕ → Counted ℕ
  | 0 => ⟨0,3⟩
  | n+1 =>
    let p := ceilLoop x n
    ⟨if x≤(p.value:ℝ) then p.value else p.value+1,p.cost+8⟩

theorem ceilLoop_value (x : ℝ) (n : ℕ) : (ceilLoop x n).value=min n ⌈x⌉₊ := by
  induction n with
  | zero => simp [ceilLoop]
  | succ n ih =>
    simp only [ceilLoop,ih]
    by_cases hn : ⌈x⌉₊≤n
    · rw [min_eq_right hn,min_eq_right (by omega : ⌈x⌉₊≤n+1),if_pos (Nat.le_ceil x)]
    · have hn' : n≤⌈x⌉₊ := by omega
      have hs : n+1≤⌈x⌉₊ := by omega
      rw [min_eq_left hn',min_eq_left hs,if_neg (by intro h; exact hn (Nat.ceil_le.mpr h))]

theorem ceilLoop_exact (x : ℝ) (cap : ℕ) (hcap : x≤cap) :
    (ceilLoop x cap).value=⌈x⌉₊ := by
  rw [ceilLoop_value,min_eq_right (Nat.ceil_le.mpr hcap)]

theorem ceilLoop_cost (x : ℝ) (cap : ℕ) : (ceilLoop x cap).cost=8*cap+3 := by
  induction cap with
  | zero => rfl
  | succ n ih => simp [ceilLoop,ih]; omega

/-- The natural counter and its real-register program coincide. Thus no
real-to-integer conversion is silently taken as one instruction. -/
theorem ceilLoop_program (x : ℝ) (cap : ℕ) :
    ((ceilLoop x cap).value:ℝ)=
      (Ceiling.program cap).run (fun r => match r with
        | .argument => x | .counter => 0) .counter := by
  rw [ceilLoop_value]
  symm
  change (Ceiling.step.run)^[cap]
    (Function.update (fun r => match r with | .argument => x | .counter => 0)
      .counter ((0:ℚ):ℝ)) .counter = _
  have hz : (Function.update (fun r : Ceiling.Register => match r with
      | .argument => x | .counter => 0) .counter ((0:ℚ):ℝ)) .counter=0 := by simp
  simpa using Ceiling.iterate_counter cap _ hz

def energyExpr : Expr (Fin m × Fin m) :=
  Expr.sumList (List.ofFn (fun i : Fin m => Expr.sumList (List.ofFn (fun j : Fin m =>
    if i=j then .constant 0 else .mul (.input (i,j)) (.input (i,j))))))

theorem energyExpr_eval (A : Mat m) : energyExpr.eval (JacobiIteration.entries A)=
    KSJacobiStep.offDiagonalEnergy A := by
  simp [energyExpr,Expr.eval_sumList,List.map_ofFn,List.sum_ofFn,Expr.eval,
    JacobiIteration.entries,KSJacobiStep.offDiagonalEnergy,pow_two,apply_ite]

theorem energyExpr_valid (A : Mat m) : energyExpr.Valid (JacobiIteration.entries A) := by
  apply Expr.valid_sumList
  intro e he
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp he
  apply Expr.valid_sumList
  intro e he
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp he
  split_ifs <;> simp [Expr.Valid]

theorem energyExpr_cost : (energyExpr (m := m)).cost≤4*m^2+2*m+1 := by
  simp only [energyExpr,Expr.cost_sumList,List.map_ofFn,List.length_ofFn,List.sum_ofFn,Function.comp_def]
  have h : ∀i j : Fin m, (if i=j then (Expr.constant 0 : Expr (Fin m × Fin m)) else
      .mul (.input (i,j)) (.input (i,j))).cost+1≤4 := by
    intro i j
    split_ifs <;> norm_num [Expr.cost]
  have hs := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) =>
    Finset.sum_le_sum (fun j (_ : j∈Finset.univ) => h i j))
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,smul_eq_mul] at hs ⊢
  nlinarith

def budgetExpr : Expr (Fin 3) :=
  .div (.mul (.add (.mul (.input 0) (.input 0)) (.constant 1)) (.input 1))
    (.mul (.input 2) (.input 2))

def budget (A : Mat m) (τ : ℝ) (cap : ℕ) : Counted ℕ :=
  let e := energyExpr.eval (JacobiIteration.entries A)
  let y := budgetExpr.eval ![(m:ℝ),e,τ]
  let c := ceilLoop y cap
  ⟨c.value,(energyExpr (m := m)).cost+10*m^2+budgetExpr.cost+c.cost+8⟩

theorem budget_argument (A : Mat m) (τ : ℝ) :
    budgetExpr.eval ![(m:ℝ),energyExpr.eval (JacobiIteration.entries A),τ]=
      KSJacobiIteration.denominator m*KSJacobiStep.offDiagonalEnergy A/τ^2 := by
  simp [budgetExpr,Expr.eval,energyExpr_eval,KSJacobiIteration.denominator,pow_two]

theorem budget_value (A : Mat m) (τ : ℝ) (cap : ℕ)
    (hcap : KSJacobiIteration.denominator m*KSJacobiStep.offDiagonalEnergy A/τ^2≤cap) :
    (budget A τ cap).value=KSJacobiIteration.iterationCount A τ := by
  simp only [budget,budget_argument]
  exact ceilLoop_exact _ cap hcap

theorem budget_cost (A : Mat m) (τ : ℝ) (cap : ℕ) :
    (budget A τ cap).cost≤20*(m+1)^2+8*cap+30 := by
  have h := energyExpr_cost (m := m)
  dsimp only [budget]
  rw [ceilLoop_cost]
  norm_num [budgetExpr,Expr.cost]
  nlinarith

def scan (A : Mat m) : List (Fin m) → Counted (Option (Fin m))
  | [] => ⟨none,1⟩
  | i::is =>
    let t := scan A is
    match t.value with
    | none => ⟨some i,t.cost+2⟩
    | some j => ⟨if A i i≤A j j then some i else some j,t.cost+5⟩

theorem scan_value (A : Mat m) (is : List (Fin m)) :
    (scan A is).value=KSJacobiIteration.maxScan (fun i => -A i i) is := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    simp only [scan,KSJacobiIteration.maxScan,ih]
    cases KSJacobiIteration.maxScan (fun i => -A i i) is with
    | none => rfl
    | some j => simp

theorem scan_cost (A : Mat m) (is : List (Fin m)) :
    (scan A is).cost≤5*is.length+1 := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    simp only [scan,List.length_cons]
    cases (scan A is).value <;> dsimp <;> omega

def minimum (A : Mat m) (hm : 0<m) : Counted (Fin m) :=
  let s := scan A (List.finRange m)
  ⟨s.value.getD ⟨0,hm⟩,s.cost+3*m+2⟩

theorem minimum_value (A : Mat m) (hm : 0<m) :
    (minimum A hm).value=KSJacobiRayleigh.minimumDiagonal A hm := by
  simp [minimum,scan_value,KSJacobiRayleigh.minimumDiagonal]

theorem minimum_cost (A : Mat m) (hm : 0<m) : (minimum A hm).cost≤8*m+3 := by
  have h := scan_cost A (List.finRange m)
  simp only [List.length_finRange] at h
  dsimp [minimum]
  omega

def output (A : Mat m) (τ : ℝ) (cap : ℕ) (hm : 0<m) : Counted (KSNumericalHessian.Space m) :=
  let n := budget A τ cap
  let s := JacobiIteration.diagonalize A n.value
  let i := minimum s.value.matrix hm
  ⟨WithLp.toLp 2 (fun j => s.value.basis j i.value),n.cost+s.cost+i.cost+3*m+3⟩

theorem output_value (A : Mat m) (τ : ℝ) (cap : ℕ) (hm : 0<m)
    (hcap : KSJacobiIteration.denominator m*KSJacobiStep.offDiagonalEnergy A/τ^2≤cap) :
    (output A τ cap hm).value=KSJacobiRayleigh.outputVector A τ hm := by
  simp only [output,budget_value A τ cap hcap,minimum_value]
  obtain ⟨he,hb⟩ := JacobiIteration.diagonalize_actual A (KSJacobiIteration.iterationCount A τ)
  simp only [he,hb,KSJacobiRayleigh.outputVector,KSJacobiRayleigh.finalMatrix,
    KSJacobiRayleigh.finalBasis,KSJacobiRayleigh.basisColumn]

theorem output_cost (A : Mat m) (τ : ℝ) (cap : ℕ) (hm : 0<m) :
    (output A τ cap hm).cost≤600*(cap+1)*(m+1)^3 := by
  have hn : (budget A τ cap).value≤cap := by
    simp only [budget,ceilLoop_value]
    exact min_le_left _ _
  have h1 := budget_cost A τ cap
  have h2 := JacobiIteration.diagonalize_cost A (budget A τ cap).value
  have h3 := minimum_cost (JacobiIteration.diagonalize A (budget A τ cap).value).value.matrix hm
  have h2' : (JacobiIteration.diagonalize A (budget A τ cap).value).cost≤510*(cap+1)*(m+1)^3 :=
    h2.trans (by gcongr)
  dsimp only [output]
  have hc : 1≤cap+1 := by omega
  have hm' : 1≤m+1 := by omega
  have hpow : 1≤(m+1)^3 := one_le_pow₀ hm'
  have hsmall : 20*(m+1)^2+11*m+36≤80*(m+1)^3 := by nlinarith
  have hs := Nat.mul_le_mul_left (80*(m+1)^3) hc
  have hcap : cap≤(cap+1)*(m+1)^3 :=
    (Nat.le_succ cap).trans (by simpa using Nat.mul_le_mul_left (cap+1) hpow)
  nlinarith

end MatrixSpencer.RealRAM.JacobiRayleigh
