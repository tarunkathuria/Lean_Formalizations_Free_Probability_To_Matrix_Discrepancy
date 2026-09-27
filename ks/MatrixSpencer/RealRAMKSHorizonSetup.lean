import MatrixSpencer.RealRAMKSParameterSetup
import MatrixSpencer.RealRAMJacobiRayleigh
import MatrixSpencer.KSConvexQueryBudgets

/-! The actual finite walk horizon is computed from the already counted
input parameters. Ceiling is a bounded comparison loop, not a unit-cost
real-to-integer primitive. Natural polynomial-cap formation is supplied by
the separate fixed arithmetic cap circuit. -/
open Matrix
open scoped BigOperators
noncomputable section
namespace MatrixSpencer.RealRAM.KSHorizonSetup
open JacobiIteration (Counted)
open KSEighthManuscriptPreprocess
variable {N d : ℕ} [Nonempty (Fin d)]

def argument (c : ℚ) : Expr (Fin 2) :=
  .div (.mul (.constant c) (.input 0)) (.mul (.input 1) (.input 1))

theorem argument_eval (c : ℚ) (n h : ℝ) :
    (argument c).eval ![n,h]=(c:ℝ)*n/h^2 := by
  simp [argument,Expr.eval,pow_two]

theorem argument_valid (c : ℚ) (n h : ℝ) (hh : h≠0) :
    (argument c).Valid ![n,h] := by
  simp [argument,Expr.Valid,Expr.eval,hh]

def compute (v : Fin N → Fin d → ℂ) (slot : Fin 14) (c : ℚ) (cap : ℕ) :
    Counted ((Fin 14 → ℝ) × ℕ) :=
  let p := KSParameterSetup.compute v
  let y := (argument c).eval ![(N:ℝ),p.value slot]
  let n := JacobiRayleigh.ceilLoop y cap
  ⟨(p.value,n.value),p.cost+(argument c).cost+n.cost+8⟩

theorem compute_parameters (v : Fin N → Fin d → ℂ) (slot : Fin 14) (c : ℚ) (cap : ℕ) :
    (compute v slot c cap).value.1=KSParameterSetup.originalOutputs v (epsilon v) := by
  exact KSParameterSetup.compute_value v

theorem compute_horizon (v : Fin N → Fin d → ℂ) (slot : Fin 14) (c : ℚ) (cap : ℕ)
    (hcap : (c:ℝ)*(N:ℝ)/(KSParameterSetup.originalOutputs v (epsilon v) slot)^2≤cap) :
    (compute v slot c cap).value.2=
      ⌈(c:ℝ)*(N:ℝ)/(KSParameterSetup.originalOutputs v (epsilon v) slot)^2⌉₊ := by
  simp only [compute,KSParameterSetup.compute_value,argument_eval]
  exact JacobiRayleigh.ceilLoop_exact _ cap hcap

theorem compute_cost (v : Fin N → Fin d → ℂ) (slot : Fin 14) (c : ℚ) (cap : ℕ) :
    (compute v slot c cap).cost≤10000400*(N+1)*(d+1)+8*cap+30 := by
  have h := KSParameterSetup.compute_cost v
  dsimp only [compute]
  rw [JacobiRayleigh.ceilLoop_cost]
  norm_num [argument,Expr.cost]
  omega

def full (v : Fin N → Fin d → ℂ) := compute v 7 16 (KSConvexQueryBudgets.fullHorizon N d)
def eighth (v : Fin N → Fin d → ℂ) := compute v 13 100 (KSConvexQueryBudgets.eighthHorizon N d)

theorem full_value (v : Fin N → Fin d → ℂ) (hd : 0<d)
    (hp : (∑i,KSRankOne.atom (v i))=1) :
    (full v).value=(KSParameterSetup.originalOutputs v (epsilon v),
      KSFullManuscriptAlgorithm.horizon v (epsilon v)) := by
  have hcap := (Nat.le_ceil (16*(N:ℝ)/
    (KSFullManuscriptParameters.movementStep N (Real.sqrt (epsilon v))
      (KSFullManuscriptAlgorithm.taylorBudget v (epsilon v)))^2)).trans
        (Nat.cast_le.mpr (KSConvexQueryBudgets.full_horizon v hd hp))
  have h := compute_horizon v 7 16 (KSConvexQueryBudgets.fullHorizon N d)
  have he : KSParameterSetup.originalOutputs v (epsilon v) 7=
      KSFullManuscriptParameters.movementStep N (Real.sqrt (epsilon v))
        (KSFullManuscriptAlgorithm.taylorBudget v (epsilon v)) := by rfl
  rw [he] at h
  norm_num only [Rat.cast_ofNat] at h
  exact Prod.ext (compute_parameters v _ _ _) (h hcap)

theorem eighth_value (v : Fin N → Fin d → ℂ) (hd : 0<d)
    (hp : (∑i,KSRankOne.atom (v i))=1) :
    (eighth v).value=(KSParameterSetup.originalOutputs v (epsilon v),
      KSEighthManuscriptBudgets.cutoff v (Real.sqrt (epsilon v))
        (ksRegularizerScale (epsilon v) (Fin d))) := by
  have hcap := (Nat.le_ceil (100*(N:ℝ)/
    (KSEighthManuscriptParameters.movementStep v (Real.sqrt (epsilon v))
      (ksRegularizerScale (epsilon v) (Fin d)))^2)).trans
        (Nat.cast_le.mpr (KSConvexQueryBudgets.eighth_horizon v hd hp))
  have h := compute_horizon v 13 100 (KSConvexQueryBudgets.eighthHorizon N d)
  have he : KSParameterSetup.originalOutputs v (epsilon v) 13=
      KSEighthManuscriptParameters.movementStep v (Real.sqrt (epsilon v))
        (ksRegularizerScale (epsilon v) (Fin d)) := by rfl
  rw [he] at h
  norm_num only [Rat.cast_ofNat] at h
  exact Prod.ext (compute_parameters v _ _ _) (h hcap)

theorem full_argument_valid (v : Fin N → Fin d → ℂ) (hd : 0<d)
    (hp : (∑i,KSRankOne.atom (v i))=1) :
    (argument 16).Valid ![(N:ℝ),(KSParameterSetup.compute v).value 7] := by
  apply argument_valid
  rw [KSParameterSetup.compute_value]
  exact ne_of_gt (KSFullManuscriptParameters.movementStep_pos
    (KSManuscriptInputPolynomialParameters.labels_pos v hd hp)
    (Real.sqrt_pos.mpr (epsilon_pos v hd hp))
    (KSFullManuscriptAlgorithm.taylorBudget_pos v
      (KSManuscriptInputPolynomialParameters.labels_pos v hd hp) (epsilon_pos v hd hp)))

theorem eighth_argument_valid (v : Fin N → Fin d → ℂ) (hd : 0<d)
    (hp : (∑i,KSRankOne.atom (v i))=1) :
    (argument 100).Valid ![(N:ℝ),(KSParameterSetup.compute v).value 13] := by
  apply argument_valid
  rw [KSParameterSetup.compute_value]
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  exact ne_of_gt (KSEighthManuscriptParameters.movementStep_pos v
    (KSManuscriptInputPolynomialParameters.labels_pos v hd hp)
    (Real.sqrt_pos.mpr (epsilon_pos v hd hp))
    (ksRegularizerScale_pos (n := Fin d) (epsilon_pos v hd hp)) hd)

end MatrixSpencer.RealRAM.KSHorizonSetup
