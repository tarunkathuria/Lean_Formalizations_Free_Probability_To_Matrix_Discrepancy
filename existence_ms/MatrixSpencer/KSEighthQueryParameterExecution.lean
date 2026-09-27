import MatrixSpencer.KSEighthCountedHessian

/-! The state-dependent eighth query mesh and tolerance use a bounded scalar
program after reading the precomputed input Taylor budget. This accounts for
the parameter arithmetic charged by the counted Hessian at each live face. -/
noncomputable section
namespace MatrixSpencer.KSEighthQueryParameterExecution
open RealRAM

inductive Reg where
  | dimension | budget | precision | root | mesh | tolerance
  deriving DecidableEq, Fintype

def rootExpr : Expr Reg :=
  .sqrt (.div (.input .precision) (.mul (.input .dimension) (.add (.input .budget) (.constant 1))))
def toleranceExpr : Expr Reg :=
  .div (.mul (.input .precision) (.mul (.input .mesh) (.input .mesh)))
    (.mul (.constant 4) (.input .dimension))
def program : Program Reg :=
  .seq (.assign .root rootExpr)
    (.seq (.branchLE (.input .root) (.constant (1/32))
      (.assign .mesh (.input .root)) (.assign .mesh (.constant (1/32))))
      (.assign .tolerance toleranceExpr))
def input (k : ℕ) (M η : ℝ) : Reg → ℝ
  | .dimension => k
  | .budget => M
  | .precision => η
  | _ => 0

theorem program_bound : program.bound≤60 := by
  norm_num [program,rootExpr,toleranceExpr,Program.bound,Expr.cost]

theorem program_values (k : ℕ) (M η : ℝ) :
    program.run (input k M η) .mesh=KSNumericalHessian.mesh k (1/32) M η ∧
    program.run (input k M η) .tolerance=KSNumericalHessian.valueTolerance k (1/32) M η := by
  by_cases h : Real.sqrt (η/((k:ℝ)*(M+1)))≤1/32
  · simp only [one_div] at h
    simp [program,rootExpr,toleranceExpr,Program.run,Expr.eval,input,h,
      KSNumericalHessian.mesh,KSNumericalHessian.valueTolerance,min_eq_right h,pow_two]
  · have h' : (1/32:ℝ)≤Real.sqrt (η/((k:ℝ)*(M+1))) := le_of_lt (lt_of_not_ge h)
    simp only [one_div] at h h'
    simp [program,rootExpr,toleranceExpr,Program.run,Expr.eval,input,h,
      KSNumericalHessian.mesh,KSNumericalHessian.valueTolerance,min_eq_left h',pow_two]

theorem program_safe (k : ℕ) (hk : 0<k) {M η : ℝ} (hM : 0≤M) (hη : 0≤η) :
    program.Safe (input k M η) := by
  have hk' : (0:ℝ)<k := Nat.cast_pos.mpr hk
  have hden : (0:ℝ)<(k:ℝ)*(M+1) := by positivity
  have hM0 : M+1≠0 := by linarith
  simp [program,rootExpr,toleranceExpr,Program.Safe,Program.run,Expr.Valid,Expr.eval,input,
    hk.ne',hM0,div_nonneg hη hden.le]
  split_ifs <;> simp [input,hk.ne']

theorem execution (k : ℕ) (hk : 0<k) {M η : ℝ} (hM : 0≤M) (hη : 0≤η) :
    ∃c≤60,Program.Executes program (input k M η) (program.run (input k M η)) c ∧
      program.run (input k M η) .mesh=KSNumericalHessian.mesh k (1/32) M η ∧
      program.run (input k M η) .tolerance=KSNumericalHessian.valueTolerance k (1/32) M η := by
  obtain ⟨c,hc,he⟩ := Program.safe_execution_bounded program (input k M η) (program_safe k hk hM hη)
  exact ⟨c,hc.trans program_bound,he,program_values k M η⟩

end MatrixSpencer.KSEighthQueryParameterExecution
