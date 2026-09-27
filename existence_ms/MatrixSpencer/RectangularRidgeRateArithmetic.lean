import MatrixSpencer.RectangularRidgeUniformResponse
import MatrixSpencer.RectangularRidgeArithmeticWeight
import MatrixSpencer.RealRAMCircuit

/-! Primitive evaluation of the actual uniform epoch rate and duration.
The registers contain the original count, the integer power returned by the
tuning scan, and the computed weight. Only scalar roots and field operations
occur; no logarithm or real-power evaluation is charged as an oracle. -/

noncomputable section
namespace MatrixSpencer.RectangularRidgeRateArithmetic
open RealRAM RectangularRidgePrimitiveParameters RectangularRidgeTuning

def rootExpr {ι : Type*} (e : Expr ι) : ℕ → Expr ι
  | 0 => e
  | m+1 => .sqrt (rootExpr e m)

theorem rootExpr_eval {ι : Type*} (e : Expr ι) (v : ι → ℝ) (m : ℕ) :
    (rootExpr e m).eval v=RectangularRidgeArithmeticWeight.root m (e.eval v) := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [rootExpr,Expr.eval,ih,RectangularRidgeArithmeticWeight.root]

theorem rootExpr_cost {ι : Type*} (e : Expr ι) (m : ℕ) : (rootExpr e m).cost=e.cost+m := by
  induction m with
  | zero => simp [rootExpr]
  | succ m ih => simp [rootExpr,Expr.cost,ih]; omega

theorem root_nonneg (m : ℕ) {x : ℝ} (hx : 0≤x) : 0≤RectangularRidgeArithmeticWeight.root m x := by
  rw [RectangularRidgeArithmeticWeight.root_eq_rpow m hx]
  exact Real.rpow_nonneg hx _

theorem rootExpr_valid {ι : Type*} (e : Expr ι) (v : ι → ℝ)
    (he : e.Valid v) (hx : 0≤e.eval v) (m : ℕ) : (rootExpr e m).Valid v := by
  induction m with
  | zero => exact he
  | succ m ih => exact ⟨ih,by rw [rootExpr_eval]; exact root_nonneg m hx⟩

def registers (N D : ℕ) (hN : 1≤N) : Fin 3 → ℝ := ![N,order N D hN,weight N D hN]

@[simp] theorem registers_zero (N D : ℕ) (hN : 1≤N) : registers N D hN 0=(N:ℝ) := rfl
@[simp] theorem registers_one (N D : ℕ) (hN : 1≤N) : registers N D hN 1=(order N D hN:ℝ) := rfl
@[simp] theorem registers_two (N D : ℕ) (hN : 1≤N) : registers N D hN 2=weight N D hN := rfl

def rateExpr (m : ℕ) : Expr (Fin 3) :=
  .add (.constant 3) (.div
    (.mul (.mul (.constant 6) (rootExpr (.constant 4096) m)) (.sqrt (.input 0)))
    (.mul (.mul (.input 2) (.div (.constant 1) (.input 1))) (rootExpr (.input 0) m)))

def durationExpr (m : ℕ) : Expr (Fin 3) := .div (.constant 1) (rateExpr m)

theorem rateExpr_cost (m : ℕ) : (rateExpr m).cost=2*m+16 := by
  simp [rateExpr,Expr.cost,rootExpr_cost]
  omega

theorem durationExpr_cost (m : ℕ) : (durationExpr m).cost=2*m+18 := by
  simp [durationExpr,Expr.cost,rateExpr_cost]
  omega

theorem rateExpr_eval {N D : ℕ} (hN : 1≤N) :
    (rateExpr (depth N D hN)).eval (registers N D hN)=
      RectangularRidgeUniformResponse.coefficient N D hN+1 := by
  have hn : (0:ℝ)<N := by exact_mod_cast (by omega : 0<N)
  have hr (x : ℝ) (hx : 0≤x) : RectangularRidgeArithmeticWeight.root (depth N D hN) x=
      x^exponent N D hN := by
    rw [RectangularRidgeArithmeticWeight.root_eq_rpow _ hx]
    simp [exponent,order]
  simp only [rateExpr,Expr.eval,rootExpr_eval,registers_zero,registers_one,registers_two,
    Rat.cast_ofNat,Rat.cast_one]
  change 3+6*RectangularRidgeArithmeticWeight.root (depth N D hN) 4096*Real.sqrt (N:ℝ)/
    (weight N D hN*(1/(order N D hN:ℝ))*RectangularRidgeArithmeticWeight.root (depth N D hN) N)=_
  rw [hr 4096 (by norm_num),hr N hn.le,
    RectangularRidgeUniformResponse.coefficient,RectangularParameters.globalResponseCoefficient_eq,
    Real.rpow_sub hn,←Real.sqrt_eq_rpow]
  change 3+6*(4096:ℝ)^exponent N D hN*Real.sqrt (N:ℝ)/
    (weight N D hN*exponent N D hN*(N:ℝ)^exponent N D hN)=_
  ring

theorem durationExpr_eval {N D : ℕ} (hN : 1≤N) :
    (durationExpr (depth N D hN)).eval (registers N D hN)=
      RectangularRidgeUniformResponse.duration N D hN := by
  simp only [durationExpr,Expr.eval,Rat.cast_one,rateExpr_eval]
  rfl

theorem rateExpr_valid {N D : ℕ} (hN : 1≤N) (hND : N≤D) :
    (rateExpr (depth N D hN)).Valid (registers N D hN) := by
  have hn : (0:ℝ)<N := by exact_mod_cast (by omega : 0<N)
  have hp : (0:ℝ)<order N D hN := by exact_mod_cast (by have := order_two_le N D hN; omega : 0<order N D hN)
  have ht := weight_positive hN hND
  have hr : 0<RectangularRidgeArithmeticWeight.root (depth N D hN) (N:ℝ) := by
    rw [RectangularRidgeArithmeticWeight.root_eq_rpow _ hn.le]
    exact Real.rpow_pos_of_pos hn _
  refine ⟨trivial,⟨?_,?_,?_⟩⟩
  · exact ⟨⟨trivial,rootExpr_valid (.constant 4096) (registers N D hN) trivial (by norm_num [Expr.eval]) _⟩,⟨trivial,hn.le⟩⟩
  · exact ⟨⟨trivial,⟨trivial,trivial,hp.ne'⟩⟩,rootExpr_valid (.input 0) (registers N D hN) trivial hn.le _⟩
  · simp only [Expr.eval,registers_two,registers_one,Rat.cast_one,rootExpr_eval,registers_zero]
    change weight N D hN*(1/(order N D hN:ℝ))*RectangularRidgeArithmeticWeight.root (depth N D hN) N≠0
    positivity

theorem durationExpr_valid {N D : ℕ} (hN : 1≤N) (hND : N≤D) :
    (durationExpr (depth N D hN)).Valid (registers N D hN) := by
  refine ⟨trivial,rateExpr_valid hN hND,?_⟩
  rw [rateExpr_eval]
  have hh := RectangularRidgeUniformResponse.coefficient_two_le hN hND
  linarith

theorem durationExpr_executes {N D : ℕ} (hN : 1≤N) (hND : N≤D) :
    Expr.Executes (registers N D hN) (durationExpr (depth N D hN))
      (RectangularRidgeUniformResponse.duration N D hN) (2*depth N D hN+18) := by
  have hh := Expr.executes_of_valid _ _ (durationExpr_valid hN hND)
  simpa only [durationExpr_eval,durationExpr_cost] using hh

theorem duration_operation_budget {N D : ℕ} (hN : 1≤N) :
    (durationExpr (depth N D hN)).cost≤2*D+20 := by
  rw [durationExpr_cost]
  have hh := depth_le N D hN
  omega

end MatrixSpencer.RectangularRidgeRateArithmetic
