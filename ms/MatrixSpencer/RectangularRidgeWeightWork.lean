import MatrixSpencer.RectangularRidgeRateArithmetic

/-! A primitive execution certificate for the comparison-tuned Tsallis weight.
All three root chains, loads, constants and safe field operations are counted.
The power register is the integer value supplied by the proved tuning scan. -/
noncomputable section
namespace MatrixSpencer.RectangularRidgeWeightWork
open RealRAM RectangularRidgeRateArithmetic RectangularRidgePrimitiveParameters RectangularRidgeTuning

def registers (N D : ℕ) (hN : 1≤N) : Fin 3 → ℝ := ![N,D,order N D hN]
@[simp] theorem registers_zero (N D : ℕ) (hN : 1≤N) : registers N D hN 0=(N:ℝ) := rfl
@[simp] theorem registers_one (N D : ℕ) (hN : 1≤N) : registers N D hN 1=(D:ℝ) := rfl
@[simp] theorem registers_two (N D : ℕ) (hN : 1≤N) : registers N D hN 2=(order N D hN:ℝ) := rfl

def reciprocal : Expr (Fin 3) := .div (.constant 1) (.input 2)
def numerator (m : ℕ) : Expr (Fin 3) :=
  .mul (.mul (.sub (.constant 1) reciprocal) (rootExpr (.constant 4096) m))
    (.div (.input 0) (rootExpr (.input 0) m))
def denominator (m : ℕ) : Expr (Fin 3) := .mul reciprocal (rootExpr (.input 1) m)
def expression (m : ℕ) : Expr (Fin 3) := .sqrt (.div (numerator m) (denominator m))

theorem expression_cost (m : ℕ) : (expression m).cost=3*m+18 := by
  simp [expression,numerator,denominator,reciprocal,Expr.cost,rootExpr_cost]
  omega

theorem expression_eval {N D : ℕ} (hN : 1≤N) (hND : N≤D) :
    (expression (depth N D hN)).eval (registers N D hN)=weight N D hN := by
  rw [←RectangularRidgeArithmeticWeight.evaluate_eq_weight hN hND]
  simp only [expression,numerator,denominator,reciprocal,Expr.eval,rootExpr_eval,
    registers_zero,registers_one,registers_two,Rat.cast_one,Rat.cast_ofNat,
    RectangularRidgeArithmeticWeight.evaluate]

theorem expression_valid {N D : ℕ} (hN : 1≤N) (hND : N≤D) :
    (expression (depth N D hN)).Valid (registers N D hN) := by
  have hn : (0:ℝ)<N := by exact_mod_cast (by omega : 0<N)
  have hd : (0:ℝ)<D := by exact_mod_cast (by omega : 0<D)
  have hp : (2:ℝ)≤order N D hN := by exact_mod_cast order_two_le N D hN
  have hp0 : (0:ℝ)<order N D hN := by linarith
  have hr (x : ℝ) (hx : 0<x) : 0<RectangularRidgeArithmeticWeight.root (depth N D hN) x := by
    rw [RectangularRidgeArithmeticWeight.root_eq_rpow _ hx.le]
    exact Real.rpow_pos_of_pos hx _
  have hi : reciprocal.Valid (registers N D hN) := ⟨trivial,trivial,hp0.ne'⟩
  have hnr := rootExpr_valid (.input 0) (registers N D hN) trivial hn.le (depth N D hN)
  have hdr := rootExpr_valid (.input 1) (registers N D hN) trivial hd.le (depth N D hN)
  have hcr := rootExpr_valid (.constant 4096) (registers N D hN) trivial
    (by norm_num [Expr.eval]) (depth N D hN)
  have hden : 0<(denominator (depth N D hN)).eval (registers N D hN) := by
    simp only [denominator,reciprocal,Expr.eval,rootExpr_eval,registers_two,registers_one,Rat.cast_one]
    exact mul_pos (one_div_pos.mpr hp0) (hr D hd)
  have hnum : 0≤(numerator (depth N D hN)).eval (registers N D hN) := by
    simp only [numerator,reciprocal,Expr.eval,rootExpr_eval,registers_zero,registers_two,Rat.cast_one,Rat.cast_ofNat]
    have hb : 1/(order N D hN:ℝ)≤1/2 := one_div_le_one_div_of_le (by norm_num) hp
    exact mul_nonneg (mul_nonneg (by linarith) (hr 4096 (by norm_num)).le)
      (div_pos hn (hr N hn)).le
  refine ⟨⟨?_,?_,hden.ne'⟩,?_⟩
  · refine ⟨⟨⟨trivial,hi⟩,hcr⟩,⟨trivial,hnr,?_⟩⟩
    simpa only [rootExpr_eval,Expr.eval,registers_zero] using (hr N hn).ne'
  · exact ⟨hi,hdr⟩
  · exact div_nonneg hnum hden.le

theorem expression_executes {N D : ℕ} (hN : 1≤N) (hND : N≤D) :
    Expr.Executes (registers N D hN) (expression (depth N D hN))
      (weight N D hN) (3*depth N D hN+18) := by
  have hh := Expr.executes_of_valid _ _ (expression_valid hN hND)
  simpa only [expression_eval hN hND,expression_cost] using hh

theorem operation_budget {N D : ℕ} (hN : 1≤N) :
    (expression (depth N D hN)).cost≤3*D+21 := by
  rw [expression_cost]
  have hh := depth_le N D hN
  omega

end MatrixSpencer.RectangularRidgeWeightWork
