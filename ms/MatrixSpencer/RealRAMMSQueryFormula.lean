import MatrixSpencer.RealRAMPositiveFormula
import MatrixSpencer.MSManuscriptPolynomialQueryCurvature

/-! Fixed primitive scalar circuits for the unchanged square-MS covariance
second derivative cap and matched movement fourth derivative cap. The owner
dimension register may be zero; every division and square root is checked.
-/
open Matrix
noncomputable section
namespace MatrixSpencer.RealRAM.MSQueryFormula
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

abbrev Reg := Fin 4
abbrev E := Expr Reg
local instance : Add E := ⟨Expr.add⟩
local instance : Mul E := ⟨Expr.mul⟩
local instance : Div E := ⟨Expr.div⟩
def c (q : ℚ) : E := .constant q
def r (i : Reg) : E := .input i
def sq (a : E) := a*a
def fourth (a : E) := sq (sq a)
def root (a : E) := Expr.sqrt a
def least (a b : E) := minimumExpr a b

@[simp] theorem c_eval (q : ℚ) (v : Reg → ℝ) : (c q).eval v=q := rfl
@[simp] theorem r_eval (i : Reg) (v : Reg → ℝ) : (r i).eval v=v i := rfl
@[simp] theorem add_eval (a b : E) (v : Reg → ℝ) : (a+b).eval v=a.eval v+b.eval v := rfl
@[simp] theorem mul_eval (a b : E) (v : Reg → ℝ) : (a*b).eval v=a.eval v*b.eval v := rfl
@[simp] theorem div_eval (a b : E) (v : Reg → ℝ) : (a/b).eval v=a.eval v/b.eval v := rfl
@[simp] theorem sq_eval (a : E) (v : Reg → ℝ) : (sq a).eval v=(a.eval v)^2 := by simp [sq,pow_two]
@[simp] theorem fourth_eval (a : E) (v : Reg → ℝ) : (fourth a).eval v=(a.eval v)^4 := by
  simp [fourth]; ring
@[simp] theorem root_eval (a : E) (v : Reg → ℝ) : (root a).eval v=Real.sqrt (a.eval v) := rfl
@[simp] theorem least_eval (a b : E) (v : Reg → ℝ) :
    (least a b).eval v=min (a.eval v) (b.eval v) := minimumExpr_eval _ _ _

def input (R : ℝ) (k m d : ℕ) : Reg → ℝ := ![R,k,m,d]
@[simp] theorem input_zero (R : ℝ) (k m d : ℕ) : input R k m d 0=R := rfl
@[simp] theorem input_one (R : ℝ) (k m d : ℕ) : input R k m d 1=k := rfl
@[simp] theorem input_two (R : ℝ) (k m d : ℕ) : input R k m d 2=m := rfl
@[simp] theorem input_three (R : ℝ) (k m d : ℕ) : input R k m d 3=d := rfl

def denominator (a : E) := c 2*a+c 2*r 1*r 2+c 2*root (r 3)
def floor (a : E) := least (c 1) (sq (c 1/denominator a))
def value (a : E) := r 3*a*c 2+c 2*r 3*root (c 2*(c 4*sq (r 1)*sq (r 2)))+
  c 2*r 3*root (c 2)
def joint (q : ℚ) (a b : E) := value b*fourth (c q/floor a)
def direction := root (r 2)*r 2
def second := joint 20971520 (r 0) (r 0)*(c 1+c 2*joint 20971520 (r 0) (r 0))
def movementJoint := joint 83886080 (r 0+direction) (r 0+direction+direction)
def movementFourth := (movementJoint+c 6*sq movementJoint)*fourth (c 1+c 2*movementJoint)

theorem denominator_eval (a : E) (R : ℝ) (k m d : ℕ) :
    (denominator a).eval (input R k m d)=2*a.eval (input R k m d)+2*(k:ℝ)*m+2*Real.sqrt (d:ℝ) := by
  simp [denominator,input]

theorem floor_eval (a : E) (R : ℝ) (k m d : ℕ) :
    (floor a).eval (input R k m d)=
      MSManuscriptOptimizerFloorScaled.floor k d (a.eval (input R k m d)) 1 m := by
  simp [floor,denominator_eval,MSManuscriptOptimizerFloorScaled.floor]

theorem value_eval (a : E) (R : ℝ) (k m d : ℕ) :
    (value a).eval (input R k m d)=
      MSManuscriptComplexValueBoundScaled.valueCap (Fin k) (Fin d) (a.eval (input R k m d)) 1 m := by
  simp [value,input,MSManuscriptComplexValueBoundScaled.valueCap,KSComplexObjectiveBound.valueCap]

theorem denominator_valid (a : E) (R : ℝ) (k m d : ℕ) (ha : a.Valid (input R k m d)) :
    (denominator a).Valid (input R k m d) := by
  simp only [denominator, HAdd.hAdd, HMul.hMul, Add.add, Mul.mul, Expr.Valid, c, r, root,
    Expr.eval, input, Matrix.cons_val, Matrix.cons_val_zero, Matrix.head_cons,
    Matrix.cons_val_succ, Matrix.head_fin_const]
  exact ⟨⟨⟨trivial,ha⟩,⟨⟨trivial,trivial⟩,trivial⟩⟩,⟨trivial,trivial,Nat.cast_nonneg d⟩⟩

theorem floor_valid (a : E) (R : ℝ) (k m d : ℕ)
    (ha : a.Valid (input R k m d)) (ha0 : 0 ≤ a.eval (input R k m d)) (hd : 0 < d) :
    (floor a).Valid (input R k m d) := by
  have hden : (denominator a).eval (input R k m d) ≠ 0 := by
    rw [denominator_eval]
    have hs := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hd)
    positivity
  have hq : (c 1/denominator a).Valid (input R k m d) :=
    ⟨trivial,denominator_valid a R k m d ha,hden⟩
  exact minimumExpr_valid _ _ _ trivial ⟨hq,hq⟩

theorem value_valid (a : E) (R : ℝ) (k m d : ℕ) (ha : a.Valid (input R k m d)) :
    (value a).Valid (input R k m d) := by
  have hs : (root (c 2*(c 4*sq (r 1)*sq (r 2)))).Valid (input R k m d) := by
    simp only [root, c, sq, r, HMul.hMul, Mul.mul, Expr.Valid, Expr.eval,
      input_one, input_two, true_and, Rat.cast_ofNat]
    change (0:ℝ) ≤ 2*(4*((k:ℝ)*(k:ℝ))*((m:ℝ)*(m:ℝ)))
    positivity
  have htwo : (root (c 2)).Valid (input R k m d) := by norm_num [root,c,Expr.Valid,Expr.eval]
  exact ⟨⟨⟨⟨trivial,ha⟩,trivial⟩,⟨⟨trivial,trivial⟩,hs⟩⟩,⟨⟨trivial,trivial⟩,htwo⟩⟩

theorem joint_valid (q : ℚ) (a b : E) (R : ℝ) (k m d : ℕ)
    (ha : a.Valid (input R k m d)) (ha0 : 0 ≤ a.eval (input R k m d))
    (hb : b.Valid (input R k m d)) (hd : 0 < d) :
    (joint q a b).Valid (input R k m d) := by
  have hf := floor_valid a R k m d ha ha0 hd
  have hfn : (floor a).eval (input R k m d) ≠ 0 := by
    rw [floor_eval]
    exact (MSManuscriptOptimizerFloorScaled.floor_pos hd (Nat.cast_nonneg m) ha0 (by norm_num)).ne'
  have hdiv : (c q/floor a).Valid (input R k m d) := ⟨trivial,hf,hfn⟩
  exact ⟨value_valid b R k m d hb,⟨⟨hdiv,hdiv⟩,⟨hdiv,hdiv⟩⟩⟩

theorem second_valid (R : ℝ) (k m d : ℕ) (hR : 0 ≤ R) (hd : 0 < d) :
    second.Valid (input R k m d) := by
  have hj := joint_valid 20971520 (r 0) (r 0) R k m d trivial hR trivial hd
  exact ⟨hj,trivial,trivial,hj⟩

theorem movementFourth_valid (R : ℝ) (k m d : ℕ) (hR : 0 ≤ R) (hd : 0 < d) :
    movementFourth.Valid (input R k m d) := by
  have hb : direction.Valid (input R k m d) := ⟨⟨trivial,Nat.cast_nonneg m⟩,trivial⟩
  have hb0 : 0 ≤ (r 0+direction).eval (input R k m d) := by simp [direction,input]; positivity
  have hj := joint_valid 83886080 (r 0+direction) (r 0+direction+direction) R k m d
    ⟨trivial,hb⟩ hb0 ⟨⟨trivial,hb⟩,hb⟩ hd
  have hsum : (c 1+c 2*movementJoint).Valid (input R k m d) := ⟨trivial,trivial,hj⟩
  exact ⟨⟨hj,trivial,hj,hj⟩,⟨⟨hsum,hsum⟩,⟨hsum,hsum⟩⟩⟩

theorem second_eval (R : ℝ) (k m d : ℕ) : second.eval (input R k m d)=
    MSManuscriptGammaInputBoundScaled.secondCap k d R 1 (1/8192) m := by
  have hj : (joint 20971520 (r 0) (r 0)).eval (input R k m d)=
      MSManuscriptGammaInputBoundScaled.jointCap k d R 1 (1/8192) m := by
    simp only [joint,mul_eval,fourth_eval,div_eval,c_eval,floor_eval,value_eval,r_eval,input_zero,Rat.cast_ofNat]
    unfold MSManuscriptGammaInputBoundScaled.jointCap MSManuscriptAffineJointBoundsScaled.jointCap
      MSManuscriptComplexSourceDomain.radius
    ring
  simp only [second,mul_eval,add_eval,c_eval,hj,Rat.cast_ofNat]
  unfold MSManuscriptGammaInputBoundScaled.secondCap
  ring

theorem movementFourth_eval (R : ℝ) (k m d : ℕ) : movementFourth.eval (input R k m d)=
    MSManuscriptMovementDrift.movementBudget m k d R 1 (1/8192) := by
  have hb : direction.eval (input R k m d)=MSManuscriptLDLMoments.directionCap m 1 := by
    simp [direction,input,MSManuscriptLDLMoments.directionCap]
  have hj : movementJoint.eval (input R k m d)=
      MSManuscriptMatchedFourth.jointBudget (Fin k) (Fin d)
        (R+MSManuscriptLDLMoments.directionCap m 1) (MSManuscriptLDLMoments.directionCap m 1)
        1 ((1/8192)/2) m := by
    simp only [movementJoint,joint,mul_eval,fourth_eval,div_eval,c_eval,floor_eval,value_eval,
      add_eval,r_eval,hb,input_zero,Rat.cast_ofNat]
    unfold MSManuscriptMatchedFourth.jointBudget MSManuscriptMatchedJointBounds.jointCap
      MSManuscriptMatchedFourth.densityFloor MSManuscriptMatchedComplex.radius
      MSManuscriptComplexSourceDomain.radius
    simp only [Fintype.card_fin]
    ring
  simp only [movementFourth,mul_eval,add_eval,c_eval,sq_eval,fourth_eval,hj,Rat.cast_ofNat]
  unfold MSManuscriptMovementDrift.movementBudget MSManuscriptMatchedInterval.fourthBudget
    MSManuscriptMatchedFourth.fourthBudget
  ring

theorem second_executes (R : ℝ) (k m d : ℕ) (hR : 0 ≤ R) (hd : 0 < d) :
    Expr.Executes (input R k m d) second
      (MSManuscriptGammaInputBoundScaled.secondCap k d R 1 (1/8192) m) second.cost := by
  rw [← second_eval]
  exact Expr.executes_of_valid _ _ (second_valid R k m d hR hd)

theorem movementFourth_executes (R : ℝ) (k m d : ℕ) (hR : 0 ≤ R) (hd : 0 < d) :
    Expr.Executes (input R k m d) movementFourth
      (MSManuscriptMovementDrift.movementBudget m k d R 1 (1/8192)) movementFourth.cost := by
  rw [← movementFourth_eval]
  exact Expr.executes_of_valid _ _ (movementFourth_valid R k m d hR hd)

theorem second_cost : second.cost ≤ 2000000 := by
  norm_num [second,joint,value,fourth,sq,floor,least,minimumExpr,denominator,c,r,root,Expr.cost]

theorem movementFourth_cost : movementFourth.cost ≤ 2000000 := by
  norm_num [movementFourth,movementJoint,joint,value,fourth,sq,floor,least,minimumExpr,
    denominator,direction,c,r,root,Expr.cost]

end MatrixSpencer.RealRAM.MSQueryFormula
