import MatrixSpencer.RectangularRidgeResponseScalars
import MatrixSpencer.RectangularRidgeEpochWork
import MatrixSpencer.RectangularRidgeAcceptanceWork

/-! Actual scalar setup for the rectangular epoch. The original integer
comparison scan supplies the retained Tsallis depth and order. Its computed
weight is passed to the duration expression. Fixed scales and the literal
movement counter are evaluated by primitive circuits, with every reciprocal
and square-root domain justified from the original input. -/
open Matrix
noncomputable section
namespace MatrixSpencer.RectangularRidgeEpochSetup
open RealRAM
open RealRAM.JacobiIteration (Counted)
open RectangularRidgeEpochInput
variable {N d : ℕ} [Nonempty (Fin d)]
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
set_option exponentiation.threshold 2048

inductive Fixed where
  | margin | threshold | ridge | radius | tolerance | movements
  deriving DecidableEq, Fintype

def sizeExpr : Expr (Fin 3) := .add (.add (.input 0) (.input 1)) (.constant 2)
def expression : Fixed → Expr (Fin 3)
  | .margin=>.div (.constant 1) (.mul (.constant 16384) (.input 1))
  | .threshold=>.div (.constant 4096) (.sqrt (.input 2))
  | .ridge=>.div (.constant 1) (.input 0)
  | .radius=>.mul (.constant 3) (.mul sizeExpr sizeExpr)
  | .tolerance=>.constant (1/10000)
  | .movements=>.add (.mul (.constant ((2 : ℚ)^1080))
      (RectangularRidgeNumericalSetup.power sizeExpr 208)) (.constant 1)

def fixedInput (c : Config N d) : Fin 3 → ℝ := ![d,N,live c]
def specified (c : Config N d) : Fixed → ℝ
  | .margin=>margin N
  | .threshold=>threshold c
  | .ridge=>1/(d : ℝ)
  | .radius=>RectangularRidgeTangentParameters.radius ((d+N+2 : ℕ) : ℝ)
  | .tolerance=>RectangularRidgeTangentParameters.tolerance
  | .movements=>(RectangularRidgeEpochRun.count c : ℝ)

theorem fixed_eval (c : Config N d) (f : Fixed) :
    (expression f).eval (fixedInput c)=specified c f := by
  cases f with
  | margin=>simp [expression,Expr.eval,fixedInput,specified,margin]
  | threshold=>rfl
  | ridge=>simp [expression,Expr.eval,fixedInput,specified]
  | radius=>simp [expression,Expr.eval,sizeExpr,fixedInput,specified,
      RectangularRidgeTangentParameters.radius,pow_two]
  | tolerance=>norm_num [expression,Expr.eval,specified,RectangularRidgeTangentParameters.tolerance]
  | movements=>
    have hp : (RectangularRidgeNumericalSetup.power sizeExpr 208).eval (fixedInput c)=
        ((d : ℝ)+N+2)^208 := by rw [RectangularRidgeNumericalSetup.power_eval];rfl
    simp only [expression,Expr.eval,hp,Rat.cast_one,Rat.cast_pow,Rat.cast_ofNat,
      specified,RectangularRidgeEpochRun.count_eq,Nat.cast_add,Nat.cast_mul,
      Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one]

theorem fixed_valid (c : Config N d) (f : Fixed) : (expression f).Valid (fixedInput c) := by
  have hn : (0 : ℝ)<N := by exact_mod_cast (by have := c.count_pos; omega : 0<N)
  have hd : (0 : ℝ)<d := by exact_mod_cast (by have := c.rectangular; have := c.count_pos; omega : 0<d)
  have hl := live_pos c
  cases f with
  | margin=>exact ⟨trivial,⟨trivial,trivial⟩,mul_ne_zero (by norm_num [Expr.eval]) hn.ne'⟩
  | threshold=>exact ⟨trivial,⟨trivial,hl.le⟩,(Real.sqrt_pos.mpr hl).ne'⟩
  | ridge=>exact ⟨trivial,trivial,hd.ne'⟩
  | radius=>exact ⟨trivial,⟨⟨⟨trivial,trivial⟩,trivial⟩,⟨⟨trivial,trivial⟩,trivial⟩⟩⟩
  | tolerance=>trivial
  | movements=>exact ⟨⟨trivial,RectangularRidgeNumericalSetup.power_valid sizeExpr (fixedInput c)
      ⟨⟨trivial,trivial⟩,trivial⟩ 208⟩,trivial⟩

theorem fixed_executes (c : Config N d) (f : Fixed) :
    Expr.Executes (fixedInput c) (expression f) (specified c f) (expression f).cost := by
  rw [←fixed_eval]
  exact Expr.executes_of_valid _ _ (fixed_valid c f)

def fixedCircuit : Circuit (Fin 3) Fixed := ⟨expression⟩
theorem fixed_cost : fixedCircuit.cost≤8000 := by
  have he (f : Fixed) : (expression f).cost+1≤1300 := by
    cases f <;> norm_num [expression,Expr.cost,RectangularRidgeNumericalSetup.power_cost,sizeExpr]
  calc fixedCircuit.cost≤∑_f : Fixed,1300 := by
         unfold Circuit.cost
         exact Finset.sum_le_sum (fun f _=>he f)
       _≤8000 := by decide

structure Values where
  depth : ℕ
  order : ℕ
  theta : ℝ
  duration : ℝ
  numerical : RectangularRidgeNumericalSetup.Parameter → ℝ
  fixed : Fixed → ℝ

def setup (c : Config N d) : Counted Values :=
  let t:=RectangularRidgeResponseScalars.selected N d
  let theta:=(RectangularRidgeWeightWork.expression t.level).eval ![N,d,t.power]
  let dur:=(RectangularRidgeRateArithmetic.durationExpr t.level).eval ![N,t.power,theta]
  let numbers:=RectangularRidgeNumericalSetup.circuit.eval ![d,N]
  let extra:=fixedCircuit.eval (fixedInput c)
  ⟨⟨t.level,t.power,theta,dur,numbers,extra⟩,
    RectangularRidgeTuning.scanCost N d (d+1) RectangularRidgeTuning.initial+
    (RectangularRidgeWeightWork.expression t.level).cost+
    (RectangularRidgeRateArithmetic.durationExpr t.level).cost+
    RectangularRidgeNumericalSetup.circuit.cost+fixedCircuit.cost+30⟩

theorem setup_depth (c : Config N d) :
    (setup c).value.depth=RectangularRidgeTuning.depth N d c.count_pos :=
  RectangularRidgeResponseScalars.selected_level c.count_pos

theorem setup_order (c : Config N d) :
    (setup c).value.order=RectangularRidgeTuning.order N d c.count_pos :=
  RectangularRidgeResponseScalars.selected_power c.count_pos

theorem setup_theta (c : Config N d) :
    (setup c).value.theta=RectangularRidgePrimitiveParameters.weight N d c.count_pos := by
  simp only [setup,RectangularRidgeResponseScalars.selected_level c.count_pos,
    RectangularRidgeResponseScalars.selected_power c.count_pos]
  exact RectangularRidgeWeightWork.expression_eval c.count_pos c.rectangular

theorem setup_duration (c : Config N d) : (setup c).value.duration=duration c := by
  change (RectangularRidgeRateArithmetic.durationExpr
    (RectangularRidgeResponseScalars.selected N d).level).eval
      ![N,(RectangularRidgeResponseScalars.selected N d).power,(setup c).value.theta]=_
  rw [RectangularRidgeResponseScalars.selected_level c.count_pos,
    RectangularRidgeResponseScalars.selected_power c.count_pos,setup_theta]
  exact RectangularRidgeRateArithmetic.durationExpr_eval c.count_pos

theorem setup_numerical (c : Config N d) (p : RectangularRidgeNumericalSetup.Parameter) :
    (setup c).value.numerical p=RectangularRidgeNumericalSetup.specified
      (RectangularRidgeNumericalOptimizerFloor.size d N) p :=
  RectangularRidgeNumericalSetup.expression_eval p ![d,N]

theorem setup_fixed (c : Config N d) (p : Fixed) : (setup c).value.fixed p=specified c p :=
  fixed_eval c p

/-- Includes the scan, all root chains, thirteen numerical scales, six fixed
parameters, their stores and the duration-positive guard used by the loop. -/
theorem setup_cost (c : Config N d) : (setup c).cost≤10*d+30000 := by
  have hs:=RectangularRidgeTuning.scanCost_le N d (d+1) RectangularRidgeTuning.initial
  have hw:=RectangularRidgeWeightWork.operation_budget (D:=d) c.count_pos
  have hd:=RectangularRidgeRateArithmetic.duration_operation_budget (D:=d) c.count_pos
  have hn:=RectangularRidgeNumericalSetup.circuit_cost_le
  have hf:=fixed_cost
  simp only [setup,RectangularRidgeResponseScalars.selected_level c.count_pos]
  omega

end MatrixSpencer.RectangularRidgeEpochSetup
