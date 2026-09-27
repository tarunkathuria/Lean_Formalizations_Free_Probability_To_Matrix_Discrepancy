import MatrixSpencer.RealRAMMSCovariance
import SimpleMS.CountedSpectralSampler
import MatrixSpencer.MSManuscriptNumericalEpochLedger

/-! Counted actual square-walk movement and ledger update. The computation
materializes the owner, high-space projection covariance, selected EVD-frame increment,
threshold rounding, reduced owner withdrawal and every stored scalar ledger.
The categorical draw itself is supplied separately and is not charged here. -/
open Matrix
open scoped BigOperators
noncomputable section
namespace MatrixSpencer.MSCountedMovement
open RealRAM
open RealRAM.JacobiIteration (Counted Mat)
open MSManuscriptNumericalEpochLedger
attribute [local instance] Classical.propDecidable
variable {N : ℕ}
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

def pointExpr : Expr (Fin 3) := .add (.input 0) (.mul (.input 1) (.input 2))
@[simp] theorem point_eval (x h u : ℝ) : pointExpr.eval ![x,h,u]=x+h*u := by
  norm_num [pointExpr,Expr.eval,Matrix.cons_val_two]

def point (x u : MSResponse.Space N) (h : ℝ) : Counted (MSResponse.Space N) :=
  ⟨WithLp.toLp 2 (fun i=>pointExpr.eval ![x i,h,u i]),10*N+2⟩
@[simp] theorem point_value (x u : MSResponse.Space N) (h : ℝ) :
    (point x u h).value=x+h • u := by
  ext i
  simp [point,point_eval]

def roundScalar (ε x : ℝ) : Counted ℝ :=
  let a:=KSCappedSimplex.absolute x
  ⟨if 1-ε≤a.value then (if 0≤x then 1 else -1) else x,a.cost+12⟩
@[simp] theorem roundScalar_value (ε x : ℝ) :
    (roundScalar ε x).value=ThresholdRounding.roundScalar ε x := by
  simp only [roundScalar,KSCappedSimplex.absolute_value,
    ThresholdRounding.roundScalar,ThresholdRounding.boundarySign]

theorem roundScalar_cost (ε x : ℝ) : (roundScalar ε x).cost≤26 := by
  have h:=KSCappedSimplex.absolute_cost x
  dsimp only [roundScalar]
  omega

def round (ε : ℝ) (x : MSResponse.Space N) : Counted (MSResponse.Space N) :=
  ⟨WithLp.toLp 2 (fun i=>(roundScalar ε (x i)).value),
    (∑i,(roundScalar ε (x i)).cost)+5*N+2⟩
@[simp] theorem round_value (ε : ℝ) (x : MSResponse.Space N) :
    (round ε x).value=WithLp.toLp 2 (ThresholdRounding.roundVector ε (WithLp.ofLp x)) := by
  ext i
  simp [round,roundScalar_value,ThresholdRounding.roundVector]

theorem round_cost (ε : ℝ) (x : MSResponse.Space N) : (round ε x).cost≤31*N+2 := by
  have h:=Finset.sum_le_sum (fun i (_ : i∈Finset.univ)=>roundScalar_cost ε (x i))
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at h
  dsimp only [round]
  omega

def roundingLoss (x y : MSResponse.Space N) : Counted ℝ :=
  ⟨∑i,(KSCappedSimplex.absolute (x i-y i)).value,
    (∑i,(KSCappedSimplex.absolute (x i-y i)).cost)+6*N+1⟩
@[simp] theorem roundingLoss_value (x y : MSResponse.Space N) :
    (roundingLoss x y).value=∑i,|x i-y i| := by
  simp only [roundingLoss,KSCappedSimplex.absolute_value]

theorem roundingLoss_cost (x y : MSResponse.Space N) : (roundingLoss x y).cost≤20*N+1 := by
  have h:=Finset.sum_le_sum (fun i (_ : i∈Finset.univ)=>KSCappedSimplex.absolute_cost (x i-y i))
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at h
  dsimp only [roundingLoss]
  omega

def update (ε : ℝ) (s : State N) (h : ℝ) (Q : Mat N) (u : MSResponse.Space N) : Counted (State N) :=
  let p:=point s.point u h
  let r:=round ε p.value
  let a:=MSCovariance.advance s.owner Q h
  let tr:=MSSampling.traceExpr.eval (JacobiIteration.entries Q)
  let loss:=roundingLoss r.value p.value
  let c:=point s.centered u h
  ⟨{s with
      point:=r.value
      owner:=a.value
      time:=s.time+h^2
      variance:=s.variance+h^2*tr
      rounding:=s.rounding+loss.value
      centered:=c.value},
    p.cost+r.cost+a.cost+(MSSampling.traceExpr (k:=N)).cost+loss.cost+c.cost+
      30*(N+s.owner.dim+1)^2+30⟩

theorem update_cost (ε : ℝ) (s : State N) (h : ℝ) (Q : Mat N) (u : MSResponse.Space N) :
    (update ε s h Q u).cost≤400*(N+s.owner.dim+1)^3 := by
  have hr:=round_cost ε (point s.point u h).value
  have ha:=MSCovariance.advance_cost s.owner Q h
  have hl:=roundingLoss_cost (round ε (point s.point u h).value).value (point s.point u h).value
  have hp : (N+s.owner.dim+1)^2≤(N+s.owner.dim+1)^3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hn : N≤(N+s.owner.dim+1)^3 := by
    have h:=Nat.pow_le_pow_right (n:=N+s.owner.dim+1) (by omega) (show 1≤3 by omega)
    simp only [pow_one] at h
    omega
  have h1 : 1≤(N+s.owner.dim+1)^3 := Nat.one_le_pow _ _ (by omega)
  dsimp only [update,point]
  rw [MSSampling.trace_cost]
  dsimp only [point] at hr hl
  omega

def afterMove (ε : ℝ) (s : State N) (h : ℝ) (z : Draws s) : Counted (State N) :=
  let p:=MSGammaTop.physical s.owner
  let q:=MSCovariance.covariance p.value s.point
  let u:=SimpleMS.CountedSpectralSampler.increment (samplingSpace s) z
  let r:=update ε s h q.value u.value
  ⟨r.value,p.cost+q.cost+u.cost+r.cost+6⟩

theorem afterMove_value (ε : ℝ) (s : State N) (h : ℝ) (z : Draws s) :
    (afterMove ε s h z).value=MSManuscriptNumericalEpochLedger.afterMove ε s h z := by
  simp only [afterMove,MSGammaTop.physical_value,MSCovariance.covariance_value,
    SimpleMS.CountedSpectralSampler.increment_value]
  simp only [update,point_value,round_value,roundingLoss_value,MSCovariance.advance_value,
    MSSampling.trace_eval]
  rfl

theorem afterMove_cost (ε : ℝ) (s : State N) (h : ℝ) (z : Draws s) :
    (afterMove ε s h z).cost≤4000*(N+s.owner.dim+1)^5 := by
  have hp:=MSGammaTop.physical_cost s.owner
  have hq:=MSCovariance.covariance_cost (MSGammaTop.physical s.owner).value s.point
  have hr:=update_cost ε s h
    (MSCovariance.covariance (MSGammaTop.physical s.owner).value s.point).value
    (SimpleMS.CountedSpectralSampler.increment (samplingSpace s) z).value
  have h3 : (N+s.owner.dim+1)^3≤(N+s.owner.dim+1)^5 := Nat.pow_le_pow_right (by omega) (by omega)
  have h5 : (N+1)^5≤(N+s.owner.dim+1)^5 := Nat.pow_le_pow_left (by omega) _
  have hn : N≤(N+s.owner.dim+1)^5 := by
    have hh := Nat.pow_le_pow_right (n:=N+s.owner.dim+1) (by omega) (show 1≤5 by omega)
    simp only [pow_one] at hh
    omega
  have h1 : 1≤(N+s.owner.dim+1)^5 := Nat.one_le_pow _ _ (by omega)
  dsimp only [SimpleMS.CountedSpectralSampler.increment] at hr
  simp only [afterMove,SimpleMS.CountedSpectralSampler.increment]
  omega

/-- All scalar point and ledger updates use additions and products, with
threshold decisions implemented by the explicit absolute-value program. -/
theorem point_execution (x h u : ℝ) : Expr.Executes ![x,h,u] pointExpr (x+h*u) 5 := by
  have hv : pointExpr.Valid ![x,h,u] := by simp [pointExpr,Expr.Valid]
  have he:=Expr.executes_of_valid _ _ hv
  rw [point_eval] at he
  exact he

end MatrixSpencer.MSCountedMovement
