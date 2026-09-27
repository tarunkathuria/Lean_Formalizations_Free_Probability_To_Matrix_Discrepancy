import HigherRankKSRuntime.RuntimeWork
import MatrixSpencer.RealRAMJacobiRayleigh

/-! A comparison-and-increment program computes the finite epoch fuel.
The loop cap is one fixed polynomial in the input dimensions, chosen once
from the proved parameter envelope. It is independent of matrix entries. -/
noncomputable section
namespace HigherRankKSRuntime.RuntimeFuel
open AugmentedHigherRankKS.RuntimeParameters MatrixSpencer.RealRAM
open MatrixSpencer.RealRAM.JacobiIteration (Counted)

structure Cap where
  coefficient : ℕ
  degree : ℕ
  bound : ∀ (N d : ℕ) (p : Dimensions), p∈Domain →
    (N:ℝ)=p.N → (d:ℝ)=p.D → p.q≤4*p.D →
    eventBound p ≤ (coefficient*(1+N+d)^degree : ℕ)

def Cap.limit (c : Cap) (N d : ℕ) : ℕ := c.coefficient*(1+N+d)^c.degree

theorem cap_exists : Nonempty Cap := by
  obtain ⟨C,e,hC,hb⟩ := eventBound_poly.input_polynomial
  refine ⟨⟨⌈C⌉₊+1,e,?_⟩⟩
  intro N d p hp hN hd hq
  have hB := (hb p hp hq).1
  have hK : C≤(⌈C⌉₊+1:ℕ) := (Nat.le_ceil C).trans (by simp)
  have hbase : 0 ≤ 1+p.N+p.D := by linarith [hp.1,hp.2.1]
  have hh := hB.trans (mul_le_mul_of_nonneg_right hK (pow_nonneg hbase e))
  simpa only [←hN,←hd,Nat.cast_mul,Nat.cast_pow,Nat.cast_add,Nat.cast_one] using hh

/-- A fixed program parameter, selected from an input-independent proof. -/
def defaultCap : Cap := Classical.choice cap_exists

def compute (c : Cap) (N d : ℕ) (p : Dimensions) : Counted ℕ :=
  let out := JacobiRayleigh.ceilLoop (eventBound p) (c.limit N d)
  ⟨out.value+1,out.cost+4⟩

theorem compute_value (c : Cap) (N d : ℕ) (p : Dimensions) (hp : p∈Domain)
    (hN : (N:ℝ)=p.N) (hd : (d:ℝ)=p.D) (hq : p.q≤4*p.D) :
    (compute c N d p).value=RuntimeWork.fuel p := by
  have hc : eventBound p ≤ (c.limit N d:ℝ) := c.bound N d p hp hN hd hq
  simp only [compute,JacobiRayleigh.ceilLoop_exact _ _ hc,RuntimeWork.fuel]

theorem compute_cost (c : Cap) (N d : ℕ) (p : Dimensions) :
    (compute c N d p).cost=8*c.limit N d+7 := by
  simp only [compute,JacobiRayleigh.ceilLoop_cost]


def program (c : Cap) (N d : ℕ) : Program Ceiling.Register :=
  .seq (Ceiling.program (c.limit N d))
    (.assign .counter (.add (.input .counter) (.constant 1)))

def initial (p : Dimensions) : Ceiling.Register → ℝ
  | .argument => eventBound p
  | .counter => 0

theorem program_safe (c : Cap) (N d : ℕ) (p : Dimensions) :
    (program c N d).Safe (initial p) := ⟨Ceiling.safe _ _,⟨trivial,trivial⟩⟩

theorem program_bound (c : Cap) (N d : ℕ) :
    (program c N d).bound=8*c.limit N d+7 := by
  simp only [program,Program.bound,Ceiling.bound,Expr.cost]


theorem program_value (c : Cap) (N d : ℕ) (p : Dimensions) :
    (program c N d).run (initial p) .counter = ((compute c N d p).value:ℝ) := by
  simp only [program,Program.run,Expr.eval,Function.update_self,Rat.cast_one,
    compute,Nat.cast_add,Nat.cast_one]
  rw [JacobiRayleigh.ceilLoop_program]
  rfl

/-- The fuel value has a genuine execution in the existing primitive
real-arithmetic language. No ceiling instruction or real-to-integer oracle
is used. -/
theorem program_execution (c : Cap) (N d : ℕ) (p : Dimensions) (hp : p∈Domain)
    (hN : (N:ℝ)=p.N) (hd : (d:ℝ)=p.D) (hq : p.q≤4*p.D) :
    ∃ w k, Program.Executes (program c N d) (initial p) w k ∧
      w .counter=(RuntimeWork.fuel p:ℝ) ∧ k≤(compute c N d p).cost := by
  refine ⟨(program c N d).run (initial p),(program c N d).cost (initial p),
    Program.executes_of_safe _ _ (program_safe c N d p),?_,?_⟩
  · rw [program_value,compute_value c N d p hp hN hd hq]
  · rw [compute_cost,←program_bound]
    exact Program.cost_le_bound _ _

/-- Polynomial cost holds even before the input satisfies the mathematical
hypotheses; only the exact-output theorem uses those hypotheses. -/
theorem compute_polynomial (c : Cap) (N d : ℕ) (p : Dimensions) :
    ((compute c N d p).cost:ℝ)≤(8*c.coefficient+7:ℝ)*(1+N+d)^c.degree := by
  have hb : (1:ℝ)≤1+N+d := by linarith [Nat.cast_nonneg (α:=ℝ) N,Nat.cast_nonneg (α:=ℝ) d]
  have hp : (1:ℝ)≤(1+N+d:ℝ)^c.degree := one_le_pow₀ hb
  rw [compute_cost,Cap.limit]
  push_cast
  nlinarith

/-- Adding the executed ceiling program preserves the uniform polynomial
bound for the complete previously counted algorithm budget. -/
theorem total_with_fuel_polynomial (O : SDPValue.Solver) (c : Cap) :
    ∃ C : ℝ, ∃ e : ℕ, 0<C ∧ ∀ (N d k : ℕ) (p : Dimensions),
      p∈Domain → (N:ℝ)=p.N → (d:ℝ)=p.D → (k:ℝ)≤p.q → p.q≤4*p.D →
      ((RuntimeWork.totalWork O N d k p+(compute c N d p).cost):ℝ)≤C*(1+N+d)^e := by
  obtain ⟨C,e,hC,hb⟩ := RuntimeWork.uniform_polynomial O
  refine ⟨C+(8*c.coefficient+7),e+c.degree,by positivity,?_⟩
  intro N d k p hp hN hd hk hq
  have htotal := hb N d k p hp hN hd hk hq
  have hfuel := compute_polynomial c N d p
  have hbase : (1:ℝ)≤1+N+d := by linarith [Nat.cast_nonneg (α:=ℝ) N,Nat.cast_nonneg (α:=ℝ) d]
  have hp1 : (1+N+d:ℝ)^e≤(1+N+d:ℝ)^(e+c.degree) :=
    pow_le_pow_right₀ hbase (Nat.le_add_right e c.degree)
  have hp2 : (1+N+d:ℝ)^c.degree≤(1+N+d:ℝ)^(e+c.degree) :=
    pow_le_pow_right₀ hbase (Nat.le_add_left c.degree e)
  have h1 := mul_le_mul_of_nonneg_left hp1 hC.le
  have h2 := mul_le_mul_of_nonneg_left hp2 (by positivity : (0:ℝ)≤8*c.coefficient+7)
  push_cast
  nlinarith

end HigherRankKSRuntime.RuntimeFuel
