import RadialKS.RuntimeRun
import Mathlib.Algebra.MvPolynomial.Eval

/-! An explicit polynomial for the complete deterministic execution bound.
The solver coefficient and degree are fixed before the dimensions vary. -/
noncomputable section
namespace RadialKS.RuntimePolynomial
open MatrixSpencer.KSPolynomialConvexSolver

/-- The dimension-only work formula, interpreted over any commutative semiring. -/
def recipe {R : Type*} [CommSemiring R] (c k : ℕ) (N d : R) : R :=
  let r := 10000*(1+22500*N^2)
  let j := 10000*(2*d+1)^2*(10*r)^4
  let D := 1+(j+3*j^2*(4*N))*(1+j*(4*N))^4
  let q := 256*(100*N^2)^2+128*N*D*(100*N^2)
  let s := 256*(100*N^2)^2+4*D*(100*N^2)
  let ah := 128*N*(100*N^2)*q
  let al := 8*(100*N^2)*s
  let H := 16*N*s+1
  let query := fun V => (15*N+4)+10000*(N+1)^2*(d+1)^2+
    1000000*(4*N+(d+d)+1)^9+(c:R)*(10000*(d+1)^4+V+1)^k
  let face := 60*(N+1)^3+query ah+2
  let direction := 50*(N+1)^2+N^2*(4*face+100*(N+1)+18)+1000*(N+1)^5+22
  let candidate := 50*(N+1)^3+8*N+1+query al+5
  let choice := 2*candidate+N+5
  let selection := (N+1)*query al+4*N^2+39*N+3
  let step := selection+direction+choice+10*N+30+50*N+7
  (12000100*(N+1)*(d+1)+8*H+100)+(44*N+4)+H*(step+2)+3*N+6

def polynomial (P : PolynomialSolver) : MvPolynomial (Fin 2) ℕ :=
  recipe P.coefficient P.degree (MvPolynomial.X 0) (MvPolynomial.X 1)

theorem recipe_eq_costBound (P : PolynomialSolver) (N d : ℕ) :
    recipe P.coefficient P.degree N d = RuntimeRun.costBound P N d := by
  rfl

theorem eval_polynomial (P : PolynomialSolver) (N d : ℕ) :
    MvPolynomial.eval ![N,d] (polynomial P) = RuntimeRun.costBound P N d := by
  rw [← recipe_eq_costBound]
  simp [polynomial, recipe]

/-- This asserts polynomiality as a polynomial identity, in addition to the
execution theorem's pointwise arithmetic bound. -/
theorem costBound_is_polynomial (P : PolynomialSolver) :
    ∃ q : MvPolynomial (Fin 2) ℕ, ∀ N d,
      MvPolynomial.eval ![N,d] q = RuntimeRun.costBound P N d :=
  ⟨polynomial P, eval_polynomial P⟩

open scoped BigOperators Matrix.Norms.L2Operator

/-- One polynomial, fixed before the input dimensions and entries are given,
bounds the complete execution returning the certified signing. -/
theorem polynomial_runtime_and_correctness (P : PolynomialSolver) :
    ∃ q : MvPolynomial (Fin 2) ℕ, ∀ (N d : ℕ) [Nonempty (Fin d)]
      (v : Fin N → Fin d → ℂ) (hd : 0 < d)
      (hp : ∑ i, MatrixSpencer.KSRankOne.atom (v i) = 1)
      (ε : ℝ), 0 ≤ ε → (∀ i, ‖MatrixSpencer.KSRankOne.atom (v i)‖ ≤ ε) →
      ∃ cost, RuntimeRun.Executes P v hd hp (Run.output P.solver v hd hp) cost ∧
        cost ≤ MvPolynomial.eval ![N,d] q ∧
        (∀ i, MatrixSpencer.IsSign (Run.output P.solver v hd hp i)) ∧
        ‖∑ i, Run.output P.solver v hd hp i • MatrixSpencer.KSRankOne.atom (v i)‖
          ≤ 35 * Real.sqrt ε := by
  refine ⟨polynomial P, ?_⟩
  intro N d _ v hd hp ε hε hsize
  rw [eval_polynomial]
  exact RuntimeRun.guarantee P v hd hp hε hsize

#print axioms polynomial_runtime_and_correctness

end RadialKS.RuntimePolynomial
