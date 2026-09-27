import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Fin.VecNotation
import Lean.Elab.Tactic

/-! Formal polynomial representations of the displayed KS runtime bounds.
The solver coefficient and degree are fixed when the solver P is fixed.
The three polynomial variables are the original label count, physical
dimension, and retry count. The coefficient semiring is Nat. -/
noncomputable section
namespace MatrixSpencer.KSRuntimePolynomialRepresentation
open MvPolynomial
set_option maxRecDepth 16384
set_option maxHeartbeats 3200000

def Represented (f : ℕ → ℕ → ℕ → ℕ) : Prop :=
  ∃ p : MvPolynomial (Fin 3) ℕ, ∀ N d r, MvPolynomial.eval ![N,d,r] p=f N d r

namespace Represented

theorem constant (c : ℕ) : Represented (fun _ _ _ => c) := by
  refine ⟨C c,?_⟩
  intros
  simp

theorem labels : Represented (fun N _ _ => N) := by
  refine ⟨X 0,?_⟩
  intros
  simp

theorem dimension : Represented (fun _ d _ => d) := by
  refine ⟨X 1,?_⟩
  intros
  simp

theorem retries : Represented (fun _ _ r => r) := by
  refine ⟨X 2,?_⟩
  intros
  simp

theorem add {f g : ℕ → ℕ → ℕ → ℕ} (hf : Represented f) (hg : Represented g) :
    Represented (fun N d r => f N d r+g N d r) := by
  obtain ⟨p,hp⟩ := hf
  obtain ⟨q,hq⟩ := hg
  refine ⟨p+q,?_⟩
  intros
  simp [hp,hq]

theorem mul {f g : ℕ → ℕ → ℕ → ℕ} (hf : Represented f) (hg : Represented g) :
    Represented (fun N d r => f N d r*g N d r) := by
  obtain ⟨p,hp⟩ := hf
  obtain ⟨q,hq⟩ := hg
  refine ⟨p*q,?_⟩
  intros
  simp [hp,hq]

theorem pow {f : ℕ → ℕ → ℕ → ℕ} (hf : Represented f) (k : ℕ) :
    Represented (fun N d r => f N d r^k) := by
  obtain ⟨p,hp⟩ := hf
  refine ⟨p^k,?_⟩
  intros
  simp [hp]

end Represented

open Lean Meta Elab Tactic

/-- Reify only the syntactic arithmetic head. In particular a fixed exponent
275 becomes one polynomial power, without unfolding 275 multiplications. -/
syntax "ks_poly_cert" : tactic
elab_rules : tactic
  | `(tactic| ks_poly_cert) => do
    let goal ← getMainGoal
    let target ← instantiateMVars (← goal.getType)
    let f := target.getAppArgs.back!
    let head ← lambdaTelescope f fun _ body => pure body.consumeMData.getAppFn.constName?
    if head == some ``HAdd.hAdd || head == some ``Nat.add then
      evalTactic (← `(tactic| apply Represented.add <;> ks_poly_cert))
    else if head == some ``HMul.hMul || head == some ``Nat.mul then
      evalTactic (← `(tactic| apply Represented.mul <;> ks_poly_cert))
    else if head == some ``HPow.hPow || head == some ``Pow.pow || head == some ``Nat.pow then
      evalTactic (← `(tactic| apply Represented.pow <;> ks_poly_cert))
    else
      evalTactic (← `(tactic| first
        | exact Represented.labels
        | exact Represented.dimension
        | exact Represented.retries
        | exact Represented.constant _))

example : Represented (fun N d r => 3*N^275*(d+1)+r*7) := by ks_poly_cert

end MatrixSpencer.KSRuntimePolynomialRepresentation
