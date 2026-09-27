import MatrixSpencer.RectangularRidgeConvexValue

/-! Existence of an accurate-value specification, for a pure existence
corollary of the walk proof. This is not a polynomial solver or an executable
implementation of supremum evaluation. Runtime results retain the explicitly
permitted polynomial convex-solver contract. -/
open Set
open scoped InnerProductSpace
noncomputable section
namespace MatrixSpencer.RectangularRidgeExactValue
open RectangularRidgeConvexValue KSFullManuscriptAffinePSD

def value {β : Type} [Fintype β] {ℓ k : ℕ}
    (D : β → Data ℓ k) (c : Space ℓ) (offset : ℝ) : ℝ :=
  sSup ((fun x=>offset+⟪c,x⟫_ℝ) '' feasible D)

theorem value_eq_of_maximum {β : Type} [Fintype β] {ℓ k : ℕ}
    (D : β → Data ℓ k) (c : Space ℓ) (offset : ℝ)
    (x : Space ℓ) (hx : x∈feasible D)
    (hmax : ∀y∈feasible D,offset+⟪c,y⟫_ℝ≤offset+⟪c,x⟫_ℝ) :
    value D c offset=offset+⟪c,x⟫_ℝ := by
  have hh : IsGreatest ((fun y=>offset+⟪c,y⟫_ℝ) '' feasible D) (offset+⟪c,x⟫_ℝ) := by
    refine ⟨⟨x,hx,rfl⟩,?_⟩
    rintro z ⟨y,hy,rfl⟩
    exact hmax y hy
  exact hh.csSup_eq

def exactSolver : Solver where
  report D c offset _:=value D c offset
  accuracy D c offset ν hν x hx hmax:=by
    rw [value_eq_of_maximum D c offset x hx hmax,sub_self,abs_zero]
    exact hν.le

theorem solver_exists : Nonempty Solver := ⟨exactSolver⟩

end MatrixSpencer.RectangularRidgeExactValue
