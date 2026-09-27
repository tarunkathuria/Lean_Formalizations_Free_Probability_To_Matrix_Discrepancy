import HigherRankKS.CubePotential

/-! Zero atoms can be taken to a cube endpoint without changing the actual potential. -/

open Matrix MatrixSpencer
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

noncomputable section
namespace HigherRankKS

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]

@[simp] theorem sourceTerm_zero_atom (β : ℝ)
    (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) : sourceTerm β 0 S = 0 := by
  simp [sourceTerm, sourceBlock]

theorem source_congr_weights_on_nonzero (A : ι → Matrix n n ℂ) (β : ℝ)
    {c d : ι → ℝ} (hcd : ∀ i, A i ≠ 0 → c i = d i)
    (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) : source A β c S = source A β d S := by
  unfold source
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : A i = 0
  · simp [hi]
  · rw [hcd i hi]

theorem potential_congr_weights_on_nonzero
    (H : Matrix (n ⊕ n) (n ⊕ n) ℂ) (A : ι → Matrix n n ℂ) (β θ : ℝ)
    {c d : ι → ℝ} (hcd : ∀ i, A i ≠ 0 → c i = d i) :
    potential H A β c θ = potential H A β d θ := by
  have heq : objective H A β c θ = objective H A β d θ := by
    funext S
    unfold objective
    rw [source_congr_weights_on_nonzero A β hcd S]
  unfold potential
  rw [heq]

variable {N : ℕ}

theorem cubePotential_congr_on_nonzero (A : Fin N → Matrix n n ℂ) (β θ : ℝ)
    {x y : Fin N → ℝ} (hxy : ∀ i, A i ≠ 0 → x i = y i) :
    cubePotential A β θ x = cubePotential A β θ y := by
  have hcenter : KSPotentialModels.center A x = KSPotentialModels.center A y := by
    unfold KSPotentialModels.center
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : A i = 0
    · simp [hi]
    · rw [hxy i hi]
  unfold cubePotential
  rw [hcenter]
  apply potential_congr_weights_on_nonzero
  intro i hi
  rw [hxy i hi]

theorem cubePotential_update_zero_atom (A : Fin N → Matrix n n ℂ) (β θ : ℝ)
    (x : Fin N → ℝ) (i : Fin N) (s : ℝ) (hi : A i = 0) :
    cubePotential A β θ (Function.update x i s) = cubePotential A β θ x := by
  apply cubePotential_congr_on_nonzero
  intro j hj
  have hji : j ≠ i := by
    intro h
    subst j
    exact hj hi
  exact Function.update_of_ne hji s x

end HigherRankKS
