import MatrixSpencer.MSManuscriptMatchedComplex
import MatrixSpencer.MSManuscriptComplexValueBoundScaled

/-! Actual matched-path complex value bounds, including compressed input scales. -/
open Matrix Set Metric
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
noncomputable section
namespace MatrixSpencer.MSManuscriptMatchedValueBound
open MSManuscriptMatchedComplex
variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
local instance {k : Type*} [Fintype k] [DecidableEq k] : CStarAlgebra (Matrix k k ℂ) := {}

theorem query_mem_ball (C Q : Matrix ι ι ℝ) (hQ : ‖realMatrixEmbedding Q‖ ≤ 1)
    {S : Matrix n n ℂ} {t γ μ : ℝ} (ht : |t| ≤ 1)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (p : Space n) (hp : p ∈ ball ((t:ℂ),S) (radius γ μ)) :
    query C Q p ∈ ball (realMatrixEmbedding (C-t^2•Q),S)
      (MSManuscriptComplexSourceDomain.radius γ μ) := by
  have hn : ‖p-((t:ℂ),S)‖ < radius γ μ := by simpa only [mem_ball,dist_eq_norm] using hp
  have ht' : ‖p.1-(t:ℂ)‖ ≤ radius γ μ := (le_max_left _ _).trans hn.le
  have hs' : ‖p.2-S‖ ≤ radius γ μ := (le_max_right _ _).trans hn.le
  have hr := radius_pos hγ hμ
  have hc := coefficient_sub_norm_le C Q hQ ht (radius_le_one hγ hγ1 hμ hμ1) ht'
  rw [mem_ball,dist_eq_norm]
  change max ‖coefficient C Q p.1-realMatrixEmbedding (C-t^2•Q)‖ ‖p.2-S‖ < _
  apply max_lt
  · unfold radius at hc hr
    linarith
  · unfold radius at hs' hr
    linarith

/-- The bound uses the actual general Hermitian family cap L, so coefficient
compression is not silently treated as preserving unit matrix norms. -/
theorem objective_norm_le_on_ball (H B : Matrix n n ℂ) (A : ι → Matrix n n ℂ)
    (hA : ∀i, (A i).IsHermitian) {L : ℝ} (hL : 0 ≤ L) (hAnorm : ∀i, ‖A i‖ ≤ L)
    (C Q : Matrix ι ι ℝ) (hQ : ‖realMatrixEmbedding Q‖ ≤ 1)
    {S : Matrix n n ℂ} {t θ R b γ μ : ℝ}
    (ht : |t| ≤ 1) (hθ : 0 ≤ θ) (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hH : ‖center H B (t:ℂ)‖ ≤ R) (hB : ‖B‖ ≤ b)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (hC : γ•(1 : Matrix ι ι ℝ) ≤ C-t^2•Q) (hC1 : C-t^2•Q ≤ 1)
    (hS : μ•(1 : Matrix n n ℂ) ≤ S) (hS1 : ‖S‖ ≤ 1)
    (p : Space n) (hp : p ∈ ball ((t:ℂ),S) (radius γ μ)) :
    ‖objective H B A C Q θ p‖ ≤ MSManuscriptComplexValueBoundScaled.valueCap ι n (R+b) θ L := by
  have hn : ‖p-((t:ℂ),S)‖ < radius γ μ := by simpa only [mem_ball,dist_eq_norm] using hp
  have ht' : ‖p.1-(t:ℂ)‖ ≤ radius γ μ := (le_max_left _ _).trans hn.le
  have hc := center_norm_le H B hH hB (radius_le_one hγ hγ1 hμ hμ1) ht'
  exact MSManuscriptComplexValueBoundScaled.objective_norm_le_on_ball (center H B p.1) A hA
    hL hAnorm hθ (add_nonneg hR hb) hc hγ hγ1 hμ hμ1 hC hC1 hS hS1 (query C Q p)
    (query_mem_ball C Q hQ ht hγ hγ1 hμ hμ1 p hp)

end MatrixSpencer.MSManuscriptMatchedValueBound
