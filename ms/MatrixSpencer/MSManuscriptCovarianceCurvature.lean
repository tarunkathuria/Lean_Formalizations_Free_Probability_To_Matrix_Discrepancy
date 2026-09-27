import MatrixSpencer.KSActualEnvelope
import MatrixSpencer.MSManuscriptGammaSmoothness


open Matrix Set Filter
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff Topology
noncomputable section
namespace MatrixSpencer.MSManuscriptCovarianceCurvature
set_option maxHeartbeats 1000000

section Envelope
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
local instance : NormedAddCommGroup ((ℝ × E) →L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ ((ℝ × E) →L[ℝ] ℝ) := inferInstance
local instance : NormedAddCommGroup ((ℝ × E) →L[ℝ] (ℝ × E) →L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ ((ℝ × E) →L[ℝ] (ℝ × E) →L[ℝ] ℝ) := inferInstance
open KSEnvelopeFourth

theorem value_second_le {I : Set ℝ} (hI : IsOpen I) {s : ℝ → E}
    (hs : ContDiffOn ℝ 4 s I) {F : (ℝ × E) → ℝ}
    (hF : ∀ t ∈ I, ContDiffAt ℝ 4 F (lift s t))
    (hstat : ∀ t ∈ I, ∀ u : E, fderiv ℝ F (lift s t) (0,u) = 0)
    {t : ℝ} (ht : t ∈ I) {g B : ℝ} (hg : 0 < g) (hB : 0 ≤ B)
    (h₂ : ‖second F (lift s t)‖ ≤ B)
    (hcoercive : ∀ u : E, g*‖u‖^2 ≤ -second F (lift s t) (0,u) (0,u)) :
    |iteratedDeriv 2 (fun z => F (lift s z)) t| ≤ B*(1+B/g) := by
  rw [value_second hI hs hF hstat ht]
  have hz := stationary_second hI hs hF hstat ht (deriv s t)
  have he : second F (lift s t) (velocity s t) (velocity s t) =
      second F (lift s t) (velocity s t) (1,0) := by
    calc
      _ = second F (lift s t) (velocity s t) ((1,0)+(0,deriv s t)) := by
        congr 1
        ext <;> simp [velocity]
      _ = _ := by rw [map_add, hz, add_zero]
  rw [he]
  have hn := norm_second_apply (second F (lift s t)) (velocity s t) ((1 : ℝ),(0 : E))
  have hone : ‖((1 : ℝ),(0 : E))‖ = 1 := by simp
  rw [hone, mul_one] at hn
  have hv := velocity_le hI hs hF hstat ht hg hB h₂ hcoercive
  exact hn.trans (mul_le_mul h₂ hv (norm_nonneg _) hB)
end Envelope

section Actual
open KSActualEnvelope KSFrobeniusTangent
variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n] [Nonempty n]
local instance : CStarAlgebra (Matrix n n ℂ) := {}
local instance : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance
local instance : NormedSpace ℝ (selfAdjoint (Matrix ι ι ℝ)) := inferInstance

theorem potential_second_le (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {θ : ℝ} (hθ : 0 < θ)
    (H : ℝ → selfAdjoint (Matrix n n ℂ)) (C : ℝ → selfAdjoint (Matrix ι ι ℝ))
    (hH : ContDiff ℝ ∞ H) (hC : ContDiff ℝ ∞ C)
    {I : Set ℝ} (hI : IsOpen I) (hpositive : ∀ t ∈ I, (C t : Matrix ι ι ℝ).PosDef)
    {t B : ℝ} (ht : t ∈ I) (hB : 0 ≤ B)
    (h₂ : secondNorm (objective A θ H C) (t,branch A θ H C t) ≤ B) :
    |iteratedDeriv 2 (fun z => ownerPotential (H z) A (C z) θ) t| ≤
      B*(1+B/(θ/2)) := by
  have hs : ContDiffOn ℝ 4 (branch A θ H C) I := by
    intro z hz
    exact ((branch_contDiffAt A hA hθ H C hH hC (hpositive z hz)).of_le
      (WithTop.coe_le_coe.mpr (show (4 : ℕ∞) ≤ ⊤ from le_top))).contDiffWithinAt
  have hf : ∀ z ∈ I, ContDiffAt ℝ 4 (objective A θ H C)
      (KSEnvelopeFourth.lift (branch A θ H C) z) := by
    intro z hz
    exact (objective_contDiffAt A hA H C hH hC (hpositive z hz) (branch_posDef A hθ H C z)).of_le
      (WithTop.coe_le_coe.mpr (show (4 : ℕ∞) ≤ ⊤ from le_top))
  have hstat : ∀ z ∈ I, ∀ u : Coordinates n,
      fderiv ℝ (objective A θ H C) (KSEnvelopeFourth.lift (branch A θ H C) z) (0,u) = 0 :=
    fun z hz u => branch_stationary A hA hθ H C hH hC (hpositive z hz) u
  have hh := value_second_le hI hs hf hstat ht (div_pos hθ (by norm_num)) hB h₂
    (branch_coercive A hA hθ H C hH hC (hpositive t ht))
  have he : (fun z => objective A θ H C (KSEnvelopeFourth.lift (branch A θ H C) z)) =ᶠ[𝓝 t]
      (fun z => ownerPotential (H z) A (C z) θ) := by
    filter_upwards [hI.mem_nhds ht] with z hz
    exact value_eq A hA H C (hpositive z hz)
  rwa [Filter.EventuallyEq.iteratedDeriv_eq 2 he] at hh
end Actual

end MatrixSpencer.MSManuscriptCovarianceCurvature
