import MatrixSpencer.FiniteHalfPhase
import MatrixSpencer.MSManuscriptBoundedProcess

/-! The scalar epoch ledger used by both finite adaptive MS phases.
Every successful actual epoch increases this bounded ledger by at least one. -/
open scoped BigOperators
noncomputable section
namespace MatrixSpencer.MSManuscriptPhaseProgress
open FiniteHalfPhase
variable {ι : Type*} [Fintype ι]

def progress (τ : ℝ) (x : EuclideanSpace ℝ ι) : ℝ :=
  ((32 / τ) * ‖x‖^2 + 128 * (frozenCoordinates x).card) / Fintype.card ι

theorem progress_nonneg {τ : ℝ} (hτ : 0 < τ) (x : EuclideanSpace ℝ ι) :
    0 ≤ progress τ x := by
  exact div_nonneg (add_nonneg (mul_nonneg (by positivity) (sq_nonneg _))
    (by positivity)) (Nat.cast_nonneg _)

theorem progress_le {τ : ℝ} (hτ : 0 < τ) (hk : 0 < Fintype.card ι)
    {x : EuclideanSpace ℝ ι} (hx : Cube x) : progress τ x ≤ 32/τ+128 := by
  have hN : (0:ℝ) < Fintype.card ι := Nat.cast_pos.mpr hk
  apply (div_le_iff₀ hN).mpr
  have hn := cube_euclidean_norm_sq_le_card hx
  have hf : ((frozenCoordinates x).card:ℝ) ≤ Fintype.card ι :=
    Nat.cast_le.mpr (frozenCoordinates_card_le x)
  have hm := mul_le_mul_of_nonneg_left hn (show 0 ≤ 32/τ by positivity)
  nlinarith

theorem progress_advance {τ B time : ℝ} (hτ : 0 < τ) (hk : 0 < Fintype.card ι)
    {potential : EuclideanSpace ℝ ι → ℝ} {x y : EuclideanSpace ℝ ι}
    (h : EpochAdvance potential τ B x y time) (hx : ¬Terminal x) :
    progress τ x + 1 ≤ progress τ y := by
  have hN : (0:ℝ) < Fintype.card ι := Nat.cast_pos.mpr hk
  have hc : 0 ≤ (32:ℝ)/τ := by positivity
  have hcτ : ((32:ℝ)/τ)*τ = 32 := by field_simp
  have hg := h.uniform_norm_progress hx
  have hf : ((frozenCoordinates x).card:ℝ) ≤ (frozenCoordinates y).card :=
    Nat.cast_le.mpr (Finset.card_le_card h.frozen)
  have hg0 : ‖x‖^2 ≤ ‖y‖^2 := by
    have := mul_nonneg (show (0:ℝ) ≤ Fintype.card ι / 32 by positivity) h.time_nonneg
    linarith
  unfold progress
  rw [← div_self hN.ne', ← add_div, div_le_div_iff_of_pos_right hN]
  rcases h.uniform_success hx with ht | hf'
  · have hg' : (Fintype.card ι:ℝ)*τ ≤ 32*(‖y‖^2-‖x‖^2) := by
      have hm := mul_le_mul_of_nonneg_left ht (show (0:ℝ) ≤ Fintype.card ι by positivity)
      nlinarith
    have hm := mul_le_mul_of_nonneg_left hg' hc
    nlinarith
  · have hm := mul_le_mul_of_nonneg_left hg0 hc
    nlinarith

end MatrixSpencer.MSManuscriptPhaseProgress
