import MatrixSpencer.KSFullManuscriptSuperlevel
import Mathlib.Analysis.Convex.Basic



open scoped InnerProductSpace
noncomputable section
namespace MatrixSpencer.KSFullManuscriptLevelBall

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def mixture (a : ℝ) (x c : E) : E := (1 - a) • x + a • c

theorem mixture_sub (a : ℝ) (x c : E) : mixture a x c - x = a • (c - x) := by
  unfold mixture
  module

theorem ball_subset_convex {K : Set E} (hK : Convex ℝ K) {x c : E} {a r : ℝ}
    (hx : x ∈ K) (hinner : Metric.closedBall c r ⊆ K) (ha : 0 < a) (ha1 : a ≤ 1) :
    Metric.closedBall (mixture a x c) (a * r) ⊆ K := by
  intro y hy
  let z := c + a⁻¹ • (y - mixture a x c)
  have hz : z ∈ Metric.closedBall c r := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    dsimp [z]
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ha]
    have hn : ‖y - mixture a x c‖ ≤ a * r := by
      simpa only [Metric.mem_closedBall, dist_eq_norm] using hy
    calc
      a⁻¹ * ‖y - mixture a x c‖ ≤ a⁻¹ * (a * r) :=
        mul_le_mul_of_nonneg_left hn (inv_nonneg.mpr ha.le)
      _ = r := by field_simp
  have hc := hK hx (hinner hz) (sub_nonneg.mpr ha1) ha.le (by ring : 1 - a + a = 1)
  convert hc using 1
  dsimp [z, mixture]
  simp only [smul_add, smul_smul, mul_inv_cancel₀ ha.ne', one_smul]
  module

theorem ball_distance_le {x c y : E} {a r R : ℝ}
    (ha : 0 ≤ a) (hx : ‖x‖ ≤ R) (hc : ‖c‖ ≤ R) (hr : r ≤ R)
    (hy : y ∈ Metric.closedBall (mixture a x c) (a * r)) :
    ‖y - x‖ ≤ 3 * a * R := by
  have hn : ‖y - mixture a x c‖ ≤ a * r := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hy
  have hm : ‖mixture a x c - x‖ ≤ 2 * a * R := by
    rw [mixture_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
    calc
      a * ‖c - x‖ ≤ a * (‖c‖ + ‖x‖) := mul_le_mul_of_nonneg_left (norm_sub_le _ _) ha
      _ ≤ 2 * a * R := by nlinarith
  calc
    ‖y - x‖ ≤ ‖y - mixture a x c‖ + ‖mixture a x c - x‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 3 * a * R := by nlinarith

theorem ball_subset_level {K : Set E} (hK : Convex ℝ K) {x c g : E} {a r R L b t : ℝ}
    (hx : x ∈ K) (hinner : Metric.closedBall c r ⊆ K) (ha : 0 < a) (ha1 : a ≤ 1)
    (hxR : ‖x‖ ≤ R) (hcR : ‖c‖ ≤ R) (hrR : r ≤ R) (hg : ‖g‖ ≤ L)
    (hlevel : t ≤ b + ⟪g, x⟫_ℝ - 3 * a * R * L) :
    Metric.closedBall (mixture a x c) (a * r) ⊆ {y | y ∈ K ∧ t ≤ b + ⟪g, y⟫_ℝ} := by
  intro y hy
  refine ⟨ball_subset_convex hK hx hinner ha ha1 hy, ?_⟩
  have hdist := ball_distance_le ha.le hxR hcR hrR hy
  have hL : 0 ≤ L := (norm_nonneg _).trans hg
  have hi : |⟪g, y⟫_ℝ - ⟪g, x⟫_ℝ| ≤ 3 * a * R * L := by
    rw [← inner_sub_right]
    calc
      |⟪g, y - x⟫_ℝ| ≤ ‖g‖ * ‖y - x‖ := abs_real_inner_le_norm _ _
      _ ≤ L * (3 * a * R) := mul_le_mul hg hdist (norm_nonneg _) hL
      _ = _ := by ring
  have := (abs_le.mp hi).1
  linarith


def fraction (τ L R : ℝ) : ℝ := τ / (8 * L * R)

theorem fraction_pos {τ L R : ℝ} (hτ : 0 < τ) (hL : 0 < L) (hR : 0 < R) :
    0 < fraction τ L R := by unfold fraction; positivity

theorem fraction_le_one {τ L R : ℝ} (hτ : τ ≤ L * R) (hL : 0 < L) (hR : 0 < R) :
    fraction τ L R ≤ 1 := by
  unfold fraction
  apply (div_le_iff₀ (by positivity : 0 < 8 * L * R)).mpr
  nlinarith

theorem fraction_loss {τ L R : ℝ} (hL : 0 < L) (hR : 0 < R) :
    3 * fraction τ L R * R * L = 3 * τ / 8 := by
  unfold fraction
  field_simp

/-- A level at least `τ` below any feasible point contains the explicit ball
of radius `τ r / (8 L R)`. No maximizing point is needed for this assertion. -/
theorem explicit_ball_subset_level {K : Set E} (hK : Convex ℝ K) {x c g : E} {τ r R L b t : ℝ}
    (hx : x ∈ K) (hinner : Metric.closedBall c r ⊆ K)
    (hτ : 0 < τ) (hτcap : τ ≤ L * R) (hL : 0 < L) (hR : 0 < R)
    (hxR : ‖x‖ ≤ R) (hcR : ‖c‖ ≤ R) (hrR : r ≤ R) (hg : ‖g‖ ≤ L)
    (hlevel : t + τ ≤ b + ⟪g, x⟫_ℝ) :
    Metric.closedBall (mixture (fraction τ L R) x c) (fraction τ L R * r) ⊆
      {y | y ∈ K ∧ t ≤ b + ⟪g, y⟫_ℝ} := by
  apply ball_subset_level hK hx hinner (fraction_pos hτ hL hR)
    (fraction_le_one hτcap hL hR) hxR hcR hrR hg
  rw [fraction_loss hL hR]
  linarith

end MatrixSpencer.KSFullManuscriptLevelBall
