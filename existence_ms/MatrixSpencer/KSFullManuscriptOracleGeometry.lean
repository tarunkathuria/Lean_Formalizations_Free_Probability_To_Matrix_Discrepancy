import MatrixSpencer.KSFullManuscriptCoordinateBounds
import MatrixSpencer.KSFullManuscriptSourceCap

/-!
# Input-derived geometry for the actual affine density SDP

The source cap, the inner radius, the coordinate outer radius, and the linear
objective bound are all given by finite arithmetic expressions in the input
matrices. Every corresponding geometry hypothesis is proved here.
-/

open Matrix
open scoped BigOperators InnerProductSpace MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSFullManuscriptOracleGeometry

open KSFullManuscriptSDPCoordinates KSFullManuscriptAffineData KSFullManuscriptAffineObjective
open KSFullManuscriptCenterData KSFullManuscriptCoordinateBounds KSFullManuscriptSDPIdentity
variable {d : ℕ} {ι : Type*} [Fintype ι]

def R (a : Fin d) (B : ι → Matrix (Fin d) (Fin d) ℂ) (lam : ℝ) : ℝ :=
  outerRadius a (KSFullManuscriptSourceCap.cap B + lam)

def r (a : Fin d) (B : ι → Matrix (Fin d) (Fin d) ℂ) (hd : 0 < d) (lam : ℝ) : ℝ :=
  min (innerRadius a B hd lam) 1

def L (a : Fin d) (H : Matrix (Fin d) (Fin d) ℂ) (θ : ℝ) : ℝ :=
  1 + Real.sqrt (∑ i, (coefficient a H θ i) ^ 2)

theorem R_pos (a : Fin d) (B : ι → Matrix (Fin d) (Fin d) ℂ) (lam : ℝ) : 0 < R a B lam :=
  outerRadius_pos a _

theorem one_le_R (a : Fin d) (B : ι → Matrix (Fin d) (Fin d) ℂ) (lam : ℝ) : 1 ≤ R a B lam := by
  unfold R outerRadius
  have hn : 0 ≤ (dimension a : ℝ) := Nat.cast_nonneg _
  have hs := Real.sqrt_nonneg (KSFullManuscriptSourceCap.cap B + lam)
  nlinarith

theorem r_pos (a : Fin d) (B : ι → Matrix (Fin d) (Fin d) ℂ) (hd : 0 < d)
    {lam : ℝ} (hlam : 0 < lam) : 0 < r a B hd lam :=
  lt_min (innerRadius_pos a B hd hlam) zero_lt_one

theorem r_le_R (a : Fin d) (B : ι → Matrix (Fin d) (Fin d) ℂ) (hd : 0 < d) (lam : ℝ) :
    r a B hd lam ≤ R a B lam := (min_le_right _ _).trans (one_le_R a B lam)

theorem L_pos (a : Fin d) (H : Matrix (Fin d) (Fin d) ℂ) (θ : ℝ) : 0 < L a H θ := by
  unfold L
  positivity

theorem coefficient_norm_le (a : Fin d) (H : Matrix (Fin d) (Fin d) ℂ) (θ : ℝ) :
    ‖coefficient a H θ‖ ≤ L a H θ := by
  have he : (∑ i, (coefficient a H θ i) ^ 2) = ‖coefficient a H θ‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Real.norm_eq_abs, sq_abs]
  unfold L
  rw [he, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
  linarith

theorem actual_inner_ball (a : Fin d) (B : ι → Matrix (Fin d) (Fin d) ℂ) (hd : 0 < d)
    {lam : ℝ} (hlam : 0 < lam) :
    Metric.closedBall (0 : Space a) (r a B hd lam) ⊆ KSFullManuscriptAffinePSD.target (centerData a B hd lam) :=
  (Metric.closedBall_subset_closedBall (min_le_left _ _)).trans (inner_ball a B hd hlam)

theorem actual_outer_ball (a : Fin d) (B : ι → Matrix (Fin d) (Fin d) ℂ) (hd : 0 < d)
    (lam : ℝ) :
    KSFullManuscriptAffinePSD.target (centerData a B hd lam) ⊆ Metric.closedBall (0 : Space a) (R a B lam) := by
  intro x hx
  have htr : realTrace (densityCenter hd : Matrix (Fin d) (Fin d) ℂ) = 1 :=
    KSFullManuscriptStrictFeasible.density_trace hd
  have hf := (target_iff a B (densityCenter hd) (rootCenter hd) htr lam x).mp hx
  have hs := feasible_density hf
  have hT := KSFullManuscriptSourceCap.regularized_source_le B hs lam
  have hZ := fun i j => KSFullManuscriptBlockBounds.block_entry_le hf.2.2.1 hs.2 hT i j
  have hb := coordinate_norm_le a (densityCenter hd) (rootCenter hd) x
    (densityCenter_entry_le hd) (rootCenter_entry_le hd) hs hf.2.2.2 hZ
  simpa only [Metric.mem_closedBall, dist_zero_right, R, outerRadius] using hb

end MatrixSpencer.KSFullManuscriptOracleGeometry
