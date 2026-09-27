import MatrixSpencer.KSFullManuscriptAffineInnerBall
import MatrixSpencer.KSFullManuscriptCenterMargin

/-!
# The actual strictly feasible center and arithmetic inner ball

The affine data are centered at exactly `S=I/d`, `Y=I/(2 sqrt d)`, `Z=0`.
The explicit complex block margin is transported through realification and
finite row reindexing. The numerical radius is computed from that margin and
the actual real coefficient entries, without a source spectral gap.
-/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSFullManuscriptCenterData

open KSFullManuscriptAffineData KSFullManuscriptCenterMargin KSFullManuscriptAffineInnerBall
open KSComplexProjectionGeometry KSComplexTraceSqrt
variable {d : ℕ} {ι : Type*} [Fintype ι]

def densityCenter (hd : 0 < d) : selfAdjoint (Matrix (Fin d) (Fin d) ℂ) :=
  ⟨KSFullManuscriptStrictFeasible.density d, (KSFullManuscriptStrictFeasible.density_posDef hd).isHermitian⟩

def rootCenter (hd : 0 < d) : selfAdjoint (Matrix (Fin d) (Fin d) ℂ) :=
  ⟨KSFullManuscriptStrictFeasible.rootCenter d, (KSFullManuscriptStrictFeasible.rootCenter_posDef hd).isHermitian⟩

def centerData (a : Fin d) (B : ι → Matrix (Fin d) (Fin d) ℂ) (hd : 0 < d) (lam : ℝ) :=
  data a B (densityCenter hd) (rootCenter hd) lam

theorem center_constant_floor (a : Fin d) (B : ι → Matrix (Fin d) (Fin d) ℂ)
    (hd : 0 < d) {lam : ℝ} (hlam : 0 < lam) :
    margin d lam • (1 : Matrix (Fin (matrixSize (Fin d))) (Fin (matrixSize (Fin d))) ℝ) ≤
      (centerData a B hd lam).constant := by
  have hc := realification_le_iff.mpr (center_floor B hd hlam)
  rw [realification_scalar] at hc
  have hh := (Matrix.le_iff.mp hc).submatrix (KSCanonicalSDPIndex.rows (Fin d)).symm
  apply Matrix.le_iff.mpr
  change ((centerData a B hd lam).constant - margin d lam •
    (1 : Matrix (KSFullManuscriptSDPBlockPencil.RealIndex (Fin d)) (KSFullManuscriptSDPBlockPencil.RealIndex (Fin d)) ℝ).submatrix
      (KSCanonicalSDPIndex.rows (Fin d)).symm
      (KSCanonicalSDPIndex.rows (Fin d)).symm).PosSemidef at hh
  simpa only [Matrix.submatrix_one_equiv] using hh

def innerRadius (a : Fin d) (B : ι → Matrix (Fin d) (Fin d) ℂ) (hd : 0 < d) (lam : ℝ) : ℝ :=
  radius (centerData a B hd lam) (margin d lam)

theorem innerRadius_pos (a : Fin d) (B : ι → Matrix (Fin d) (Fin d) ℂ)
    (hd : 0 < d) {lam : ℝ} (hlam : 0 < lam) : 0 < innerRadius a B hd lam :=
  radius_pos _ (margin_pos hd hlam)

/-- The actual numerical SDP has the explicitly computed inner ball. -/
theorem inner_ball (a : Fin d) (B : ι → Matrix (Fin d) (Fin d) ℂ)
    (hd : 0 < d) {lam : ℝ} (hlam : 0 < lam) :
    Metric.closedBall (0 : Space a) (innerRadius a B hd lam) ⊆
      KSFullManuscriptAffinePSD.target (centerData a B hd lam) :=
  ball_subset_target _ (margin_pos hd hlam) (center_constant_floor a B hd hlam)

theorem zero_feasible (a : Fin d) (B : ι → Matrix (Fin d) (Fin d) ℂ)
    (hd : 0 < d) {lam : ℝ} (hlam : 0 < lam) :
    (0 : Space a) ∈ KSFullManuscriptAffinePSD.target (centerData a B hd lam) :=
  inner_ball a B hd hlam (Metric.mem_closedBall_self (innerRadius_pos a B hd hlam).le)

end MatrixSpencer.KSFullManuscriptCenterData
