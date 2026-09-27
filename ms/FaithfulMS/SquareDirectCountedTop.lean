import FaithfulMS.SquareDirectGamma
import MatrixSpencer.RealRAMMSGammaTop

/-! Scalar negation, one exact EVD, the minimum-diagonal scan, an explicitly
computed Rayleigh quotient, and the threshold comparison. -/
open Matrix
open scoped BigOperators
noncomputable section
namespace FaithfulMS.SquareDirectCountedTop
open MatrixSpencer MatrixSpencer.RealRAM
open JacobiIteration (Counted Mat)
variable {k : ℕ}
attribute [local instance] Classical.propDecidable

def compute (G : Mat k) (t : ℝ) (hk : 0<k) : Counted (Option (EuclideanSpace ℝ (Fin k))) :=
  let A := MSGammaTop.negative G
  let u := SquareDirectEVD.direction A.value hk
  let q := MSGammaTop.rayleigh G u.value
  ⟨if q.value ≤ t then none else some u.value, A.cost+u.cost+q.cost+4⟩

theorem compute_value (G : Mat k) (t : ℝ) (hk : 0<k) :
    (compute G t hk).value =
      if SquareDirectGamma.value G hk ≤ t then none else some (SquareDirectGamma.vector G hk) := by
  simp only [compute, MSGammaTop.negative_value, SquareDirectEVD.direction_value,
    MSGammaTop.rayleigh_value, SquareDirectGamma.value, SquareDirectGamma.vector]

theorem spectral_execution (G : Mat k) (hG : G.IsSymm) :
    SquareDirectEVD.Executes (-G) (SquareDirectEVD.compute (-G)).value
      (SquareDirectEVD.compute (-G)).cost := SquareDirectEVD.compute_execution _ hG.neg

theorem rayleigh_execution (G : Mat k) (hk : 0<k) :
    Expr.Executes (MSGammaTop.rayleighInput G (SquareDirectGamma.vector G hk))
      MSGammaTop.rayleighExpr (SquareDirectGamma.value G hk) (6*k^2+2*k+1) :=
  MSGammaTop.rayleigh_execution _ _

theorem compute_cost (G : Mat k) (t : ℝ) (hk : 0<k) :
    (compute G t hk).cost ≤ 100*(k+1)^3 := by
  have hu := SquareDirectEVD.direction_cost (MSGammaTop.negative G).value hk
  have hq := MSGammaTop.rayleigh_cost G
    (SquareDirectEVD.direction (MSGammaTop.negative G).value hk).value
  have h2 : (k+1)^2 ≤ (k+1)^3 := Nat.pow_le_pow_right (by omega) (by omega)
  dsimp only [compute, MSGammaTop.negative]
  dsimp only [MSGammaTop.negative] at hu hq
  nlinarith

end FaithfulMS.SquareDirectCountedTop
