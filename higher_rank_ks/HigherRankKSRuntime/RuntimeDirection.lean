import HigherRankKSRuntime.Tangent.RuntimeFrame
import HigherRankKSRuntime.Tangent.RuntimeMatrix
import HigherRankKSRuntime.TangentEVD
import MatrixSpencer.RealRAMFullHessian

/-! Counted centered Hessian queries, scalar tangent-frame construction,
matrix compression, exact EVD, and expansion of the selected direction. -/

open Matrix
open scoped BigOperators
noncomputable section
namespace HigherRankKSRuntime.RuntimeDirection
open HigherRankKSRuntime.Tangent HigherRankKSRuntime.Tangent.RuntimeMatrix
open MatrixSpencer.RealRAM
open MatrixSpencer.RealRAM.JacobiIteration (Counted)
open RadialBasis (Space)
variable {m : ℕ}

def compute (R : FullHessian.Report m) (x : Space m) (t : ℝ)
    (hr : 0 < (Frame.canonical m x).rank) : Counted (Space m) :=
  let H := FullHessian.matrix R t
  let U := RuntimeFrame.compute x
  let L := product U.valueᵀ H.value
  let B := product L.value U.value
  let w := SeamlessKS.ExactEVD.direction B.value hr
  let g := matvec U.value w.value
  ⟨g.value, H.cost + U.cost + m * (Frame.canonical m x).rank +
    L.cost + B.cost + w.cost + g.cost + 8⟩

theorem compute_value (R : FullHessian.Report m) (x : Space m) (t : ℝ)
    (hr : 0 < (Frame.canonical m x).rank) :
    (compute R x t hr).value = TangentEVD.output x
      (MatrixSpencer.KSFullManuscriptHessian.matrixReport (fun y => (R y).value) 0 t) hr := by
  simp only [compute, matvec_value, product_value, RuntimeFrame.compute_value,
    FullHessian.matrix_value, SeamlessKS.ExactEVD.direction_value]
  rw [← FrameFormula.compression_matrix, ← FrameFormula.apply_columns]
  rfl

theorem compute_unit (R : FullHessian.Report m) (x : Space m) (t : ℝ)
    (hr : 0 < (Frame.canonical m x).rank) : ‖(compute R x t hr).value‖ = 1 := by
  rw [compute_value]
  exact TangentEVD.output_norm _ _ _

theorem compute_orthogonal (R : FullHessian.Report m) (x : Space m) (t : ℝ)
    (hr : 0 < (Frame.canonical m x).rank) : inner ℝ x (compute R x t hr).value = 0 := by
  rw [compute_value]
  exact TangentEVD.output_orthogonal _ _ _

theorem compute_minimal (R : FullHessian.Report m) (x : Space m) (t : ℝ)
    (hr : 0 < (Frame.canonical m x).rank) (g : Space m)
    (hg : ‖g‖ = 1) (horth : inner ℝ x g = 0) :
    let H := MatrixSpencer.KSFullManuscriptHessian.matrixReport (fun y => (R y).value) 0 t
    MatrixSpencer.KSRayleighAccuracy.realRayleigh H (compute R x t hr).value ≤
      MatrixSpencer.KSRayleighAccuracy.realRayleigh H g := by
  dsimp only
  rw [compute_value]
  exact TangentEVD.output_minimizes_tangent _ _
    (MatrixSpencer.KSFullManuscriptHessian.matrixReport_isSymm _ _ _) _ g hg horth

theorem spectral_execution (R : FullHessian.Report m) (x : Space m) (t : ℝ) :
    let H := FullHessian.matrix R t
    let U := RuntimeFrame.compute x
    let L := product U.valueᵀ H.value
    let B := product L.value U.value
    SeamlessKS.ExactEVD.Executes B.value (SeamlessKS.ExactEVD.compute B.value).value
      (SeamlessKS.ExactEVD.compute B.value).cost := by
  dsimp only
  apply SeamlessKS.ExactEVD.compute_execution
  rw [product_value, product_value, RuntimeFrame.compute_value,
    FullHessian.matrix_value, ← FrameFormula.compression_matrix]
  exact RestrictedEVD.compression_symmetric _ _
    (MatrixSpencer.KSFullManuscriptHessian.matrixReport_isSymm _ _ _)

theorem compute_cost (R : FullHessian.Report m) (x : Space m) (t : ℝ)
    (hr : 0 < (Frame.canonical m x).rank) {Q : ℕ}
    (hQ : ∀ y, ‖y‖ ≤ 2 * |t| → (R y).cost ≤ Q) :
    (compute R x t hr).cost ≤
      m ^ 2 * (4 * Q + 100 * (m + 1) + 18) + 1000 * (m + 1) ^ 5 + 20 := by
  have hH := FullHessian.matrix_cost R t hQ
  have hU := RuntimeFrame.compute_cost x
  have hrm : (Frame.canonical m x).rank ≤ m + 1 :=
    (RuntimeFrame.rank_le x).trans (by omega)
  have hL := product_cost (RuntimeFrame.compute x).valueᵀ
    (FullHessian.matrix R t).value
    (b := m + 1) (by omega) hrm (by omega) (by omega)
  have hB := product_cost
    (product (RuntimeFrame.compute x).valueᵀ (FullHessian.matrix R t).value).value
    (RuntimeFrame.compute x).value (b := m + 1) (by omega) hrm (by omega) hrm
  have hw := SeamlessKS.ExactEVD.direction_cost
    (product (product (RuntimeFrame.compute x).valueᵀ (FullHessian.matrix R t).value).value
      (RuntimeFrame.compute x).value).value hr
  have hg := product_cost (RuntimeFrame.compute x).value
    (fun i (_ : Fin 1) => (SeamlessKS.ExactEVD.direction
      (product (product (RuntimeFrame.compute x).valueᵀ (FullHessian.matrix R t).value).value
        (RuntimeFrame.compute x).value).value hr).value i)
    (b := m + 1) (by omega) (by omega) hrm (by omega)
  have hr2 : m * (Frame.canonical m x).rank ≤ (m + 1) ^ 2 := by
    calc
      _ ≤ (m + 1) * (m + 1) := Nat.mul_le_mul (by omega) hrm
      _ = _ := by ring
  have h35 : (m + 1) ^ 3 ≤ (m + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
  have h45 : (m + 1) ^ 4 ≤ (m + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
  have h25 : (m + 1) ^ 2 ≤ (m + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
  have h15 : m + 1 ≤ (m + 1) ^ 5 := Nat.le_self_pow (by omega) _
  dsimp only [compute, matvec]
  nlinarith

end HigherRankKSRuntime.RuntimeDirection
