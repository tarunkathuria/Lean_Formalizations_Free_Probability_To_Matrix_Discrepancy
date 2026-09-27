import RadialKS.RuntimeFrame
import RadialKS.RuntimeMatrix
import RadialKS.RawNumerics
import MatrixSpencer.RealRAMFullHessian

/-! Counted raw-Hessian compression, exact EVD, and expansion of its unit vector. -/
open Matrix
open scoped BigOperators
noncomputable section
namespace RadialKS.RuntimeDirection
open RadialKS.RuntimeMatrix
open MatrixSpencer.RealRAM
open MatrixSpencer.RealRAM.JacobiIteration (Counted)
open RadialBasis (Space)
variable {m n p : ℕ}

def compute (R : FullHessian.Report m) (z : Space m) (t : ℝ)
    (hr : 0 < (Frame.canonical m z).rank) : Counted (Space m) :=
  let H := FullHessian.matrix R t
  let K := FullHessian.weighted (fun _ => 1) H.value
  let U := RuntimeFrame.compute z
  let L := product U.valueᵀ K.value
  let B := product L.value U.value
  let w := SeamlessKS.ExactEVD.direction B.value hr
  let g := matvec U.value w.value
  ⟨g.value, H.cost+K.cost+U.cost+m*(Frame.canonical m z).rank+L.cost+B.cost+w.cost+g.cost+8⟩

theorem compute_value (R : FullHessian.Report m) (z : Space m) (t : ℝ)
    (hr : 0 < (Frame.canonical m z).rank) :
    (compute R z t hr).value = RestrictedEVD.output (Frame.canonical m z).embed
      (RawNumerics.half (MatrixSpencer.KSFullManuscriptHessian.matrixReport
        (fun y => (R y).value) 0 t)) hr := by
  simp only [compute, matvec_value, product_value, RuntimeFrame.compute_value,
    FullHessian.weighted_value, FullHessian.matrix_value, SeamlessKS.ExactEVD.direction_value]
  rw [← FrameFormula.compression_matrix]
  rw [← FrameFormula.apply_columns]
  rfl

theorem spectral_execution (R : FullHessian.Report m) (z : Space m) (t : ℝ) :
    let H := FullHessian.matrix R t
    let K := FullHessian.weighted (fun _ => 1) H.value
    let U := RuntimeFrame.compute z
    let L := product U.valueᵀ K.value
    let B := product L.value U.value
    SeamlessKS.ExactEVD.Executes B.value (SeamlessKS.ExactEVD.compute B.value).value
      (SeamlessKS.ExactEVD.compute B.value).cost := by
  dsimp only
  apply SeamlessKS.ExactEVD.compute_execution
  rw [product_value, product_value, RuntimeFrame.compute_value,
    FullHessian.weighted_value, FullHessian.matrix_value, ← FrameFormula.compression_matrix]
  apply RestrictedEVD.compression_symmetric
  exact MatrixSpencer.KSFullManuscriptHessian.weighted_isSymm (fun _ => 1)
    (MatrixSpencer.KSFullManuscriptHessian.matrixReport_isSymm _ _ _)

theorem compute_cost (R : FullHessian.Report m) (z : Space m) (t : ℝ)
    (hr : 0 < (Frame.canonical m z).rank) {Q : ℕ}
    (hQ : ∀ y, ‖y‖ ≤ 2*|t| → (R y).cost ≤ Q) :
    (compute R z t hr).cost ≤
      m^2*(4*Q+100*(m+1)+18)+1000*(m+1)^5+20 := by
  have hH := FullHessian.matrix_cost R t hQ
  have hK := FullHessian.weighted_cost (fun _ : Fin m => (1 : ℝ)) (FullHessian.matrix R t).value
  have hU := RuntimeFrame.compute_cost z
  have hrm : (Frame.canonical m z).rank ≤ m+1 := (RuntimeFrame.rank_le z).trans (by omega)
  have hL := product_cost (RuntimeFrame.compute z).valueᵀ
    (FullHessian.weighted (fun _ => 1) (FullHessian.matrix R t).value).value
    (b := m+1) (by omega) hrm (by omega) (by omega)
  have hB := product_cost
    (product (RuntimeFrame.compute z).valueᵀ
      (FullHessian.weighted (fun _ => 1) (FullHessian.matrix R t).value).value).value
    (RuntimeFrame.compute z).value (b := m+1) (by omega) hrm (by omega) hrm
  have hw := SeamlessKS.ExactEVD.direction_cost
    (product (product (RuntimeFrame.compute z).valueᵀ
      (FullHessian.weighted (fun _ => 1) (FullHessian.matrix R t).value).value).value
      (RuntimeFrame.compute z).value).value hr
  have hg := product_cost (RuntimeFrame.compute z).value
    (fun i (_ : Fin 1) => (SeamlessKS.ExactEVD.direction
      (product (product (RuntimeFrame.compute z).valueᵀ
        (FullHessian.weighted (fun _ => 1) (FullHessian.matrix R t).value).value).value
        (RuntimeFrame.compute z).value).value hr).value i)
    (b := m+1) (by omega) (by omega) hrm (by omega)
  have hr2 : m*(Frame.canonical m z).rank ≤ (m+1)^2 := by
    calc _ ≤ (m+1)*(m+1) := Nat.mul_le_mul (by omega) hrm
         _ = _ := by ring
  have h35 : (m+1)^3 ≤ (m+1)^5 := Nat.pow_le_pow_right (by omega) (by omega)
  have h45 : (m+1)^4 ≤ (m+1)^5 := Nat.pow_le_pow_right (by omega) (by omega)
  have h25 : (m+1)^2 ≤ (m+1)^5 := Nat.pow_le_pow_right (by omega) (by omega)
  have h15 : m+1 ≤ (m+1)^5 := Nat.le_self_pow (by omega) _
  dsimp only [compute, matvec]
  nlinarith

end RadialKS.RuntimeDirection
