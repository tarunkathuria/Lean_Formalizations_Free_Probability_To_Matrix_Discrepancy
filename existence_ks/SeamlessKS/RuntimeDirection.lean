import SeamlessKS.RuntimeMagnitude
import SeamlessKS.ExactEVD

/-! Counted finite Hessian stencil, exact EVD, and comparison scans.
The additional spectral instruction is `ExactEVD.Executes.evd`; no rotation
loop or spectral tolerance is evaluated by either numerical routine. -/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace SeamlessKS.RuntimeDirection
open MatrixSpencer MatrixSpencer.RealRAM
open MatrixSpencer.RealRAM.JacobiIteration (Counted)
open SeamlessKS.Parameters SeamlessKS.Walk
open MatrixSpencer.KSLiveEnumeration (count)
variable {N d m : ℕ}

def compute (R : FullHessian.Report m) (w : Fin m → ℝ) (t : ℝ)
    (hm : 0<m) : Counted (EuclideanSpace ℝ (Fin m)) :=
  let H := FullHessian.matrix R t
  let K := FullHessian.weighted w H.value
  let q := ExactEVD.direction K.value hm
  ⟨q.value,H.cost+K.cost+q.cost+3⟩

theorem compute_value (R : FullHessian.Report m) (w : Fin m → ℝ) (t : ℝ)
    (hm : 0<m) :
    (compute R w t hm).value=ExactEVD.output
      (KSFullManuscriptHessian.weighted w
        (KSFullManuscriptHessian.matrixReport (fun z => (R z).value) 0 t)) hm := by
  simp only [compute,FullHessian.matrix_value,FullHessian.weighted_value,ExactEVD.direction_value]

theorem spectral_execution (R : FullHessian.Report m) (w : Fin m → ℝ) (t : ℝ) :
    let A := (FullHessian.weighted w (FullHessian.matrix R t).value).value
    ExactEVD.Executes A (ExactEVD.compute A).value (ExactEVD.compute A).cost := by
  apply ExactEVD.compute_execution
  rw [FullHessian.weighted_value,FullHessian.matrix_value]
  exact KSFullManuscriptHessian.weighted_isSymm w
    (KSFullManuscriptHessian.matrixReport_isSymm _ _ _)

theorem compute_cost (R : FullHessian.Report m) (w : Fin m → ℝ) (t : ℝ)
    (hm : 0<m) {Q : ℕ}
    (hQ : ∀ z, ‖z‖≤2*|t| → (R z).cost≤Q) :
    (compute R w t hm).cost≤
      m^2*(4*Q+100*(m+1)+18)+600*(m+1)^3+5 := by
  have hH := FullHessian.matrix_cost R t hQ
  have hK := FullHessian.weighted_cost w (FullHessian.matrix R t).value
  have hq := ExactEVD.direction_cost
    (FullHessian.weighted w (FullHessian.matrix R t).value).value hm
  have hp : m+1≤(m+1)^3 := Nat.le_self_pow (by omega) _
  dsimp only [compute]
  nlinarith

theorem actual_value [Nonempty (Fin d)] (O : KSConvexValueOracle.Solver)
    (v : Fin N → Fin d → ℂ) (hd : 0<d) (hp : ∑ i,KSRankOne.atom (v i)=1)
    (s : WalkState N) (hs : ¬Walk.terminal s)
    (R : FullHessian.Report (count s.coeff)) (hR : ∀ z,(R z).value=faceReport O v s z) :
    (compute R (liveWeights s) (queryStep v) (liveCount_pos s hs)).value=liveOutput O v s hs := by
  have he : (fun z => (R z).value)=faceReport O v s := funext hR
  rw [compute_value,he]
  rfl

/-- Exact norm from EVD of the real symmetric representation; no padding. -/
def norm (A : Matrix (Fin d) (Fin d) ℂ) : Counted ℝ :=
  let B := KSNormReport.realify A
  let r := ExactEVD.norm B.value
  ⟨r.value,B.cost+r.cost+3⟩

theorem norm_value (A : Matrix (Fin d) (Fin d) ℂ) :
    (norm A).value=ExactEVD.normReport (KSComplexTraceSqrt.realificationFin A) := by
  simp only [norm,KSNormReport.realify_value,ExactEVD.norm_value]

theorem norm_spectral_execution (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) :
    let Q := (KSNormReport.realify A).value
    ExactEVD.Executes Q (ExactEVD.compute Q).value (ExactEVD.compute Q).cost := by
  apply ExactEVD.compute_execution
  rw [KSNormReport.realify_value]
  exact KSComplexNorm.realificationFin_symmetric A hA

theorem norm_cost (A : Matrix (Fin d) (Fin d) ℂ) :
    (norm A).cost≤700*(d+d+1)^3 := by
  have hB := KSNormReport.realify_cost A
  have hr := ExactEVD.norm_cost (KSNormReport.realify A).value
  have hp : d+d+1≤(d+d+1)^3 := Nat.le_self_pow (by omega) _
  have hsq : (d+d)^2≤(d+d+1)^3 := by
    calc
      _ ≤ (d+d+1)^2 := Nat.pow_le_pow_left (by omega) 2
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
  dsimp only [norm]
  nlinarith

theorem actual_norm_value [Nonempty (Fin d)] (v : Fin N → Fin d → ℂ) (hd : 0<d)
    (hp : ∑ i,KSRankOne.atom (v i)=1) (s : WalkState N) :
    (norm (StatePotential.signedSum v s.coeff)).value=Walk.normReport v s := norm_value _

end SeamlessKS.RuntimeDirection
