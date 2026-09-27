import MatrixSpencer.KSEighthCountedHessian
import MatrixSpencer.RealRAMJacobiRayleigh

/-! Counted eighth covariance, including the finite calculation of its actual
matrix-dependent Jacobi budget. The polynomial ceiling cap is a fuel value for
computing that budget, and equality below proves that this implementation
returns the same covariance used in the walk's correctness proof. -/
open Matrix Set
open scoped BigOperators
noncomputable section
namespace MatrixSpencer.KSEighthCountedCovariance
open RealRAM RealRAM.JacobiIteration KSEighthLiveEnumeration
open KSEighthCountedPreparation KSEighthHessianQueries
variable {N d : ℕ}
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

def evaluate (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ)
    (θ η κ β : ℝ) (hd : 0<d) (q : Queries O v θ hd) (cap : ℕ) (x : Fin N → ℝ) :
    Counted (Matrix (Fin (count x)) (Fin (count x)) ℝ) :=
  let H := KSEighthCountedHessian.hessian O v θ η hd q x
  let A := (-κ⁻¹) • H.value
  let n := JacobiRayleigh.budget A β cap
  let P := KSCappedSimplex.matrixReport A (KSEighthManuscriptCovariance.target (count x)) n.value
  ⟨P.value,H.cost+n.cost+P.cost+6*(count x)^2+20⟩

def costBudget (N Q cap : ℕ) : ℕ :=
  1000*(N+1)^4*(Q+1)+(20*(N+1)^2+8*cap+30)+1500*(cap+1)*(N+1)^3+6*N^2+20

theorem evaluate_value (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ)
    (θ η κ β : ℝ) (hd : 0<d) (q : Queries O v θ hd) (cap : ℕ) (x : Fin N → ℝ)
    (hcap : KSJacobiIteration.iterationCount
      ((-κ⁻¹) • KSEighthConvexController.hessianReport O v θ η hd x) β≤cap) :
    (evaluate O v θ η κ β hd q cap x).value=
      KSEighthConvexController.covariance O v θ η κ β hd x := by
  have hb : KSJacobiIteration.denominator (count x)*KSJacobiStep.offDiagonalEnergy
      ((-κ⁻¹) • KSEighthConvexController.hessianReport O v θ η hd x)/β^2≤(cap:ℝ) :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr hcap)
  simp only [evaluate,KSEighthCountedHessian.hessian_value,JacobiRayleigh.budget_value _ _ _ hb,
    KSCappedSimplex.matrixReport_value,KSEighthConvexController.covariance,
    KSEighthManuscriptCovariance.covariance]

theorem budget_le_cap {m : ℕ} (A : Mat m) (β : ℝ) (cap : ℕ) :
    (JacobiRayleigh.budget A β cap).value≤cap := by
  simp only [JacobiRayleigh.budget,JacobiRayleigh.ceilLoop_value]
  exact min_le_left _ _

theorem evaluate_cost (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ)
    {θ η : ℝ} (hθ : 0<θ) (hη : 0<η) (κ β : ℝ) (hd : 0<d)
    (q : Queries O v θ hd) (cap : ℕ) {x : Fin N → ℝ}
    (hx : x∈ksCube (1/8)) (hk : 0<count x) {Q : ℕ}
    (hQ : ∀y∈ksCube (1/4),
      (q.retained (KSPotentialModels.live (1/8) x) (queryTolerance v θ η x) y).cost≤Q) :
    (evaluate O v θ η κ β hd q cap x).cost≤costBudget N Q cap := by
  have hH := KSEighthCountedHessian.hessian_cost O v hθ hη hd q hx hk hQ
  let A := (-κ⁻¹) • (KSEighthCountedHessian.hessian O v θ η hd q x).value
  have hn := JacobiRayleigh.budget_cost A β cap
  have hp := KSCappedSimplex.matrixReport_cost A (KSEighthManuscriptCovariance.target (count x))
    (JacobiRayleigh.budget A β cap).value
  have hnc := budget_le_cap A β cap
  have hkN := KSEighthManuscriptMovement.count_le x
  have hp' : (KSCappedSimplex.matrixReport A (KSEighthManuscriptCovariance.target (count x))
      (JacobiRayleigh.budget A β cap).value).cost≤1500*(cap+1)*(N+1)^3 := by
    apply hp.trans
    gcongr
  have hn' : (JacobiRayleigh.budget A β cap).cost≤20*(N+1)^2+8*cap+30 := by
    apply hn.trans
    gcongr
  change (KSEighthCountedHessian.hessian O v θ η hd q x).cost+
    (JacobiRayleigh.budget A β cap).cost+
    (KSCappedSimplex.matrixReport A (KSEighthManuscriptCovariance.target (count x))
      (JacobiRayleigh.budget A β cap).value).cost+6*(count x)^2+20≤_
  unfold costBudget
  gcongr

theorem actual_cap (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ)
    (hd : 0<d) (hp : (∑i,KSRankOne.atom (v i))=1) {x : Fin N → ℝ}
    (hx : x∈ksCube (1/8)) (hk : 0<count x) :
    KSJacobiIteration.iterationCount
      ((-(KSEighthManuscriptParameters.kappa N (Real.sqrt (KSEighthManuscriptPreprocess.epsilon v)))⁻¹) •
        KSEighthConvexController.hessianReport O v
          (ksRegularizerScale (KSEighthManuscriptPreprocess.epsilon v) (Fin d))
          (KSEighthManuscriptParameters.precision N (Real.sqrt (KSEighthManuscriptPreprocess.epsilon v))) hd x)
      (KSEighthManuscriptParameters.beta v (Real.sqrt (KSEighthManuscriptPreprocess.epsilon v))
        (ksRegularizerScale (KSEighthManuscriptPreprocess.epsilon v) (Fin d)))≤
      KSJacobiPolynomialBounds.eighthJacobi N d := by
  have hN := KSManuscriptInputPolynomialParameters.labels_pos v hd hp
  have hδ := Real.sqrt_pos.mpr (KSEighthManuscriptPreprocess.epsilon_pos v hd hp)
  have hη := KSEighthManuscriptParameters.precision_pos hN hδ
  have hη1 : KSEighthManuscriptParameters.precision N
      (Real.sqrt (KSEighthManuscriptPreprocess.epsilon v))≤1 := by
    have hδ1 := Real.sqrt_le_one.mpr (KSEighthManuscriptPreprocess.epsilon_le_one v hd hp)
    have hNl : (1:ℝ)≤N := by exact_mod_cast hN
    apply (KSEighthManuscriptParameters.precision_le hN hδ).trans
    unfold KSEighthManuscriptParameters.kappa
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  exact KSJacobiPolynomialBounds.eighth_iterationCount_le v hd hp x hk
    (KSEighthConvexValue.faceReport O v _ _ hd x)
    (KSEighthConvexReportMagnitude.faceReport_abs O v hd hp hx hk hη hη1)

end MatrixSpencer.KSEighthCountedCovariance
