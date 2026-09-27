import MatrixSpencer.KSEighthCountedRun
import MatrixSpencer.KSEighthConvexExplicit
import MatrixSpencer.KSConvexQueryBudgets

/-!
# Actual-input eighth online evaluator

All covariance and Jacobi budget hypotheses in the generic counted run are
discharged here from the original Parseval input. The only intermediate cost
inputs left in this module concern the explicitly counted SDP query record;
the owner-program compiler and permitted solver instantiate those separately.
-/
open Set
open scoped BigOperators
noncomputable section
namespace MatrixSpencer.KSEighthConvexRuntime
open KSEighthCountedPreparation KSEighthManuscriptPreprocess
open KSEighthManuscriptRun KSEighthLiveEnumeration
open KSEighthWalkRun (terminal)
variable {N d : ℕ}

def controller (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ)
    (hd : 0<d) (hp : (∑i,KSRankOne.atom (v i))=1) : KSEighthManuscriptRun.Controller N :=
  KSEighthConvexController.controller O v (δ:=Real.sqrt (epsilon v))
    (θ:=ksRegularizerScale (epsilon v) (Fin d))
    (KSManuscriptInputPolynomialParameters.labels_pos v hd hp)
    (Real.sqrt_pos.mpr (epsilon_pos v hd hp))
    (by letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩; exact ksRegularizerScale_pos (n:=Fin d) (epsilon_pos v hd hp)) hd

def operations (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ)
    (hd : 0<d) (hp : (∑i,KSRankOne.atom (v i))=1)
    (q : Queries O v (ksRegularizerScale (epsilon v) (Fin d)) hd) :
    KSEighthCountedRun.Operations (controller O v hd hp) where
  report := q.state (KSEighthManuscriptParameters.rho N (Real.sqrt (epsilon v))/8)
  report_value := q.state_value _
  covariance := fun s _ => KSEighthCountedCovariance.evaluate O v
    (ksRegularizerScale (epsilon v) (Fin d))
    (KSEighthManuscriptParameters.precision N (Real.sqrt (epsilon v)))
    (KSEighthManuscriptParameters.kappa N (Real.sqrt (epsilon v)))
    (KSEighthManuscriptParameters.beta v (Real.sqrt (epsilon v))
      (ksRegularizerScale (epsilon v) (Fin d))) hd q (KSJacobiPolynomialBounds.eighthJacobi N d) s.coeff
  covariance_value := fun s hs => KSEighthCountedCovariance.evaluate_value O v _ _ _ _ hd q _ s.coeff
    (KSEighthCountedCovariance.actual_cap O v hd hp s.cube (count_pos_of_not_vertex s.cube hs))

def covarianceBudget (N d Q : ℕ) : ℕ :=
  KSEighthCountedCovariance.costBudget N Q (KSJacobiPolynomialBounds.eighthJacobi N d)

theorem covariance_cost (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ)
    (hd : 0<d) (hp : (∑i,KSRankOne.atom (v i))=1)
    (q : Queries O v (ksRegularizerScale (epsilon v) (Fin d)) hd) {Q : ℕ}
    (hQ : ∀x∈ksCube (1/8),0<count x→∀y∈ksCube (1/4),
      (q.retained (KSPotentialModels.live (1/8) x)
        (KSEighthHessianQueries.queryTolerance v (ksRegularizerScale (epsilon v) (Fin d))
          (KSEighthManuscriptParameters.precision N (Real.sqrt (epsilon v))) x) y).cost≤Q)
    (s : State (controller O v hd hp)) (hs : ¬terminal s) :
    ((operations O v hd hp q).covariance s hs).cost≤covarianceBudget N d Q := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  have hN := KSManuscriptInputPolynomialParameters.labels_pos v hd hp
  have hδ := Real.sqrt_pos.mpr (epsilon_pos v hd hp)
  have hθ := ksRegularizerScale_pos (n:=Fin d) (epsilon_pos v hd hp)
  exact KSEighthCountedCovariance.evaluate_cost O v hθ
    (KSEighthManuscriptParameters.precision_pos hN hδ) _ _ hd q _ s.cube
    (count_pos_of_not_vertex s.cube hs) (hQ s.coeff s.cube (count_pos_of_not_vertex s.cube hs))

def pathBudget (N d Q T : ℕ) : ℕ :=
  T*((23*N+5)+KSEighthCountedRun.childBudget N Q (covarianceBudget N d Q)+3)+(23*N+5)+2

theorem leaf_execution (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ)
    (hd : 0<d) (hp : (∑i,KSRankOne.atom (v i))=1)
    (q : Queries O v (ksRegularizerScale (epsilon v) (Fin d)) hd) {Q : ℕ}
    (hstate : ∀x∈ksCube (1/8),
      (q.state (KSEighthManuscriptParameters.rho N (Real.sqrt (epsilon v))/8) x).cost≤Q)
    (hface : ∀x∈ksCube (1/8),0<count x→∀y∈ksCube (1/4),
      (q.retained (KSPotentialModels.live (1/8) x)
        (KSEighthHessianQueries.queryTolerance v (ksRegularizerScale (epsilon v) (Fin d))
          (KSEighthManuscriptParameters.precision N (Real.sqrt (epsilon v))) x) y).cost≤Q)
    (T : ℕ) (s : State (controller O v hd hp))
    (l : (KSEighthManuscriptRun.run (controller O v hd hp) T s).Leaves) :
    ∃k r,KSOnlinePathRuntime.Executes
      (KSEighthCountedRun.evaluator (controller O v hd hp) (operations O v hd hp q)
        hstate (covariance_cost O v hd hp q hface)) T s
      ((KSEighthManuscriptRun.run (controller O v hd hp) T s).leafState l) k r ∧
      k≤pathBudget N d Q T ∧ r≤T :=
  KSEighthCountedRun.leaf_execution (controller O v hd hp) (operations O v hd hp q)
    hstate (covariance_cost O v hd hp q hface) T s l

end MatrixSpencer.KSEighthConvexRuntime
