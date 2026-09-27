import AugmentedHigherRankKS.FourBlockPotentialHessian
import AugmentedHigherRankKS.FourBlockSourceDerivatives
import AugmentedHigherRankKS.FourBlockSourceResponse
import AugmentedHigherRankKS.FourBlockProbe
import HigherRankKS.WeightedCompactIntegral

open Matrix MatrixSpencer HigherRankKS Filter Set
open scoped Topology BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
noncomputable section
namespace AugmentedHigherRankKS.ObjectiveResponse
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
local instance objectiveResponseCStar {j : Type*} [Fintype j] [DecidableEq j] :
    CStarAlgebra (Matrix j j ℂ) := {}
local instance objectiveResponseSpace :
    NormedSpace ℝ (selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ)) := inferInstance
local instance objectiveResponseTangentGroup : NormedAddCommGroup (densityTangent (n := FourSpin n)) := inferInstance
local instance objectiveResponseTangentSpace : NormedSpace ℝ (densityTangent (n := FourSpin n)) := inferInstance

/-- All scalar source acceleration terms, including the nonlinear density Hessian. -/
def sourceAcceleration (A : ι → Matrix n n ℂ) (β : ℝ) (c : ℝ → ι → ℝ)
    (Z : Matrix (FourSpin n) (FourSpin n) ℂ)
    (S X : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ)) : ℝ :=
  ∑ i, (iteratedDeriv 2 (fun t => c t i) 0 * SourceDerivative.probe β (A i) Z S +
    2 * deriv (fun t => c t i) 0 * fderiv ℝ (SourceDerivative.probe β (A i) Z) S X +
    c 0 i * fderiv ℝ (fderiv ℝ (SourceDerivative.probe β (A i) Z)) S X X)

/-- The scalar acceleration is the actual second derivative of the full source probe. -/
theorem sourceAcceleration_eq_second (A : ι → Matrix n n ℂ)
    (k : ℕ) (hk : 1 ≤ k) (c : ℝ → ι → ℝ) (hc : ContDiffAt ℝ 2 c 0)
    (Z : Matrix (FourSpin n) (FourSpin n) ℂ)
    (S X : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ))
    (hS : (S : Matrix (FourSpin n) (FourSpin n) ℂ).PosDef) :
    sourceAcceleration A ((1 : ℝ) / 2 ^ k) c Z S X =
      iteratedDeriv 2 (fun t => realTrace (Z * source A ((1 : ℝ) / 2 ^ k) (c t)
        ((S + t • X) : Matrix (FourSpin n) (FourSpin n) ℂ))) 0 := by
  have heq : (fun t => realTrace (Z * source A ((1 : ℝ) / 2 ^ k) (c t)
      ((S + t • X) : Matrix (FourSpin n) (FourSpin n) ℂ))) =
      (fun t => ∑ i, c t i • SourceDerivative.probe ((1 : ℝ) / 2 ^ k) (A i) Z (S + t • X)) := by
    funext t
    simp only [source, Matrix.mul_sum, Matrix.mul_smul, realTrace_sum, realTrace_smul,
      SourceDerivative.probe, smul_eq_mul]
    rfl
  rw [heq]
  have hprobe (i : ι) : ContDiffAt ℝ 2 (SourceDerivative.probe ((1 : ℝ) / 2 ^ k) (A i) Z) S :=
    (SourceDerivative.contDiffAt_probe (A i) Z k hk S hS).of_le
      (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have hci (i : ι) : ContDiffAt ℝ 2 (fun t => c t i) 0 :=
    (contDiff_apply ℝ ℝ i).contDiffAt.comp 0 hc
  have hpi (i : ι) : ContDiffAt ℝ 2
      (fun t : ℝ => SourceDerivative.probe ((1 : ℝ) / 2 ^ k) (A i) Z (S + t • X)) 0 := by
    have hb : ContDiffAt ℝ 2 (SourceDerivative.probe ((1 : ℝ) / 2 ^ k) (A i) Z)
        (S + (0 : ℝ) • X) := by simpa using hprobe i
    exact hb.comp 0 (f := fun t : ℝ => S + t • X) (by fun_prop)
  rw [SourceDerivatives.iteratedDeriv_two_finset_sum _ _ (fun i _ => (hci i).smul (hpi i))]
  apply Finset.sum_congr rfl
  intro i _
  rw [SourceDerivatives.iteratedDeriv_two_smul _ _ (hci i) (hpi i),
    SourceScalarMetric.iteratedDeriv_two_line _ S X (hprobe i)]
  have hd : HasFDerivAt (SourceDerivative.probe ((1 : ℝ) / 2 ^ k) (A i) Z)
      (fderiv ℝ (SourceDerivative.probe ((1 : ℝ) / 2 ^ k) (A i) Z) S) (S + (0 : ℝ) • X) := by
    simpa using ((hprobe i).differentiableAt (by norm_num)).hasFDerivAt
  have hl := hd.comp_hasDerivAt (0 : ℝ)
    ((hasDerivAt_const (0 : ℝ) S).add ((hasDerivAt_id (0 : ℝ)).smul_const X))
  have hld : deriv (fun t : ℝ => SourceDerivative.probe ((1 : ℝ) / 2 ^ k) (A i) Z (S + t • X)) 0 =
      fderiv ℝ (SourceDerivative.probe ((1 : ℝ) / 2 ^ k) (A i) Z) S X := by
    simpa only [Function.comp_def, Pi.add_apply, id_eq, one_smul, zero_add] using hl.deriv
  rw [hld]
  simp only [zero_smul, add_zero, smul_eq_mul]

/-- Exact mixed center term along affine center and full density variations. -/
theorem center_second_affine (H K : Matrix (FourSpin n) (FourSpin n) ℂ)
    (S X : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ)) :
    iteratedDeriv 2 (fun t : ℝ => tracePairing (H + t • K) (S + t • X)) 0 =
      2 * tracePairing K X := by
  have hh (t : ℝ) : HasDerivAt (fun t : ℝ => tracePairing (H + t • K)) (tracePairing K) t := by
    simpa only [one_smul, zero_add] using tracePairing.hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_const t H).add ((hasDerivAt_id t).smul_const K))
  have hs (t : ℝ) : HasDerivAt (fun t : ℝ => S + t • X) X t := by
    simpa only [one_smul, zero_add] using
      ((hasDerivAt_const t S).add ((hasDerivAt_id t).smul_const X))
  have hd : deriv (fun t : ℝ => tracePairing (H + t • K) (S + t • X)) =
      (fun t => tracePairing K (S + t • X) + tracePairing (H + t • K) X) := by
    funext t
    simpa only [add_comm] using ((hh t).clm_apply (hs t)).deriv
  have hfirst := (tracePairing K).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hs 0)
  have hsecond := (hh 0).clm_apply (hasDerivAt_const (0 : ℝ) X)
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, hd]
  simpa only [Function.comp_def, Pi.add_apply, map_zero, add_zero, two_mul] using
    (hfirst.add hsecond).deriv

/-- The actual reduced input curve for an arbitrary full Hermitian response. -/
def reducedCurve (A : ι → Matrix n n ℂ) (β : ℝ) (c : ℝ → ι → ℝ)
    (S X : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ)) (t : ℝ) :=
  jointReducedSourcePair A β (c t, S + t • X)

theorem reducedCurve_smooth (A : ι → Matrix n n ℂ)
    (k : ℕ) (hk : 1 ≤ k) (c : ℝ → ι → ℝ) (hc : ContDiffAt ℝ 2 c 0)
    (S X : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ))
    (hS : (S : Matrix (FourSpin n) (FourSpin n) ℂ).PosDef) :
    ContDiffAt ℝ 2 (reducedCurve A ((1 : ℝ) / 2 ^ k) c S X) 0 := by
  have h := (contDiffAt_jointReducedSourcePair A k hk (c 0) S hS).of_le
    (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have hb : ContDiffAt ℝ 2 (jointReducedSourcePair A ((1 : ℝ) / 2 ^ k))
      (c 0, S + (0 : ℝ) • X) := by simpa using h
  exact hb.comp 0 (f := fun t : ℝ => (c t, S + t • X))
    (hc.prodMk (by fun_prop))

/-- The compressed density retains affine zero acceleration. -/
theorem reducedCurve_first_acceleration (A : ι → Matrix n n ℂ)
    (k : ℕ) (hk : 1 ≤ k) (c : ℝ → ι → ℝ) (hc : ContDiffAt ℝ 2 c 0)
    (S X : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ))
    (hS : (S : Matrix (FourSpin n) (FourSpin n) ℂ).PosDef) :
    (iteratedDeriv 2 (reducedCurve A ((1 : ℝ) / 2 ^ k) c S X) 0).1 = 0 := by
  have he := WeightedCompactIntegral.iteratedDeriv_clm (ContinuousLinearMap.fst ℝ _ _)
    (reducedCurve_smooth A k hk c hc S X hS)
  change iteratedDeriv 2 (fun t => (reducedCurve A ((1 : ℝ) / 2 ^ k) c S X t).1) 0 =
    (iteratedDeriv 2 (reducedCurve A ((1 : ℝ) / 2 ^ k) c S X) 0).1 at he
  rw [← he]
  change iteratedDeriv 2 (fun t : ℝ =>
    hermitianRectangularCompressionCLM (sourceEmbedding A) (S + t • X)) 0 = 0
  have hd : deriv (fun t : ℝ => hermitianRectangularCompressionCLM (sourceEmbedding A)
      (S + t • X)) = fun _ => hermitianRectangularCompressionCLM (sourceEmbedding A) X := by
    funext t
    simpa only [one_smul, zero_add] using
      ((hermitianRectangularCompressionCLM (sourceEmbedding A)).hasFDerivAt.comp_hasDerivAt t
        ((hasDerivAt_const t S).add ((hasDerivAt_id t).smul_const X))).deriv
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, hd]
  simp

set_option maxHeartbeats 1000000 in
/-- Fixed transport pairing of the supported source acceleration is exactly
all scalar atom accelerations, with the full density response retained. -/
theorem reducedCurve_second_acceleration (A : ι → Matrix n n ℂ)
    (k : ℕ) (hk : 1 ≤ k) (c : ℝ → ι → ℝ) (hcs : ContDiffAt ℝ 2 c 0)
    (hc : ∀ i, 0 < c 0 i)
    (T : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ)
    (S X : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ))
    (hS : (S : Matrix (FourSpin n) (FourSpin n) ℂ).PosDef) :
    tracePairing T (iteratedDeriv 2 (reducedCurve A ((1 : ℝ) / 2 ^ k) c S X) 0).2 =
      sourceAcceleration A ((1 : ℝ) / 2 ^ k) c
        (sourceEmbedding A * T * (sourceEmbedding A)ᴴ) S X := by
  have hG := reducedCurve_smooth A k hk c hcs S X hS
  have hlin := WeightedCompactIntegral.iteratedDeriv_clm
    ((tracePairing T).comp (ContinuousLinearMap.snd ℝ _ _)) hG
  change iteratedDeriv 2 (fun t => tracePairing T
    (reducedCurve A ((1 : ℝ) / 2 ^ k) c S X t).2) 0 =
      tracePairing T (iteratedDeriv 2 (reducedCurve A ((1 : ℝ) / 2 ^ k) c S X) 0).2 at hlin
  have hcoeff : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ i, 0 < c t i := by
    apply Filter.eventually_all.mpr
    intro i
    exact ((continuous_apply i).continuousAt.comp hcs.continuousAt).eventually
      (isOpen_Ioi.mem_nhds (hc i))
  have hline : Tendsto (fun t : ℝ => S + t • X) (𝓝 0) (𝓝 S) := by
    simpa using ((continuous_const.add (continuous_id.smul continuous_const)).continuousAt :
      ContinuousAt (fun t : ℝ => S + t • X) 0).tendsto
  have heq : (fun t => tracePairing T (reducedCurve A ((1 : ℝ) / 2 ^ k) c S X t).2) =ᶠ[𝓝 0]
      (fun t => realTrace ((sourceEmbedding A * T * (sourceEmbedding A)ᴴ) *
        source A ((1 : ℝ) / 2 ^ k) (c t) ((S + t • X) : Matrix (FourSpin n) (FourSpin n) ℂ))) := by
    filter_upwards [hcoeff, hline.eventually (eventually_posDef_of_posDef S hS)] with t ht hSt
    change realTrace (T * ((jointReducedSourcePair A ((1 : ℝ) / 2 ^ k) (c t, S + t • X)).2 :
      Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ)) = _
    rw [jointReducedSourcePair_snd_coe A _ (c t, S + t • X)
      (fun i => (ht i).le) hSt.posSemidef]
    simpa only [compressedSource, Prod.fst, Prod.snd, AddSubgroup.coe_add, selfAdjoint.val_smul] using
      (KSSafeRetirement.realTrace_embedded_mul (sourceEmbedding A) T
        (source A ((1 : ℝ) / 2 ^ k) (c t) ((S + t • X) : Matrix (FourSpin n) (FourSpin n) ℂ))).symm
  exact hlin.symm.trans ((heq.iteratedDeriv_eq 2).trans
    (sourceAcceleration_eq_second A k hk c hcs _ S X hS).symm)


end AugmentedHigherRankKS.ObjectiveResponse
