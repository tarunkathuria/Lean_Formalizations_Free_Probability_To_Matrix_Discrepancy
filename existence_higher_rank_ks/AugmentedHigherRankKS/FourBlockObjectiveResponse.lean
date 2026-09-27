import AugmentedHigherRankKS.FourBlockObjectiveAffineSplit

open Matrix MatrixSpencer HigherRankKS Filter Set
open scoped Topology BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
noncomputable section
namespace AugmentedHigherRankKS.ObjectiveResponse
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
local instance objectiveResponseFinalCStar {j : Type*} [Fintype j] [DecidableEq j] :
    CStarAlgebra (Matrix j j ℂ) := {}
local instance objectiveResponseFinalSpace :
    NormedSpace ℝ (selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ)) := inferInstance
local instance objectiveResponseFinalTangentGroup : NormedAddCommGroup (densityTangent (n := FourSpin n)) := inferInstance
local instance objectiveResponseFinalTangentSpace : NormedSpace ℝ (densityTangent (n := FourSpin n)) := inferInstance

set_option maxHeartbeats 500000 in
/-- The actual affine fidelity response is source acceleration minus mismatch energy. -/
theorem fidelity_second_affine (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) (k : ℕ) (hk : 1 ≤ k)
    (c : ℝ → ι → ℝ) (hcs : ContDiffAt ℝ 2 c 0) (hc : ∀ i, 0 < c 0 i)
    (S X : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ))
    (hS : (S : Matrix (FourSpin n) (FourSpin n) ℂ).PosDef) :
    iteratedDeriv 2 (fun t : ℝ => jointSourceFidelity A ((1 : ℝ) / 2 ^ k) (c t, S + t • X)) 0 =
      sourceAcceleration A ((1 : ℝ) / 2 ^ k) c
        (sourceEmbedding A * responseTransport A ((1 : ℝ) / 2 ^ k) (c 0) S * (sourceEmbedding A)ᴴ) S X -
      responseEnergy A hA k hk c hc S X hS := by
  let P := fun t : ℝ => (c t, S + t • X)
  have hP : ContDiffAt ℝ 2 P 0 := hcs.prodMk (by fun_prop)
  have hP0 : P 0 = (c 0, S) := by simp [P]
  have hfid := SourceResponse.nonlinear_fidelity_second_curve_energy A hA k hk P hP
    (by simpa only [hP0] using hc) (by simpa only [hP0] using hS)
  dsimp only at hfid
  simp only [P, zero_smul, add_zero] at hfid
  change iteratedDeriv 2 (fun t => jointSourceFidelity A ((1 : ℝ) / 2 ^ k) (P t)) 0 =
    -_ + realTrace (_ * ((iteratedDeriv 2 (reducedCurve A ((1 : ℝ) / 2 ^ k) c S X) 0).1 :
      Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ)) +
      tracePairing _ (iteratedDeriv 2 (reducedCurve A ((1 : ℝ) / 2 ^ k) c S X) 0).2 at hfid
  rw [reducedCurve_first_acceleration A k hk c hcs S X hS,
    reducedCurve_second_acceleration A k hk c hcs hc _ S X hS] at hfid
  simp only [ZeroMemClass.coe_zero, Matrix.mul_zero, realTrace_zero, add_zero] at hfid
  change iteratedDeriv 2 (fun t => jointSourceFidelity A ((1 : ℝ) / 2 ^ k) (P t)) 0 = _
  rw [hfid]
  unfold responseEnergy responseTransport reducedCurve
  ring


set_option maxHeartbeats 1000000 in
/-- Exact response for the actual objective along any full density variation.
The supported inverse-Sylvester energy and every source acceleration term are explicit. -/
theorem objective_second_affine (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) (k : ℕ) (hk : 1 ≤ k)
    (c : ℝ → ι → ℝ) (hcs : ContDiffAt ℝ 2 c 0) (hc : ∀ i, 0 < c 0 i)
    (H K : Matrix (FourSpin n) (FourSpin n) ℂ) (θ : ℝ)
    (S X : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ))
    (hS : (S : Matrix (FourSpin n) (FourSpin n) ℂ).PosDef) :
    iteratedDeriv 2 (fun t : ℝ => hermitianObjective (H + t • K) A ((1 : ℝ) / 2 ^ k)
      (c t) θ (S + t • X)) 0 =
      2 * tracePairing K X +
      sourceAcceleration A ((1 : ℝ) / 2 ^ k) c
        (sourceEmbedding A * responseTransport A ((1 : ℝ) / 2 ^ k) (c 0) S * (sourceEmbedding A)ᴴ) S X +
      fderiv ℝ (fderiv ℝ (tsallisPotential θ)) S X X -
      responseEnergy A hA k hk c hc S X hS := by
  rw [objective_second_split A hA k hk c hcs hc H K θ S X hS,
    fidelity_second_affine A hA k hk c hcs hc S X hS]
  ring

set_option maxHeartbeats 800000 in
/-- The full chart Hessian is the affine joint response in the corresponding
trace-zero Hermitian direction. -/
theorem chart_hessian_eq_affine_second (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) (k : ℕ) (hk : 1 ≤ k)
    (c : ℝ → ι → ℝ) (hcs : ContDiffAt ℝ ∞ c 0) (hc : ∀ i, 0 < c 0 i)
    (H K : Matrix (FourSpin n) (FourSpin n) ℂ) (θ : ℝ)
    (S : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ))
    (X : densityTangent (n := FourSpin n))
    (hS : (S : Matrix (FourSpin n) (FourSpin n) ℂ).PosDef) :
    fderiv ℝ (fderiv ℝ (chartObjective (fun t : ℝ => H + t • K) A ((1 : ℝ) / 2 ^ k) c θ S))
      (0, 0) (1, X) (1, X) =
    iteratedDeriv 2 (fun t : ℝ => hermitianObjective (H + t • K) A ((1 : ℝ) / 2 ^ k)
      (c t) θ (S + t • (X : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ)))) 0 := by
  have hobj := contDiffAt_objective_of_data A hA k hk θ
    (fun t : ℝ => H + t • K) c 0 (by fun_prop) hcs hc S hS
  have hchart : ContDiff ℝ ∞ (densityChart S) :=
    contDiff_const.add (densityTangent (n := FourSpin n)).subtypeL.contDiff
  have hmap : ContDiffAt ℝ ∞
      (fun P : ℝ × densityTangent (n := FourSpin n) => (P.1, densityChart S P.2)) (0, 0) :=
    contDiffAt_fst.prodMk (hchart.contDiffAt.comp (0, 0) (f := Prod.snd) contDiffAt_snd)
  have hb : ContDiffAt ℝ ∞
      (fun P : ℝ × selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ) =>
        hermitianObjective (H + P.1 • K) A ((1 : ℝ) / 2 ^ k) (c P.1) θ P.2)
      (0, densityChart S 0) := by simpa using hobj
  have hf : ContDiffAt ℝ 2
      (chartObjective (fun t : ℝ => H + t • K) A ((1 : ℝ) / 2 ^ k) c θ S) (0, 0) :=
    by
      have hh := hb.comp (0, 0) hmap
      exact hh.of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  rw [← SourceScalarMetric.iteratedDeriv_two_line _ (0, 0) (1, X) hf]
  congr 1
  funext t
  simp only [chartObjective, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul, mul_one, zero_add, densityChart, Submodule.coe_smul]

end AugmentedHigherRankKS.ObjectiveResponse
