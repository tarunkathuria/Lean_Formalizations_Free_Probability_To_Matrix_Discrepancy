import AugmentedHigherRankKS.FourBlockPotentialHessian

/-! A local optimizing branch constructed from the concrete four-block objective. -/
open Matrix MatrixSpencer HigherRankKS Filter Set
open scoped Topology BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
noncomputable section
namespace AugmentedHigherRankKS
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
local instance optimizerBranchCStar : CStarAlgebra (Matrix (FourSpin n) (FourSpin n) ℂ) := {}
local instance optimizerBranchSpace :
    NormedSpace ℝ (selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ)) := inferInstance
local instance optimizerBranchFinite : FiniteDimensional ℝ (selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ)) :=
  inferInstanceAs (FiniteDimensional ℝ (selfAdjoint.submodule ℝ (Matrix (FourSpin n) (FourSpin n) ℂ)))
local instance optimizerBranchTangentGroup : NormedAddCommGroup (densityTangent (n := FourSpin n)) := inferInstance
local instance optimizerBranchTangentSpace : NormedSpace ℝ (densityTangent (n := FourSpin n)) := inferInstance
local instance optimizerBranchTangentFinite : FiniteDimensional ℝ (densityTangent (n := FourSpin n)) := inferInstance

set_option maxHeartbeats 800000 in
theorem exists_local_optimizer_branch
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (k : ℕ) (hk : 1 ≤ k) (θ : ℝ) (hθ : 0 < θ)
    (H : ℝ → Matrix (FourSpin n) (FourSpin n) ℂ) (c : ℝ → ι → ℝ)
    (hH : ContDiffAt ℝ ∞ H 0) (hcs : ContDiffAt ℝ ∞ c 0)
    (hc : ∀ i, 0 < c 0 i)
    (S : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ))
    (hS : (S : Matrix (FourSpin n) (FourSpin n) ℂ) ∈ densitySet)
    (hmax : ∀ T ∈ densitySet, objective (H 0) A ((1 : ℝ) / 2 ^ k) (c 0) θ T ≤
      objective (H 0) A ((1 : ℝ) / 2 ^ k) (c 0) θ S) :
    let F := chartObjective H A ((1 : ℝ) / 2 ^ k) c θ S
    ∃ g : ℝ → densityTangent (n := FourSpin n),
      g 0 = 0 ∧ ContDiffAt ℝ ∞ g 0 ∧ ContDiffAt ℝ ∞ F (0, 0) ∧
      (∀ᶠ t in 𝓝 (0 : ℝ), ∀ X : densityTangent (n := FourSpin n),
        fderiv ℝ F (t, g t) (0, X) = 0) ∧
      (fun t => potential (H t) A ((1 : ℝ) / 2 ^ k) (c t) θ) =ᶠ[𝓝 0]
        (fun t => F (t, g t)) := by
  have hβ : 0 < (1 : ℝ) / 2 ^ k := by positivity
  have hβ1 : (1 : ℝ) / 2 ^ k < 1 := by
    apply (div_lt_one (by positivity)).mpr
    exact one_lt_pow₀ (by norm_num) (by omega)
  have hSpos := maximizer_posDef (H 0) A hβ hβ1 (fun i => (hc i).le) hθ hS hmax
  let F := chartObjective H A ((1 : ℝ) / 2 ^ k) c θ S
  have hchart : ContDiff ℝ ∞ (densityChart S) :=
    contDiff_const.add (densityTangent (n := FourSpin n)).subtypeL.contDiff
  have hmap : ContDiffAt ℝ ∞
      (fun P : ℝ × densityTangent (n := FourSpin n) => (P.1, densityChart S P.2)) (0, 0) :=
    contDiffAt_fst.prodMk (hchart.contDiffAt.comp (0, 0) (f := Prod.snd) contDiffAt_snd)
  have hF : ContDiffAt ℝ ∞ F (0, 0) := by
    have ho := contDiffAt_objective_of_data A hA k hk θ H c 0 hH hcs hc S hSpos
    have ho' : ContDiffAt ℝ ∞
        (fun P : ℝ × selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ) =>
          hermitianObjective (H P.1) A ((1 : ℝ) / 2 ^ k) (c P.1) θ P.2) (0, densityChart S 0) := by
      simpa using ho
    exact ho'.comp (0, 0) hmap
  have hslice : ContDiffAt ℝ ∞ (fun Y => F (0, Y)) 0 :=
    hF.comp 0 (contDiffAt_const.prodMk contDiffAt_id)
  have hlocal : IsLocalMax (fun Y => F (0, Y)) 0 := by
    filter_upwards [eventually_densityChart_mem S hSpos hS.2] with Y hY
    simpa only [F, chartObjective, densityChart_zero, hermitianObjective] using
      hmax (densityChart S Y) hY
  have hzero := hlocal.hasFDerivAt_eq_zero (hslice.differentiableAt (by simp)).hasFDerivAt
  have hnegative : ∀ X : densityTangent (n := FourSpin n), X ≠ 0 →
      fderiv ℝ (fderiv ℝ (fun Y => F (0, Y))) 0 X X < 0 := by
    intro X hX
    change fderiv ℝ (fderiv ℝ (fun Y =>
      hermitianObjective (H 0) A ((1 : ℝ) / 2 ^ k) (c 0) θ (densityChart S Y))) 0 X X < 0
    rw [OptimizerResponse.densityChart_hessian_apply
      (hermitianObjective (H 0) A ((1 : ℝ) / 2 ^ k) (c 0) θ) S
      (contDiffAt_hermitianObjective (H 0) A hA k hk (c 0) hc θ S hSpos) X X]
    exact hermitianObjective_hessian_neg (H 0) A hA k hk (c 0) hc θ hθ S X hSpos
      (fun he => hX (Subtype.ext he))
  obtain ⟨g, hg0, hg, hgstat⟩ :=
    OptimizerResponse.exists_smooth_stationary_branch F 0 hF hzero hnegative
  have hpositive : ∀ᶠ t in 𝓝 (0 : ℝ), (densityChart S (g t) : Matrix (FourSpin n) (FourSpin n) ℂ).PosDef := by
    have hcont : Tendsto (fun t => densityChart S (g t)) (𝓝 0) (𝓝 S) := by
      simpa only [Function.comp_def, hg0, densityChart_zero] using (hchart.contDiffAt.comp 0 hg).continuousAt.tendsto
    exact hcont.eventually (eventually_posDef_of_posDef S hSpos)
  have hcoeff : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ i, 0 < c t i := by
    apply Filter.eventually_all.mpr
    intro i
    exact ((continuous_apply i).continuousAt.comp hcs.continuousAt).eventually
      (isOpen_Ioi.mem_nhds (hc i))
  have hvalue : (fun t => potential (H t) A ((1 : ℝ) / 2 ^ k) (c t) θ) =ᶠ[𝓝 0]
      (fun t => F (t, g t)) := by
    filter_upwards [hpositive, hcoeff, hgstat] with t htpos htcoeff htstat
    let T := densityChart S (g t)
    have hT : (T : Matrix (FourSpin n) (FourSpin n) ℂ) ∈ densitySet :=
      ⟨htpos.posSemidef, (densityChart_trace S (g t)).trans hS.2⟩
    have hd := (contDiffAt_hermitianObjective (H t) A hA k hk (c t) htcoeff θ T htpos).differentiableAt
      (by simp)
    have hstationary : densityTangentRestriction
        (fderiv ℝ (hermitianObjective (H t) A ((1 : ℝ) / 2 ^ k) (c t) θ) T) = 0 := by
      have he := (hd.hasFDerivAt.comp (g t) (hasStrictFDerivAt_densityChart S (g t)).hasFDerivAt).fderiv
      change fderiv ℝ (fun Y => F (t, Y)) (g t) =
        densityTangentRestriction (fderiv ℝ (hermitianObjective (H t) A ((1 : ℝ) / 2 ^ k) (c t) θ) T) at he
      exact he.symm.trans htstat
    have hm := OptimizerResponse.stationary_isMaxOn
      (hermitianObjective (H t) A ((1 : ℝ) / 2 ^ k) (c t) θ)
      ((concaveOn_objective (H t) A hβ hβ1 (fun i => (htcoeff i).le) hθ.le).comp_linearMap
        (hermitianInclusion (n := FourSpin n)).toLinearMap) T hT hd hstationary
    exact potential_eq_of_optimizer (H t) A ((1 : ℝ) / 2 ^ k) (c t) θ hT
      (fun U hU => hm ⟨U, hU.1.isHermitian⟩ hU)
  have hgraph : ContDiffAt ℝ ∞ (fun t => (t, g t)) 0 := contDiffAt_id.prodMk hg
  have hF' : ContDiffAt ℝ ∞ F (0, g 0) := by simpa only [hg0] using hF
  have hdiff : ∀ᶠ t in 𝓝 (0 : ℝ), DifferentiableAt ℝ F (t, g t) := by
    filter_upwards [hgraph.continuousAt.eventually
      ((hF'.of_le (by simp : (1 : WithTop ℕ∞) ≤ ∞)).eventually (by norm_num))] with t ht
    exact ht.differentiableAt le_rfl
  have hstationary : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ X : densityTangent (n := FourSpin n),
      fderiv ℝ F (t, g t) (0, X) = 0 := by
    filter_upwards [hdiff, hgstat] with t ht hst X
    have he := OptimizerHessian.vertical_fderiv F t (g t) ht
    rw [hst] at he
    exact (DFunLike.congr_fun he X).symm
  exact ⟨g, hg0, hg, hF, hstationary, hvalue⟩

end AugmentedHigherRankKS
