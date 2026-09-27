import HigherRankKS.OptimizerResponse
import AugmentedHigherRankKS.FourBlockSmoothness
import AugmentedHigherRankKS.FourBlockOptimizer
import HigherRankKS.SourceScalarMetric

/-! Actual Hessian nondegeneracy and smoothness of the nonlinear optimized
potential. Concavity supplies the nonpositive source Hessian, and the trace
root supplies strict negativity in every nonzero density direction. -/

open Matrix MatrixSpencer HigherRankKS Filter Set
open scoped Topology BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff

noncomputable section
namespace AugmentedHigherRankKS

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
local instance potentialSmoothCStar {j : Type*} [Fintype j] [DecidableEq j] :
    CStarAlgebra (Matrix j j ℂ) := {}
local instance potentialSmoothNormedSpace :
    NormedSpace ℝ (selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ)) := inferInstance

def nonlinearSourceFidelity (A : ι → Matrix n n ℂ) (β : ℝ) (c : ι → ℝ)
    (S : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ)) : ℝ :=
  2 * fidelity (S : Matrix (FourSpin n) (FourSpin n) ℂ) (source A β c (S : Matrix (FourSpin n) (FourSpin n) ℂ))

def hermitianObjective (H : Matrix (FourSpin n) (FourSpin n) ℂ)
    (A : ι → Matrix n n ℂ) (β : ℝ) (c : ι → ℝ) (θ : ℝ)
    (S : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ)) : ℝ :=
  objective H A β c θ (S : Matrix (FourSpin n) (FourSpin n) ℂ)

theorem hermitianObjective_eq (H : Matrix (FourSpin n) (FourSpin n) ℂ)
    (A : ι → Matrix n n ℂ) (β : ℝ) (c : ι → ℝ) (θ : ℝ)
    (S : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ)) :
    hermitianObjective H A β c θ S =
      tracePairing H S + nonlinearSourceFidelity A β c S + tsallisPotential θ S := rfl

theorem contDiffAt_nonlinearSourceFidelity (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) (k : ℕ) (hk : 1 ≤ k)
    (c : ι → ℝ) (hc : ∀ i, 0 < c i)
    (S : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ))
    (hS : (S : Matrix (FourSpin n) (FourSpin n) ℂ).PosDef) :
    ContDiffAt ℝ ∞ (nonlinearSourceFidelity A ((1 : ℝ) / 2 ^ k) c) S :=
  (contDiffAt_jointSourceFidelity A hA k hk c hc S hS).comp S
    (contDiffAt_const.prodMk contDiffAt_id)

theorem contDiffAt_hermitianObjective (H : Matrix (FourSpin n) (FourSpin n) ℂ)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (k : ℕ) (hk : 1 ≤ k) (c : ι → ℝ) (hc : ∀ i, 0 < c i) (θ : ℝ)
    (S : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ))
    (hS : (S : Matrix (FourSpin n) (FourSpin n) ℂ).PosDef) :
    ContDiffAt ℝ ∞ (hermitianObjective H A ((1 : ℝ) / 2 ^ k) c θ) S :=
  (((tracePairing H).contDiff.contDiffAt).add
    (contDiffAt_nonlinearSourceFidelity A hA k hk c hc S hS)).add
      (contDiffAt_tsallisPotential θ S hS)

/-- Ordinary concavity of the actual nonlinear source term implies its
actual Hessian is negative semidefinite throughout the faithful cone. -/
theorem nonlinearSourceFidelity_hessian_nonpos (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) (k : ℕ) (hk : 1 ≤ k)
    (c : ι → ℝ) (hc : ∀ i, 0 < c i)
    (S X : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ))
    (hS : (S : Matrix (FourSpin n) (FourSpin n) ℂ).PosDef) :
    fderiv ℝ (fderiv ℝ (nonlinearSourceFidelity A ((1 : ℝ) / 2 ^ k) c)) S X X ≤ 0 := by
  let D : Set (selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ)) :=
    {T | (T : Matrix (FourSpin n) (FourSpin n) ℂ).PosDef}
  have hD : IsOpen D := isOpen_iff_mem_nhds.mpr fun T hT => eventually_posDef_of_posDef T hT
  have hβ : 0 < (1 : ℝ) / 2 ^ k := by positivity
  have hβ1 : (1 : ℝ) / 2 ^ k < 1 := by
    apply (div_lt_one (by positivity)).mpr
    exact one_lt_pow₀ (by norm_num) (by omega)
  have hconc : ConcaveOn ℝ D (nonlinearSourceFidelity A ((1 : ℝ) / 2 ^ k) c) := by
    refine ⟨?_, ?_⟩
    · intro T hT U hU a b ha hb hab
      exact posDef_convex_mixture hT hU ha hb hab
    · intro T hT U hU a b ha hb hab
      have h := fidelity_source_concave A hβ hβ1 (fun i => (hc i).le)
        hT.posSemidef hU.posSemidef ha hb hab
      change a * (2 * _) + b * (2 * _) ≤ 2 * _
      simp only [AddSubgroup.coe_add, selfAdjoint.val_smul]
      nlinarith
  exact SourceScalarMetric.hessian_nonpos_of_concave _ hD hconc
    (fun T hT => (contDiffAt_nonlinearSourceFidelity A hA k hk c hc T hT).differentiableAt
      (by simp)) hS
    ((contDiffAt_nonlinearSourceFidelity A hA k hk c hc S hS).of_le
      (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))) X

theorem fderiv_hermitianObjective (H : Matrix (FourSpin n) (FourSpin n) ℂ)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (k : ℕ) (hk : 1 ≤ k) (c : ι → ℝ) (hc : ∀ i, 0 < c i) (θ : ℝ)
    (S : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ))
    (hS : (S : Matrix (FourSpin n) (FourSpin n) ℂ).PosDef) :
    fderiv ℝ (hermitianObjective H A ((1 : ℝ) / 2 ^ k) c θ) S = tracePairing H +
      fderiv ℝ (nonlinearSourceFidelity A ((1 : ℝ) / 2 ^ k) c) S +
      fderiv ℝ (tsallisPotential θ) S := by
  have hf := (contDiffAt_nonlinearSourceFidelity A hA k hk c hc S hS).differentiableAt (by simp)
  have ht := (contDiffAt_tsallisPotential θ S hS).differentiableAt (by simp)
  exact (((tracePairing H).hasFDerivAt.add hf.hasFDerivAt).add ht.hasFDerivAt).fderiv

theorem hermitianObjective_hessian_apply (H : Matrix (FourSpin n) (FourSpin n) ℂ)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (k : ℕ) (hk : 1 ≤ k) (c : ι → ℝ) (hc : ∀ i, 0 < c i) (θ : ℝ)
    (S X Y : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ))
    (hS : (S : Matrix (FourSpin n) (FourSpin n) ℂ).PosDef) :
    fderiv ℝ (fderiv ℝ (hermitianObjective H A ((1 : ℝ) / 2 ^ k) c θ)) S X Y =
      fderiv ℝ (fderiv ℝ (nonlinearSourceFidelity A ((1 : ℝ) / 2 ^ k) c)) S X Y +
      fderiv ℝ (fderiv ℝ (tsallisPotential θ)) S X Y := by
  have hf := ((contDiffAt_nonlinearSourceFidelity A hA k hk c hc S hS).fderiv_right
    (by simp : (∞ : WithTop ℕ∞) + 1 ≤ ∞)).differentiableAt (by simp)
  have ht := ((contDiffAt_tsallisPotential θ S hS).fderiv_right
    (by simp : (∞ : WithTop ℕ∞) + 1 ≤ ∞)).differentiableAt (by simp)
  have hd := ((hasFDerivAt_const (𝕜 := ℝ) (tracePairing H) S).add hf.hasFDerivAt).add ht.hasFDerivAt
  simp only [zero_add] at hd
  have heq : fderiv ℝ (hermitianObjective H A ((1 : ℝ) / 2 ^ k) c θ) =ᶠ[𝓝 S]
      (fun T => tracePairing H + fderiv ℝ (nonlinearSourceFidelity A ((1 : ℝ) / 2 ^ k) c) T +
        fderiv ℝ (tsallisPotential θ) T) := by
    filter_upwards [eventually_posDef_of_posDef S hS] with T hT
    exact fderiv_hermitianObjective H A hA k hk c hc θ T hT
  rw [(hd.congr_of_eventuallyEq heq).fderiv]
  rfl

/-- The actual nonlinear objective has strictly negative Hessian at every
faithful density, with no Hessian sign supplied as a premise. -/
theorem hermitianObjective_hessian_neg (H : Matrix (FourSpin n) (FourSpin n) ℂ)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (k : ℕ) (hk : 1 ≤ k) (c : ι → ℝ) (hc : ∀ i, 0 < c i)
    (θ : ℝ) (hθ : 0 < θ)
    (S X : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ))
    (hS : (S : Matrix (FourSpin n) (FourSpin n) ℂ).PosDef) (hX : X ≠ 0) :
    fderiv ℝ (fderiv ℝ (hermitianObjective H A ((1 : ℝ) / 2 ^ k) c θ)) S X X < 0 := by
  rw [hermitianObjective_hessian_apply H A hA k hk c hc θ S X X hS]
  exact add_neg_of_nonpos_of_neg (nonlinearSourceFidelity_hessian_nonpos A hA k hk c hc S X hS)
    (OptimizerResponse.tsallis_hessian_neg θ hθ S X hS hX)

section Parameter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Smooth external center and positive live weights give joint smoothness
of the actual full-density objective. -/
theorem contDiffAt_objective_of_data
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (k : ℕ) (hk : 1 ≤ k) (θ : ℝ)
    (H : E → Matrix (FourSpin n) (FourSpin n) ℂ) (c : E → ι → ℝ) (x₀ : E)
    (hH : ContDiffAt ℝ ∞ H x₀) (hcs : ContDiffAt ℝ ∞ c x₀)
    (hc : ∀ i, 0 < c x₀ i)
    (S : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ))
    (hS : (S : Matrix (FourSpin n) (FourSpin n) ℂ).PosDef) :
    ContDiffAt ℝ ∞
      (fun P : E × selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ) =>
        hermitianObjective (H P.1) A ((1 : ℝ) / 2 ^ k) (c P.1) θ P.2) (x₀, S) := by
  have hcenter : ContDiffAt ℝ ∞
      (fun P : E × selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ) =>
        realTrace (H P.1 * (P.2 : Matrix (FourSpin n) (FourSpin n) ℂ))) (x₀, S) := by
    have hh : ContDiffAt ℝ ∞ (fun P : E × selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ) =>
        H P.1) (x₀, S) := hH.comp (x₀, S) contDiffAt_fst
    have hs : ContDiffAt ℝ ∞ (fun P : E × selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ) =>
        (P.2 : Matrix (FourSpin n) (FourSpin n) ℂ)) (x₀, S) :=
      (hermitianInclusion (n := FourSpin n)).contDiff.contDiffAt.comp (x₀, S) contDiffAt_snd
    exact realTraceCLM.contDiff.contDiffAt.comp (x₀, S) (hh.mul hs)
  have hmap : ContDiffAt ℝ ∞
      (fun P : E × selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ) => (c P.1, P.2)) (x₀, S) :=
    (hcs.comp (x₀, S) contDiffAt_fst).prodMk contDiffAt_snd
  have hfidelity := (contDiffAt_jointSourceFidelity A hA k hk (c x₀) hc S hS).comp (x₀, S) hmap
  have hroot : ContDiffAt ℝ ∞
      (fun P : E × selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ) => tsallisPotential θ P.2) (x₀, S) :=
    (contDiffAt_tsallisPotential θ S hS).comp (x₀, S) (f := Prod.snd) contDiffAt_snd
  exact (hcenter.add hfidelity).add hroot

variable [CompleteSpace E] [Nonempty n]
local instance potentialSmoothFinite : FiniteDimensional ℝ (selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ)) :=
  inferInstanceAs (FiniteDimensional ℝ (selfAdjoint.submodule ℝ (Matrix (FourSpin n) (FourSpin n) ℂ)))
local instance potentialSmoothTangentGroup : NormedAddCommGroup (densityTangent (n := FourSpin n)) := inferInstance
local instance potentialSmoothTangentSpace : NormedSpace ℝ (densityTangent (n := FourSpin n)) := inferInstance

/-- The concrete optimized potential is smooth under arbitrary smooth
external center and positive live-weight data. Attainment, faithfulness,
concavity, and strict negative curvature are all proved from the objective. -/
theorem contDiffAt_potential_of_positive_weights
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (k : ℕ) (hk : 1 ≤ k) (θ : ℝ) (hθ : 0 < θ)
    (H : E → Matrix (FourSpin n) (FourSpin n) ℂ) (c : E → ι → ℝ) (x₀ : E)
    (hH : ContDiffAt ℝ ∞ H x₀) (hcs : ContDiffAt ℝ ∞ c x₀)
    (hc : ∀ i, 0 < c x₀ i) :
    ContDiffAt ℝ ∞ (fun x => potential (H x) A ((1 : ℝ) / 2 ^ k) (c x) θ) x₀ := by
  have hβ : 0 < (1 : ℝ) / 2 ^ k := by positivity
  have hβ1 : (1 : ℝ) / 2 ^ k < 1 := by
    apply (div_lt_one (by positivity)).mpr
    exact one_lt_pow₀ (by norm_num) (by omega)
  obtain ⟨M, hM, hmax⟩ := exists_optimizer (H x₀) A hβ.le hβ1.le (fun i => (hc i).le) θ
  have hMpos := maximizer_posDef (H x₀) A hβ hβ1 (fun i => (hc i).le) hθ hM hmax
  let S : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ) := ⟨M, hM.1.isHermitian⟩
  let f : E × selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ) → ℝ := fun P =>
    hermitianObjective (H P.1) A ((1 : ℝ) / 2 ^ k) (c P.1) θ P.2
  have hf : ContDiffAt ℝ ∞ f (x₀, S) :=
    contDiffAt_objective_of_data A hA k hk θ H c x₀ hH hcs hc S hMpos
  have hnear : ∀ᶠ x in 𝓝 x₀, ∀ i, 0 < c x i := by
    apply Filter.eventually_all.mpr
    intro i
    exact ((continuous_apply i).continuousAt.comp hcs.continuousAt).eventually
      (IsOpen.mem_nhds isOpen_Ioi (hc i))
  have hconc : ∀ᶠ x in 𝓝 x₀,
      ConcaveOn ℝ (OptimizerResponse.densityDomain (n := FourSpin n)) (fun T => f (x, T)) := by
    filter_upwards [hnear] with x hx
    exact (concaveOn_objective (H x) A hβ hβ1 (fun i => (hx i).le) hθ.le).comp_linearMap
      (hermitianInclusion (n := FourSpin n)).toLinearMap
  have hnegative : ∀ X : densityTangent (n := FourSpin n), X ≠ 0 →
      fderiv ℝ (fderiv ℝ (fun Y => f (x₀, densityChart S Y))) 0 X X < 0 := by
    intro X hX
    change fderiv ℝ (fderiv ℝ (fun Y =>
      hermitianObjective (H x₀) A ((1 : ℝ) / 2 ^ k) (c x₀) θ (densityChart S Y))) 0 X X < 0
    rw [OptimizerResponse.densityChart_hessian_apply
      (hermitianObjective (H x₀) A ((1 : ℝ) / 2 ^ k) (c x₀) θ) S
      (contDiffAt_hermitianObjective (H x₀) A hA k hk (c x₀) hc θ S hMpos) X X]
    exact hermitianObjective_hessian_neg (H x₀) A hA k hk (c x₀) hc θ hθ S X hMpos
      (fun he => hX (Subtype.ext he))
  have hsmooth := OptimizerResponse.contDiffAt_density_sup f x₀ S hMpos hM.2 hf
    (fun T hT => hmax T hT) hconc hnegative
  have heq (x : E) :
      (fun T => f (x, T)) '' (OptimizerResponse.densityDomain (n := FourSpin n)) =
        objective (H x) A ((1 : ℝ) / 2 ^ k) (c x) θ '' densitySet := by
    ext y
    constructor
    · rintro ⟨T, hT, rfl⟩
      exact ⟨T, hT, rfl⟩
    · rintro ⟨T, hT, rfl⟩
      exact ⟨⟨T, hT.1.isHermitian⟩, hT, rfl⟩
  simpa only [heq, potential] using hsmooth

end Parameter


end AugmentedHigherRankKS
