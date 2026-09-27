import MatrixSpencer.DyadicDensityCalculus
import MatrixSpencer.DyadicDensityFaithfulness
import MatrixSpencer.OptimizerResponse

/-! The actual dyadic density maximizer and potential. All choices are made
from proved compact attainment; all source channels may be singular. -/
open Matrix Set Filter Topology
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
namespace MatrixSpencer
noncomputable section
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
local instance dyadicOptimizerCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance dyadicOptimizerSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance

theorem continuousOn_dyadicDensityObjective (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (m : ℕ) (θ : ℝ) : ContinuousOn (dyadicDensityObjective H B m θ) densitySet := by
  apply continuousOn_iff_continuous_restrict.mpr
  have hs : Continuous (fun S : (densitySet : Set (Matrix n n ℂ)) => (S : Matrix n n ℂ)) :=
    continuous_subtype_val
  have hf := continuous_fidelity_of_psd hs ((continuous_krausChannel B).comp hs)
    (fun S => S.property.1) (fun S => krausChannel_posSemidef B S.property.1)
  have hr := continuousOn_iff_continuous_restrict.mp (continuousOn_density_dyadicTsallisRegularizer (n := n) m θ)
  exact ((continuous_realTrace.comp (continuous_const.mul hs)).add
    (continuous_const.mul hf)).add hr

theorem exists_dyadicDensityOptimizer [Nonempty n] (H : Matrix n n ℂ)
    (B : ι → Matrix n n ℂ) (m : ℕ) (θ : ℝ) :
    ∃ S ∈ densitySet, ∀ T ∈ densitySet,
      dyadicDensityObjective H B m θ T ≤ dyadicDensityObjective H B m θ S :=
  isCompact_densitySet.exists_isMaxOn densitySet_nonempty (continuousOn_dyadicDensityObjective H B m θ)

def dyadicDensityPotential (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ) (m : ℕ) (θ : ℝ) : ℝ :=
  sSup (dyadicDensityObjective H B m θ '' densitySet)

def dyadicDensityOptimizer [Nonempty n] (H : Matrix n n ℂ)
    (B : ι → Matrix n n ℂ) (m : ℕ) (θ : ℝ) : Matrix n n ℂ :=
  (exists_dyadicDensityOptimizer H B m θ).choose

theorem dyadicDensityOptimizer_mem [Nonempty n] (H : Matrix n n ℂ)
    (B : ι → Matrix n n ℂ) (m : ℕ) (θ : ℝ) :
    dyadicDensityOptimizer H B m θ ∈ densitySet :=
  (exists_dyadicDensityOptimizer H B m θ).choose_spec.1

theorem dyadicDensityOptimizer_isMaxOn [Nonempty n] (H : Matrix n n ℂ)
    (B : ι → Matrix n n ℂ) (m : ℕ) (θ : ℝ) :
    ∀ T ∈ densitySet, dyadicDensityObjective H B m θ T ≤
      dyadicDensityObjective H B m θ (dyadicDensityOptimizer H B m θ) :=
  (exists_dyadicDensityOptimizer H B m θ).choose_spec.2

def hermitianDyadicDensityOptimizer [Nonempty n] (H : Matrix n n ℂ)
    (B : ι → Matrix n n ℂ) (m : ℕ) (θ : ℝ) : selfAdjoint (Matrix n n ℂ) :=
  ⟨dyadicDensityOptimizer H B m θ, (dyadicDensityOptimizer_mem H B m θ).1.isHermitian⟩

def hermitianDyadicDensityPotential (B : ι → Matrix n n ℂ) (m : ℕ) (θ : ℝ)
    (H : selfAdjoint (Matrix n n ℂ)) : ℝ := dyadicDensityPotential H B m θ

theorem hermitianDyadicDensityOptimizer_trace [Nonempty n] (H : Matrix n n ℂ)
    (B : ι → Matrix n n ℂ) (m : ℕ) (θ : ℝ) :
    realTrace (hermitianDyadicDensityOptimizer H B m θ : Matrix n n ℂ) = 1 :=
  (dyadicDensityOptimizer_mem H B m θ).2

theorem dyadicDensityPotential_eq_of_maximizer (H : Matrix n n ℂ)
    (B : ι → Matrix n n ℂ) (m : ℕ) (θ : ℝ) {S : Matrix n n ℂ} (hS : S ∈ densitySet)
    (hmax : ∀ T ∈ densitySet, dyadicDensityObjective H B m θ T ≤ dyadicDensityObjective H B m θ S) :
    dyadicDensityPotential H B m θ = dyadicDensityObjective H B m θ S := by
  have hg : IsGreatest (dyadicDensityObjective H B m θ '' densitySet) (dyadicDensityObjective H B m θ S) := by
    refine ⟨⟨S, hS, rfl⟩, ?_⟩
    rintro z ⟨T, hT, rfl⟩
    exact hmax T hT
  exact hg.csSup_eq

theorem dyadicDensityPotential_eq_optimizer [Nonempty n] (H : Matrix n n ℂ)
    (B : ι → Matrix n n ℂ) (m : ℕ) (θ : ℝ) :
    dyadicDensityPotential H B m θ =
      dyadicDensityObjective H B m θ (dyadicDensityOptimizer H B m θ) :=
  dyadicDensityPotential_eq_of_maximizer H B m θ (dyadicDensityOptimizer_mem H B m θ)
    (dyadicDensityOptimizer_isMaxOn H B m θ)

theorem hermitianDyadicDensityPotential_eq_objective [Nonempty n]
    (H : selfAdjoint (Matrix n n ℂ)) (B : ι → Matrix n n ℂ) (m : ℕ) (θ : ℝ) :
    hermitianDyadicDensityPotential B m θ H = hermitianDyadicDensityObjective
      (H : Matrix n n ℂ) B m θ (hermitianDyadicDensityOptimizer (H : Matrix n n ℂ) B m θ) := by
  change dyadicDensityPotential (H : Matrix n n ℂ) B m θ =
    dyadicDensityObjective (H : Matrix n n ℂ) B m θ (dyadicDensityOptimizer (H : Matrix n n ℂ) B m θ)
  exact dyadicDensityPotential_eq_optimizer (H : Matrix n n ℂ) B m θ

theorem dyadicDensityObjective_le_potential [Nonempty n] (H : Matrix n n ℂ)
    (B : ι → Matrix n n ℂ) (m : ℕ) (θ : ℝ) {S : Matrix n n ℂ} (hS : S ∈ densitySet) :
    dyadicDensityObjective H B m θ S ≤ dyadicDensityPotential H B m θ := by
  rw [dyadicDensityPotential_eq_optimizer]
  exact dyadicDensityOptimizer_isMaxOn H B m θ S hS

theorem dyadicDensityObjective_center_difference (H H' S : Matrix n n ℂ)
    (B : ι → Matrix n n ℂ) (m : ℕ) (θ : ℝ) :
    dyadicDensityObjective H' B m θ S = dyadicDensityObjective H B m θ S + realTrace ((H' - H) * S) := by
  simp only [dyadicDensityObjective, Matrix.sub_mul, realTrace_sub]
  ring

theorem dyadicDensityPotential_supporting_plane [Nonempty n] (H H' : Matrix n n ℂ)
    (B : ι → Matrix n n ℂ) (m : ℕ) (θ : ℝ) {S : Matrix n n ℂ} (hS : S ∈ densitySet)
    (hmax : ∀ T ∈ densitySet, dyadicDensityObjective H B m θ T ≤ dyadicDensityObjective H B m θ S) :
    dyadicDensityPotential H B m θ + realTrace ((H' - H) * S) ≤ dyadicDensityPotential H' B m θ := by
  rw [dyadicDensityPotential_eq_of_maximizer H B m θ hS hmax,
    ← dyadicDensityObjective_center_difference]
  exact dyadicDensityObjective_le_potential H' B m θ hS

theorem concaveOn_dyadicDensityObjective (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (hθ : 0 < θ) :
    ConcaveOn ℝ densitySet (dyadicDensityObjective H B m θ) := by
  refine ⟨densitySet_convex, ?_⟩
  intro S hS T hT a b ha hb hab
  have hf := fidelity_concave hS.1 hT.1 (krausChannel_posSemidef B hS.1)
    (krausChannel_posSemidef B hT.1) ha hb hab
  have hr := dyadicTsallisRegularizer_concave m hm θ hθ hS.1 hT.1 ha hb hab
  simp only [dyadicDensityObjective, krausChannel_weighted_add, Matrix.mul_add,
    Matrix.mul_smul, realTrace_add, realTrace_smul, smul_eq_mul]
  nlinarith

theorem dyadicDensityObjective_strict_concave_posDef (H : Matrix n n ℂ)
    (B : ι → Matrix n n ℂ) (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (hθ : 0 < θ)
    {S T : Matrix n n ℂ} (hS : S.PosDef) (hT : T.PosDef) (hne : S ≠ T)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    a * dyadicDensityObjective H B m θ S + b * dyadicDensityObjective H B m θ T <
      dyadicDensityObjective H B m θ (a • S + b • T) := by
  have hf := fidelity_concave hS.posSemidef hT.posSemidef
    (krausChannel_posSemidef B hS.posSemidef) (krausChannel_posSemidef B hT.posSemidef) ha.le hb.le hab
  have hr := dyadicTsallisRegularizer_strict_concave_posDef m hm θ hθ hS hT hne ha hb hab
  simp only [dyadicDensityObjective, krausChannel_weighted_add, Matrix.mul_add,
    Matrix.mul_smul, realTrace_add, realTrace_smul]
  nlinarith

theorem dyadicDensity_maximizers_eq_of_posDef (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (hθ : 0 < θ) {S T : Matrix n n ℂ}
    (hS : S ∈ densitySet) (hT : T ∈ densitySet) (hSP : S.PosDef) (hTP : T.PosDef)
    (hsmax : ∀ U ∈ densitySet, dyadicDensityObjective H B m θ U ≤ dyadicDensityObjective H B m θ S)
    (htmax : ∀ U ∈ densitySet, dyadicDensityObjective H B m θ U ≤ dyadicDensityObjective H B m θ T) :
    S = T := by
  by_contra hne
  have hmix := densitySet_convex hS hT (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have hstrict := dyadicDensityObjective_strict_concave_posDef H B m hm θ hθ hSP hTP hne
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  have hs := hsmax ((1 / 2 : ℝ) • S + (1 / 2 : ℝ) • T) hmix
  have ht := htmax ((1 / 2 : ℝ) • S + (1 / 2 : ℝ) • T) hmix
  linarith

theorem regularizedOwnerPotential_eq_dyadicDensityPotential [DecidableEq ι]
    (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (m : ℕ) (θ : ℝ) :
    regularizedOwnerPotential H A C (dyadicTsallisRegularizer m θ) =
      dyadicDensityPotential H (covarianceKraus A C) m θ := by
  unfold regularizedOwnerPotential dyadicDensityPotential
  congr 2
  funext S
  exact regularizedOwnerObjective_eq_dyadicDensityObjective H A hA hC m θ S

theorem dyadicDensityOptimizer_posDef [Nonempty n] (H : Matrix n n ℂ)
    (B : ι → Matrix n n ℂ) (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (hθ : 0 < θ) :
    (dyadicDensityOptimizer H B m θ).PosDef :=
  dyadicDensity_maximizer_posDef H B hm hθ (dyadicDensityOptimizer_mem H B m θ)
    (dyadicDensityOptimizer_isMaxOn H B m θ)

theorem hermitianDyadicDensityOptimizer_posDef [Nonempty n] (H : Matrix n n ℂ)
    (B : ι → Matrix n n ℂ) (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (hθ : 0 < θ) :
    (hermitianDyadicDensityOptimizer H B m θ : Matrix n n ℂ).PosDef :=
  dyadicDensityOptimizer_posDef H B m hm θ hθ

theorem dyadicDensity_maximizers_eq (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (hθ : 0 < θ) {S T : Matrix n n ℂ}
    (hS : S ∈ densitySet) (hT : T ∈ densitySet)
    (hsmax : ∀ U ∈ densitySet, dyadicDensityObjective H B m θ U ≤ dyadicDensityObjective H B m θ S)
    (htmax : ∀ U ∈ densitySet, dyadicDensityObjective H B m θ U ≤ dyadicDensityObjective H B m θ T) :
    S = T :=
  dyadicDensity_maximizers_eq_of_posDef H B m hm θ hθ hS hT
    (dyadicDensity_maximizer_posDef H B hm hθ hS hsmax)
    (dyadicDensity_maximizer_posDef H B hm hθ hT htmax) hsmax htmax

theorem existsUnique_dyadicDensityOptimizer [Nonempty n] (H : Matrix n n ℂ)
    (B : ι → Matrix n n ℂ) (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (hθ : 0 < θ) :
    ∃! S : Matrix n n ℂ, S ∈ densitySet ∧
      ∀ T ∈ densitySet, dyadicDensityObjective H B m θ T ≤ dyadicDensityObjective H B m θ S := by
  obtain ⟨S, hS, hmax⟩ := exists_dyadicDensityOptimizer H B m θ
  refine ⟨S, ⟨hS, hmax⟩, ?_⟩
  intro T hT
  exact dyadicDensity_maximizers_eq H B m hm θ hθ hT.1 hS hT.2 hmax

end
end MatrixSpencer
