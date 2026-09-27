import MatrixSpencer.OwnerBounds
import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Actual owner potentials with an additive density regularizer

The supremum is over the existing physical PSD trace-one density set. The
regularizer is an actual function, with its continuity hypothesis explicit.
No optimizer faithfulness, response estimate, or walk existence is assumed.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix
noncomputable section

namespace MatrixSpencer

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n]

local instance regularizedOwnerCStarAlgebra : CStarAlgebra (Matrix n n ℂ) := {}

def regularizedOwnerObjective (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ)
    (C : Matrix ι ι ℝ) (R : Matrix n n ℂ → ℝ) (S : Matrix n n ℂ) : ℝ :=
  realTrace (H * S) + 2 * fidelity S (covarianceSource A C S) + R S

def regularizedOwnerPotential (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ)
    (C : Matrix ι ι ℝ) (R : Matrix n n ℂ → ℝ) : ℝ :=
  sSup (regularizedOwnerObjective H A C R '' densitySet)

def regularizedBaseObjective (H : Matrix n n ℂ) (R : Matrix n n ℂ → ℝ)
    (S : Matrix n n ℂ) : ℝ := realTrace (H * S) + R S

def regularizedBasePotential (H : Matrix n n ℂ) (R : Matrix n n ℂ → ℝ) : ℝ :=
  sSup (regularizedBaseObjective H R '' densitySet)

/-- Joint continuity includes arbitrary singular owner covariances. -/
theorem continuous_regularizedOwnerObjective_psd (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (R : Matrix n n ℂ → ℝ)
    (hR : ContinuousOn R densitySet) :
    Continuous (fun p : (Matrix n n ℂ × {C : Matrix ι ι ℝ // C.PosSemidef}) ×
        (densitySet : Set (Matrix n n ℂ)) =>
      regularizedOwnerObjective p.1.1 A p.1.2 R p.2) := by
  have hH : Continuous (fun p : (Matrix n n ℂ × {C : Matrix ι ι ℝ // C.PosSemidef}) ×
      (densitySet : Set (Matrix n n ℂ)) => p.1.1) := continuous_fst.fst
  have hC : Continuous (fun p : (Matrix n n ℂ × {C : Matrix ι ι ℝ // C.PosSemidef}) ×
      (densitySet : Set (Matrix n n ℂ)) => (p.1.2 : Matrix ι ι ℝ)) :=
    continuous_subtype_val.comp continuous_fst.snd
  have hS : Continuous (fun p : (Matrix n n ℂ × {C : Matrix ι ι ℝ // C.PosSemidef}) ×
      (densitySet : Set (Matrix n n ℂ)) => (p.2 : Matrix n n ℂ)) :=
    continuous_subtype_val.comp continuous_snd
  have hsource := (continuous_covarianceSource A).comp (hC.prodMk hS)
  have hf := continuous_fidelity_of_psd hS hsource (fun p => p.2.property.1)
    (fun p => covarianceSource_posSemidef A hA p.1.2.property p.2.property.1)
  have hr : Continuous (fun p : (Matrix n n ℂ × {C : Matrix ι ι ℝ // C.PosSemidef}) ×
      (densitySet : Set (Matrix n n ℂ)) => R p.2) :=
    (continuousOn_iff_continuous_restrict.mp hR).comp continuous_snd
  exact ((continuous_realTrace.comp (hH.mul hS)).add (continuous_const.mul hf)).add hr

theorem continuousOn_regularizedOwnerObjective (H : Matrix n n ℂ)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (R : Matrix n n ℂ → ℝ)
    (hR : ContinuousOn R densitySet) :
    ContinuousOn (regularizedOwnerObjective H A C R) densitySet := by
  apply continuousOn_iff_continuous_restrict.mpr
  have hs : Continuous (fun S : (densitySet : Set (Matrix n n ℂ)) =>
      (S : Matrix n n ℂ)) := continuous_subtype_val
  have hm : Continuous (fun S : (densitySet : Set (Matrix n n ℂ)) => covarianceSource A C S) :=
    (continuous_covarianceSource A).comp (continuous_const.prodMk hs)
  have hf := continuous_fidelity_of_psd hs hm (fun S => S.property.1)
    (fun S => covarianceSource_posSemidef A hA hC S.property.1)
  exact ((continuous_realTrace.comp (continuous_const.mul hs)).add
    (continuous_const.mul hf)).add (continuousOn_iff_continuous_restrict.mp hR)

/-- A continuous regularizer gives an actual maximizing density. -/
theorem exists_regularizedOwnerMaximizer [Nonempty n] (H : Matrix n n ℂ)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (R : Matrix n n ℂ → ℝ)
    (hR : ContinuousOn R densitySet) :
    ∃ S ∈ densitySet, ∀ T ∈ densitySet,
      regularizedOwnerObjective H A C R T ≤ regularizedOwnerObjective H A C R S := by
  exact isCompact_densitySet.exists_isMaxOn densitySet_nonempty
    (continuousOn_regularizedOwnerObjective H A hA hC R hR)

omit [DecidableEq ι] in
theorem regularizedOwnerPotential_eq_of_maximizer (H : Matrix n n ℂ)
    (A : ι → Matrix n n ℂ) (C : Matrix ι ι ℝ) (R : Matrix n n ℂ → ℝ)
    {S : Matrix n n ℂ} (hS : S ∈ densitySet)
    (hmax : ∀ T ∈ densitySet,
      regularizedOwnerObjective H A C R T ≤ regularizedOwnerObjective H A C R S) :
    regularizedOwnerPotential H A C R = regularizedOwnerObjective H A C R S := by
  have hg : IsGreatest (regularizedOwnerObjective H A C R '' densitySet)
      (regularizedOwnerObjective H A C R S) := by
    refine ⟨⟨S, hS, rfl⟩, ?_⟩
    rintro z ⟨T, hT, rfl⟩
    exact hmax T hT
  exact hg.csSup_eq

theorem exists_regularizedOwnerPotential_eq [Nonempty n] (H : Matrix n n ℂ)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (R : Matrix n n ℂ → ℝ)
    (hR : ContinuousOn R densitySet) :
    ∃ S ∈ densitySet, regularizedOwnerPotential H A C R =
      regularizedOwnerObjective H A C R S := by
  obtain ⟨S, hS, hmax⟩ := exists_regularizedOwnerMaximizer H A hA hC R hR
  exact ⟨S, hS, regularizedOwnerPotential_eq_of_maximizer H A C R hS hmax⟩

theorem regularizedOwnerObjective_le_potential [Nonempty n] (H : Matrix n n ℂ)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (R : Matrix n n ℂ → ℝ)
    (hR : ContinuousOn R densitySet) {S : Matrix n n ℂ} (hS : S ∈ densitySet) :
    regularizedOwnerObjective H A C R S ≤ regularizedOwnerPotential H A C R := by
  obtain ⟨T, hT, hmax⟩ := exists_regularizedOwnerMaximizer H A hA hC R hR
  rw [regularizedOwnerPotential_eq_of_maximizer H A C R hT hmax]
  exact hmax S hS

/-- The maximum theorem supplies continuity of the actual supremum. -/
theorem continuous_regularizedOwnerPotential_psd (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (R : Matrix n n ℂ → ℝ)
    (hR : ContinuousOn R densitySet) :
    Continuous (fun p : Matrix n n ℂ × {C : Matrix ι ι ℝ // C.PosSemidef} =>
      regularizedOwnerPotential p.1 A p.2 R) := by
  letI : CompactSpace (densitySet : Set (Matrix n n ℂ)) :=
    isCompact_iff_compactSpace.mp isCompact_densitySet
  have hc : Continuous (fun p : Matrix n n ℂ × {C : Matrix ι ι ℝ // C.PosSemidef} =>
      sSup ((fun S : (densitySet : Set (Matrix n n ℂ)) =>
        regularizedOwnerObjective p.1 A p.2 R S) '' Set.univ)) :=
    (isCompact_univ : IsCompact (Set.univ : Set (densitySet : Set (Matrix n n ℂ)))).continuous_sSup
      (continuous_regularizedOwnerObjective_psd A hA R hR)
  convert hc using 1
  funext p
  unfold regularizedOwnerPotential
  congr 1
  ext r
  simp only [Set.mem_image, Set.mem_univ, true_and]
  constructor
  · rintro ⟨S, hS, hr⟩
    exact ⟨⟨S, hS⟩, hr⟩
  · rintro ⟨S, hr⟩
    exact ⟨S, S.property, hr⟩

theorem regularizedOwnerPotential_mono_covariance [Nonempty n]
    (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C D : Matrix ι ι ℝ} (hC : C.PosSemidef) (hD : D.PosSemidef) (hCD : C ≤ D)
    (R : Matrix n n ℂ → ℝ) (hR : ContinuousOn R densitySet) :
    regularizedOwnerPotential H A C R ≤ regularizedOwnerPotential H A D R := by
  obtain ⟨S, hS, hmax⟩ := exists_regularizedOwnerMaximizer H A hA hC R hR
  rw [regularizedOwnerPotential_eq_of_maximizer H A C R hS hmax]
  apply le_trans _ (regularizedOwnerObjective_le_potential H A hA hD R hR hS)
  have hf := fidelity_mono hS.1 hS.1 (covarianceSource_posSemidef A hA hC hS.1)
    (covarianceSource_posSemidef A hA hD hS.1) le_rfl (covarianceSource_mono A hA hCD hS.1)
  unfold regularizedOwnerObjective
  linarith

omit [DecidableEq ι] in
theorem regularizedOwnerObjective_center_difference (H H' S : Matrix n n ℂ)
    (A : ι → Matrix n n ℂ) (C : Matrix ι ι ℝ) (R : Matrix n n ℂ → ℝ) :
    regularizedOwnerObjective H' A C R S = regularizedOwnerObjective H A C R S +
      realTrace ((H' - H) * S) := by
  simp only [regularizedOwnerObjective, Matrix.sub_mul, realTrace_sub]
  ring

theorem regularizedOwnerPotential_supporting_plane [Nonempty n]
    (H H' : Matrix n n ℂ) (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (R : Matrix n n ℂ → ℝ)
    (hR : ContinuousOn R densitySet) {S : Matrix n n ℂ} (hS : S ∈ densitySet)
    (hmax : ∀ T ∈ densitySet,
      regularizedOwnerObjective H A C R T ≤ regularizedOwnerObjective H A C R S) :
    regularizedOwnerPotential H A C R + realTrace ((H' - H) * S) ≤
      regularizedOwnerPotential H' A C R := by
  rw [regularizedOwnerPotential_eq_of_maximizer H A C R hS hmax,
    ← regularizedOwnerObjective_center_difference]
  exact regularizedOwnerObjective_le_potential H' A hA hC R hR hS

theorem convexOn_regularizedOwnerPotential [Nonempty n]
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (R : Matrix n n ℂ → ℝ)
    (hR : ContinuousOn R densitySet) :
    ConvexOn ℝ Set.univ (fun H : Matrix n n ℂ => regularizedOwnerPotential H A C R) := by
  refine ⟨convex_univ, ?_⟩
  intro H _ H' _ a b ha hb hab
  change regularizedOwnerPotential (a • H + b • H') A C R ≤
    a * regularizedOwnerPotential H A C R + b * regularizedOwnerPotential H' A C R
  obtain ⟨S, hS, hmax⟩ := exists_regularizedOwnerMaximizer (a • H + b • H') A hA hC R hR
  rw [regularizedOwnerPotential_eq_of_maximizer _ A C R hS hmax]
  have h1 := mul_le_mul_of_nonneg_left (regularizedOwnerObjective_le_potential H A hA hC R hR hS) ha
  have h2 := mul_le_mul_of_nonneg_left (regularizedOwnerObjective_le_potential H' A hA hC R hR hS) hb
  have he : regularizedOwnerObjective (a • H + b • H') A C R S =
      a * regularizedOwnerObjective H A C R S + b * regularizedOwnerObjective H' A C R S := by
    simp only [regularizedOwnerObjective, Matrix.add_mul, Matrix.smul_mul,
      realTrace_add, realTrace_smul]
    linear_combination -(2 * fidelity S (covarianceSource A C S) + R S) * hab
  rw [he]
  simpa only [smul_eq_mul] using add_le_add h1 h2

theorem regularizedOwnerPotential_sub_le_norm [Nonempty n]
    {H H' : Matrix n n ℂ} (hH : H.IsHermitian) (hH' : H'.IsHermitian)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (R : Matrix n n ℂ → ℝ)
    (hR : ContinuousOn R densitySet) :
    regularizedOwnerPotential H' A C R - regularizedOwnerPotential H A C R ≤ ‖H' - H‖ := by
  obtain ⟨S, hS, hmax⟩ := exists_regularizedOwnerMaximizer H' A hA hC R hR
  rw [regularizedOwnerPotential_eq_of_maximizer H' A C R hS hmax,
    regularizedOwnerObjective_center_difference H H' S]
  have hb := regularizedOwnerObjective_le_potential H A hA hC R hR hS
  have ht := realTrace_mul_density_le_norm (hH'.sub hH) hS
  linarith

theorem abs_regularizedOwnerPotential_sub_le_norm [Nonempty n]
    {H H' : Matrix n n ℂ} (hH : H.IsHermitian) (hH' : H'.IsHermitian)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (R : Matrix n n ℂ → ℝ)
    (hR : ContinuousOn R densitySet) :
    |regularizedOwnerPotential H' A C R - regularizedOwnerPotential H A C R| ≤ ‖H' - H‖ := by
  apply abs_le.mpr
  have hu := regularizedOwnerPotential_sub_le_norm hH hH' A hA hC R hR
  have hl := regularizedOwnerPotential_sub_le_norm hH' hH A hA hC R hR
  rw [norm_sub_rev H H'] at hl
  exact ⟨by linarith, hu⟩

theorem lipschitz_regularizedOwnerPotential [Nonempty n]
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (R : Matrix n n ℂ → ℝ)
    (hR : ContinuousOn R densitySet) :
    LipschitzWith 1 (fun H : selfAdjoint (Matrix n n ℂ) => regularizedOwnerPotential H A C R) := by
  apply LipschitzWith.of_dist_le_mul
  intro H H'
  have h := abs_regularizedOwnerPotential_sub_le_norm H'.property H.property A hA hC R hR
  simpa only [Real.dist_eq, dist_eq_norm, NNReal.coe_one, one_mul] using h

omit [DecidableEq ι] in
theorem regularizedOwnerObjective_zero (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ)
    (R : Matrix n n ℂ → ℝ) (S : Matrix n n ℂ) :
    regularizedOwnerObjective H A 0 R S = regularizedBaseObjective H R S := by
  simp [regularizedOwnerObjective, regularizedBaseObjective, covarianceSource,
    fidelity, fidelityCore, realTrace_zero]

omit [DecidableEq ι] in
theorem regularizedOwnerPotential_zero (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ)
    (R : Matrix n n ℂ → ℝ) :
    regularizedOwnerPotential H A 0 R = regularizedBasePotential H R := by
  unfold regularizedOwnerPotential regularizedBasePotential
  congr 2
  funext S
  exact regularizedOwnerObjective_zero H A R S

omit [Fintype ι] [DecidableEq ι] in
theorem regularizedOwnerPotential_empty (H : Matrix n n ℂ) (R : Matrix n n ℂ → ℝ)
    (A : Empty → Matrix n n ℂ) (C : Matrix Empty Empty ℝ) :
    regularizedOwnerPotential H A C R = regularizedBasePotential H R := by
  have hc : C = 0 := by ext i; exact i.elim
  rw [hc, regularizedOwnerPotential_zero]

omit [Fintype ι] [DecidableEq ι] in
theorem exists_regularizedBaseMaximizer [Nonempty n] (H : Matrix n n ℂ)
    (R : Matrix n n ℂ → ℝ) (hR : ContinuousOn R densitySet) :
    ∃ S ∈ densitySet, ∀ T ∈ densitySet,
      regularizedBaseObjective H R T ≤ regularizedBaseObjective H R S := by
  have hc : ContinuousOn (regularizedBaseObjective H R) densitySet := by
    exact ((continuous_realTrace.comp (continuous_const.mul continuous_id)).continuousOn).add hR
  exact isCompact_densitySet.exists_isMaxOn densitySet_nonempty hc

omit [Fintype ι] [DecidableEq ι] [DecidableEq n] in
theorem regularizedBasePotential_eq_of_maximizer (H : Matrix n n ℂ)
    (R : Matrix n n ℂ → ℝ) {S : Matrix n n ℂ} (hS : S ∈ densitySet)
    (hmax : ∀ T ∈ densitySet,
      regularizedBaseObjective H R T ≤ regularizedBaseObjective H R S) :
    regularizedBasePotential H R = regularizedBaseObjective H R S := by
  have hg : IsGreatest (regularizedBaseObjective H R '' densitySet)
      (regularizedBaseObjective H R S) := by
    refine ⟨⟨S, hS, rfl⟩, ?_⟩
    rintro z ⟨T, hT, rfl⟩
    exact hmax T hT
  exact hg.csSup_eq

omit [Fintype ι] [DecidableEq ι] in
theorem regularizedBaseObjective_le_potential [Nonempty n] (H : Matrix n n ℂ)
    (R : Matrix n n ℂ → ℝ) (hR : ContinuousOn R densitySet)
    {S : Matrix n n ℂ} (hS : S ∈ densitySet) :
    regularizedBaseObjective H R S ≤ regularizedBasePotential H R := by
  obtain ⟨T, hT, hmax⟩ := exists_regularizedBaseMaximizer H R hR
  rw [regularizedBasePotential_eq_of_maximizer H R hT hmax]
  exact hmax S hS

theorem regularizedBasePotential_le_owner [Nonempty n] (H : Matrix n n ℂ)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (R : Matrix n n ℂ → ℝ)
    (hR : ContinuousOn R densitySet) :
    regularizedBasePotential H R ≤ regularizedOwnerPotential H A C R := by
  rw [← regularizedOwnerPotential_zero H A R]
  exact regularizedOwnerPotential_mono_covariance H A hA Matrix.PosSemidef.zero hC hC.nonneg R hR

/-- The covariance excess does not depend on the density regularizer. -/
theorem regularizedOwnerPotential_le_base_add [Nonempty n] (H : Matrix n n ℂ)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) (hN : ∀ i, ‖A i‖ ≤ 1)
    {C : Matrix ι ι ℝ} (hC0 : C.PosSemidef) (hC1 : C ≤ 1)
    (R : Matrix n n ℂ → ℝ) (hR : ContinuousOn R densitySet) :
    regularizedOwnerPotential H A C R ≤
      regularizedBasePotential H R + 2 * Real.sqrt (Fintype.card ι : ℝ) := by
  obtain ⟨S, hS, hmax⟩ := exists_regularizedOwnerMaximizer H A hA hC0 R hR
  rw [regularizedOwnerPotential_eq_of_maximizer H A C R hS hmax]
  have hf := density_ownerFidelity_le_sqrt_card A hA hN hC0 hC1 hS
  have hb := regularizedBaseObjective_le_potential H R hR hS
  unfold regularizedOwnerObjective regularizedBaseObjective at *
  linarith

theorem regularizedOwnerPotential_le_norm_add [Nonempty n]
    {H : Matrix n n ℂ} (hH : H.IsHermitian)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) (hN : ∀ i, ‖A i‖ ≤ 1)
    {C : Matrix ι ι ℝ} (hC0 : C.PosSemidef) (hC1 : C ≤ 1)
    (R : Matrix n n ℂ → ℝ) (hR : ContinuousOn R densitySet)
    {M : ℝ} (hRM : ∀ S ∈ densitySet, R S ≤ M) :
    regularizedOwnerPotential H A C R ≤
      ‖H‖ + 2 * Real.sqrt (Fintype.card ι : ℝ) + M := by
  obtain ⟨S, hS, hmax⟩ := exists_regularizedOwnerMaximizer H A hA hC0 R hR
  rw [regularizedOwnerPotential_eq_of_maximizer H A C R hS hmax]
  have hf := density_ownerFidelity_le_sqrt_card A hA hN hC0 hC1 hS
  have hh := realTrace_mul_density_le_norm hH hS
  have hr := hRM S hS
  unfold regularizedOwnerObjective
  linarith

/-- Installing a new covariance only pays its fidelity excess. -/
theorem regularizedOwnerPotential_refresh_le [Nonempty n]
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ) (A' : κ → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (hA' : ∀ i, (A' i).IsHermitian)
    (hN' : ∀ i, ‖A' i‖ ≤ 1) {C : Matrix ι ι ℝ} {C' : Matrix κ κ ℝ}
    (hC : C.PosSemidef) (hC' : C'.PosSemidef) (hC'1 : C' ≤ 1)
    (R : Matrix n n ℂ → ℝ) (hR : ContinuousOn R densitySet) :
    regularizedOwnerPotential H A' C' R - regularizedOwnerPotential H A C R ≤
      2 * Real.sqrt (Fintype.card κ : ℝ) := by
  have hold := regularizedBasePotential_le_owner H A hA hC R hR
  have hnew := regularizedOwnerPotential_le_base_add H A' hA' hN' hC' hC'1 R hR
  linarith

end MatrixSpencer
