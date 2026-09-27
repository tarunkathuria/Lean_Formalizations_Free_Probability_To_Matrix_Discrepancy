import MatrixSpencer.CovarianceSource
import MatrixSpencer.DensityFaithfulness

/-!
# The potential in the original owner covariance coordinates

This is the actual supremum over physical trace-one densities, with the
bilinear covariance source. Its relation to the Kraus formulation is proved.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix

noncomputable section

namespace MatrixSpencer

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n]

def ownerObjective (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ)
    (C : Matrix ι ι ℝ) (θ : ℝ) (S : Matrix n n ℂ) : ℝ :=
  realTrace (H * S) + 2 * fidelity S (covarianceSource A C S) +
    2 * θ * realTrace (CFC.sqrt S)

def ownerPotential (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ)
    (C : Matrix ι ι ℝ) (θ : ℝ) : ℝ :=
  sSup (ownerObjective H A C θ '' densitySet)

theorem ownerObjective_eq_densityObjective (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) {C : Matrix ι ι ℝ} (hC : C.PosSemidef)
    (θ : ℝ) (S : Matrix n n ℂ) :
    ownerObjective H A C θ S = densityObjective H (covarianceKraus A C) θ S := by
  unfold ownerObjective densityObjective
  rw [covarianceSource_eq_kraus A hA hC]

theorem ownerPotential_eq_densityPotential (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (θ : ℝ) :
    ownerPotential H A C θ = densityPotential H (covarianceKraus A C) θ := by
  unfold ownerPotential densityPotential
  congr 2
  funext S
  exact ownerObjective_eq_densityObjective H A hA hC θ S

/-- The original-coordinate objective is jointly continuous on covariance/density PSD domains. -/
theorem continuous_ownerObjective_psd (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (θ : ℝ) :
    Continuous (fun p : (Matrix n n ℂ × {C : Matrix ι ι ℝ // C.PosSemidef}) ×
        (densitySet : Set (Matrix n n ℂ)) =>
      ownerObjective p.1.1 A p.1.2 θ p.2) := by
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
  have hroot := continuous_matrix_sqrt_of_psd hS (fun p => p.2.property.1)
  exact ((continuous_realTrace.comp (hH.mul hS)).add (continuous_const.mul hf)).add
    (continuous_const.mul (continuous_realTrace.comp hroot))

/-- Maximizing over the compact density domain preserves joint continuity. -/
theorem continuous_ownerPotential_psd (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (θ : ℝ) :
    Continuous (fun p : Matrix n n ℂ × {C : Matrix ι ι ℝ // C.PosSemidef} =>
      ownerPotential p.1 A p.2 θ) := by
  letI : CompactSpace (densitySet : Set (Matrix n n ℂ)) :=
    isCompact_iff_compactSpace.mp isCompact_densitySet
  have hc : Continuous (fun p : Matrix n n ℂ × {C : Matrix ι ι ℝ // C.PosSemidef} =>
      sSup ((fun S : (densitySet : Set (Matrix n n ℂ)) => ownerObjective p.1 A p.2 θ S) '' Set.univ)) :=
    (isCompact_univ : IsCompact (Set.univ : Set (densitySet : Set (Matrix n n ℂ)))).continuous_sSup
      (continuous_ownerObjective_psd A hA θ)
  convert hc using 1
  funext p
  unfold ownerPotential
  congr 1
  ext r
  simp only [Set.mem_image, Set.mem_univ, true_and]
  constructor
  · rintro ⟨S, hS, hr⟩
    exact ⟨⟨S, hS⟩, hr⟩
  · rintro ⟨S, hr⟩
    exact ⟨S, S.property, hr⟩

/-- The supremum in original coordinates is attained at the proved faithful optimizer. -/
theorem exists_ownerOptimizer [Nonempty n] (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) {C : Matrix ι ι ℝ} (hC : C.PosSemidef)
    {θ : ℝ} (hθ : 0 < θ) :
    ∃ S ∈ densitySet, S.PosDef ∧ ownerPotential H A C θ = ownerObjective H A C θ S ∧
      ∀ T ∈ densitySet, ownerObjective H A C θ T ≤ ownerObjective H A C θ S := by
  let S := densityOptimizer H (covarianceKraus A C) θ
  have hmem := densityOptimizer_mem H (covarianceKraus A C) θ
  have hmax := densityOptimizer_isMaxOn H (covarianceKraus A C) θ
  refine ⟨S, hmem, densityOptimizer_posDef H (covarianceKraus A C) hθ, ?_, ?_⟩
  · rw [ownerPotential_eq_densityPotential H A hA hC θ,
      ownerObjective_eq_densityObjective H A hA hC θ S]
    exact densityPotential_eq_of_maximizer H _ θ hmem hmax
  · intro T hT
    rw [ownerObjective_eq_densityObjective H A hA hC θ T,
      ownerObjective_eq_densityObjective H A hA hC θ S]
    exact hmax T hT

/-- Source monotonicity yields monotonicity of the actual optimized potential. -/
theorem ownerPotential_mono_covariance [Nonempty n]
    (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C D : Matrix ι ι ℝ} (hC : C.PosSemidef) (hD : D.PosSemidef)
    (hCD : C ≤ D) (θ : ℝ) : ownerPotential H A C θ ≤ ownerPotential H A D θ := by
  obtain ⟨S, hS, hmax⟩ := exists_densityOptimizer H (covarianceKraus A C) θ
  rw [ownerPotential_eq_densityPotential H A hA hC θ,
    densityPotential_eq_of_maximizer H _ θ hS hmax,
    ← ownerObjective_eq_densityObjective H A hA hC θ S,
    ownerPotential_eq_densityPotential H A hA hD θ]
  apply le_trans _ (densityObjective_le_potential H (covarianceKraus A D) θ hS)
  rw [← ownerObjective_eq_densityObjective H A hA hD θ S]
  have hf := fidelity_mono hS.1 hS.1 (covarianceSource_posSemidef A hA hC hS.1)
    (covarianceSource_posSemidef A hA hD hS.1) le_rfl (covarianceSource_mono A hA hCD hS.1)
  unfold ownerObjective
  linarith

end MatrixSpencer
