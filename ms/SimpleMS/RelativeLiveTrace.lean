import SimpleMS.LegalSpace
import MatrixSpencer.RectangularRidgeLiveShort

/-! The half-projection trace bound counts only the coordinates still live
at the start of the epoch. Previously frozen coordinates cost no dimension. -/
open Matrix
open scoped BigOperators MatrixOrder
noncomputable section
namespace SimpleMS.RelativeLiveTrace
open MatrixSpencer
variable {N : ℕ}

theorem highProjection_trace_rank_lower {C : Matrix (Fin N) (Fin N) ℝ}
    (hC : C.IsHermitian) (hC1 : C ≤ 1) :
    2 * realTrace C - (C.rank : ℝ) ≤ realTrace (highProjection C) := by
  classical
  have hRank : (C.rank : ℝ) = ∑ j, if hC.eigenvalues j ≠ 0 then (1 : ℝ) else 0 := by
    rw [hC.rank_eq_card_non_zero_eigs, Fintype.card_subtype, Finset.sum_boole]
  have hTrace : realTrace C = ∑ j, hC.eigenvalues j := hC.trace_eq_sum_eigenvalues
  rw [highProjection_eq C hC, RealSpectralCutoff.high,
    RealSpectralCutoff.spectralMatrix_trace, hTrace, hRank,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro j _
  have hj := eigenvalue_le_one hC hC1 j
  by_cases hz : hC.eigenvalues j = 0
  · norm_num [hz]
  · rw [if_pos hz]
    split_ifs with hh
    · linarith
    · have hh' := lt_of_not_ge hh
      linarith

theorem half_high_le {C : Matrix (Fin N) (Fin N) ℝ} (hC : C.PosSemidef) :
    (1/2 : ℝ) • highProjection C ≤ C := by
  have h := RealSpectralCutoff.high_le_inv_smul hC (show (0 : ℝ) < 1/2 by norm_num)
  rw [← highProjection_eq C hC.isHermitian] at h
  have hs := smul_le_smul_of_nonneg_left h (show (0 : ℝ) ≤ 1/2 by norm_num)
  norm_num [smul_smul] at hs
  exact hs

theorem high_annihilates {C : Matrix (Fin N) (Fin N) ℝ} (hC : C.PosSemidef)
    (F₀ : Finset (Fin N)) (hF₀ : ∀ i ∈ F₀, C *ᵥ Pi.single i 1 = 0) :
    ∀ i ∈ F₀, highProjection C *ᵥ Pi.single i 1 = 0 := by
  have hp : (highProjection C).PosSemidef :=
    (highProjection_isStarProjection C hC.isHermitian).nonneg.posSemidef
  have hh := RectangularRidgeLiveShort.annihilators_mono C
    ((1/2 : ℝ) • highProjection C) (hp.smul (by norm_num)) (half_high_le hC) F₀ hF₀
  intro i hi
  have he : (1/2 : ℝ) • (highProjection C *ᵥ Pi.single i 1) = 0 := by
    simpa only [Matrix.smul_mulVec] using hh i hi
  exact (smul_eq_zero.mp he).resolve_left (by norm_num)

theorem highSpace_zero {C : Matrix (Fin N) (Fin N) ℝ} (hC : C.PosSemidef)
    (F₀ : Finset (Fin N)) (hF₀ : ∀ i ∈ F₀, C *ᵥ Pi.single i 1 = 0)
    (u : EuclideanSpace ℝ (Fin N)) (hu : u ∈ highSpace C) : ∀ i ∈ F₀, u i = 0 := by
  intro i hi
  have hcol : ∀ j, highProjection C j i = 0 := by
    intro j
    have h := congr_fun (high_annihilates hC F₀ hF₀ i hi) j
    simpa using h
  have hrow : ∀ j, highProjection C i j = 0 := by
    intro j
    have hh := (highProjection_isStarProjection C hC.isHermitian).isSelfAdjoint.star_eq
    have hs : highProjection C i j = highProjection C j i := by
      simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, star_trivial] using
        congrArg (fun M : Matrix (Fin N) (Fin N) ℝ => M j i) hh
    rw [hs,hcol]
  obtain ⟨v,hv⟩ := hu
  rw [← hv]
  change (highProjection C *ᵥ WithLp.ofLp v) i = 0
  simp [Matrix.mulVec, dotProduct, hrow]

theorem movementSpace_sdiff {C : Matrix (Fin N) (Fin N) ℝ} (hC : C.PosSemidef)
    (F₀ F : Finset (Fin N)) (x : EuclideanSpace ℝ (Fin N))
    (hF₀ : ∀ i ∈ F₀, C *ᵥ Pi.single i 1 = 0) :
    movementSpace C (legalSpace F x) = movementSpace C (legalSpace (F \ F₀) x) := by
  apply le_antisymm
  · intro u hu
    have hl := (mem_legalSpace F x u).mp hu.2
    exact ⟨hu.1,(mem_legalSpace (F \ F₀) x u).mpr
      ⟨fun i hi => hl.1 i (Finset.mem_sdiff.mp hi).1,hl.2⟩⟩
  · intro u hu
    have hl := (mem_legalSpace (F \ F₀) x u).mp hu.2
    refine ⟨hu.1,(mem_legalSpace F x u).mpr ⟨?_,hl.2⟩⟩
    intro i hi
    by_cases hi₀ : i ∈ F₀
    · exact highSpace_zero hC F₀ hF₀ u hu.1 i hi₀
    · exact hl.1 i (Finset.mem_sdiff.mpr ⟨hi,hi₀⟩)

theorem flatCovariance_sdiff {C : Matrix (Fin N) (Fin N) ℝ} (hC : C.PosSemidef)
    (F₀ F : Finset (Fin N)) (x : EuclideanSpace ℝ (Fin N))
    (hF₀ : ∀ i ∈ F₀, C *ᵥ Pi.single i 1 = 0) :
    flatCovariance C (legalSpace F x) = flatCovariance C (legalSpace (F \ F₀) x) := by
  unfold flatCovariance
  rw [movementSpace_sdiff hC F₀ F x hF₀]

theorem flat_trace_rank_lower {C : Matrix (Fin N) (Fin N) ℝ}
    (hC : C.IsHermitian) (hC1 : C ≤ 1) (V : Submodule ℝ (CoefficientSpace (Fin N))) :
    (2 * realTrace C - (C.rank : ℝ) - (Module.finrank ℝ Vᗮ : ℝ)) / 2 ≤
      realTrace (flatCovariance C V) := by
  have hh := highProjection_trace_rank_lower hC hC1
  rw [matrix_trace_eq_finrank_range (highProjection_isStarProjection C hC).isIdempotentElem.eq] at hh
  change 2 * realTrace C - (C.rank : ℝ) ≤ (Module.finrank ℝ (highSpace C) : ℝ) at hh
  have hi := (highSpace C).finrank_sup_add_finrank_inf_eq V
  have hu := (highSpace C ⊔ V).finrank_le
  have hv := V.finrank_add_finrank_orthogonal
  have hd : Module.finrank ℝ (highSpace C) ≤
      Module.finrank ℝ (movementSpace C V) + Module.finrank ℝ Vᗮ := by
    dsimp only [movementSpace]
    omega
  have hdr : (Module.finrank ℝ (highSpace C) : ℝ) ≤
      (Module.finrank ℝ (movementSpace C V) : ℝ) + (Module.finrank ℝ Vᗮ : ℝ) := by
    exact_mod_cast hd
  rw [flatCovariance_trace]
  linarith

/-- Only newly frozen constraints and the radial constraint reduce the
dimension of the high spectral subspace. -/
theorem flat_trace_lower {C : Matrix (Fin N) (Fin N) ℝ}
    (hC : C.PosSemidef) (hC1 : C ≤ 1) (F₀ F : Finset (Fin N))
    (x : EuclideanSpace ℝ (Fin N))
    (hF₀ : ∀ i ∈ F₀, C *ᵥ Pi.single i 1 = 0) :
    (2 * realTrace C - (C.rank : ℝ) - ((F \ F₀).card : ℝ) - 1) / 2 ≤
      realTrace (flatCovariance C (legalSpace F x)) := by
  rw [flatCovariance_sdiff hC F₀ F x hF₀]
  have ht := flat_trace_rank_lower hC.isHermitian hC1 (legalSpace (F \ F₀) x)
  have hc : (Module.finrank ℝ (legalSpace (F \ F₀) x)ᗮ : ℝ) ≤
      ((F \ F₀).card : ℝ) + 1 := by exact_mod_cast legalSpace_codim (F \ F₀) x
  linarith

theorem flat_trace_lower_of_rank_le {C : Matrix (Fin N) (Fin N) ℝ}
    (hC : C.PosSemidef) (hC1 : C ≤ 1) (F₀ F : Finset (Fin N))
    (x : EuclideanSpace ℝ (Fin N)) (ℓ : ℝ)
    (hF₀ : ∀ i ∈ F₀, C *ᵥ Pi.single i 1 = 0) (hrank : (C.rank : ℝ) ≤ ℓ) :
    (2 * realTrace C - ℓ - ((F \ F₀).card : ℝ) - 1) / 2 ≤
      realTrace (flatCovariance C (legalSpace F x)) := by
  have h := flat_trace_lower hC hC1 F₀ F x hF₀
  linarith

theorem trace_positive_of_ledger {C : Matrix (Fin N) (Fin N) ℝ}
    (hC : C.PosSemidef) (hC1 : C ≤ 1) (F₀ F : Finset (Fin N))
    (x : EuclideanSpace ℝ (Fin N)) (ℓ paid variance τ : ℝ) (hℓ : 32 ≤ ℓ)
    (hF₀ : ∀ i ∈ F₀, C *ᵥ Pi.single i 1 = 0) (hrank : (C.rank : ℝ) ≤ ℓ)
    (htrace : ℓ - paid - variance ≤ realTrace C) (hpaid : paid ≤ ℓ / 64)
    (hvariance : variance ≤ ℓ * τ) (hτ : τ ≤ 1 / 3)
    (hnew : ((F \ F₀).card : ℝ) ≤ ℓ / 64) :
    ℓ / 16 ≤ realTrace (flatCovariance C (legalSpace F x)) ∧
      0 < realTrace (flatCovariance C (legalSpace F x)) := by
  have h := flat_trace_lower_of_rank_le hC hC1 F₀ F x ℓ hF₀ hrank
  have hv : variance ≤ ℓ / 3 := by nlinarith
  constructor <;> linarith

end SimpleMS.RelativeLiveTrace
