import MatrixSpencer.KSSpinDrift

/-!
# The legal-kernel curvature estimate with a general source cap

The smooth source gives `rᵢ² ≤ (200/81)/64`, instead of the smaller
`1/64` bound used by the original full-cube proof. This module proves the
required extension from the concrete kernel projection and PSD spin atoms.
It does not assume a favorable covariance or negative legal direction.

The scalar derivative schedule is deliberately absent: the resulting
geometric theorem accepts arbitrary slopes `z` with `|zᵢ| ≤ 1`, and its
physical instantiation must subsequently prove those bounds from the new
source and the failed local candidate tests.
-/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder

noncomputable section

namespace SeamlessKS.Projection

open MatrixSpencer MatrixSpencer.KSSpinDrift MatrixSpencer.KSWeightedProjection

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The direct negative term loses at most `5 L/u` of its trace budget. -/
theorem kernel_direct_bound (E F : Matrix ι ι ℝ) (d : ι → ℝ)
    {h u L : ℝ} (hu : 0 < u) (hL : 0 ≤ L)
    (hd : ∀ i, d i ≤ L / u) (hsum : ∑ i, d i = h)
    (hE : hsSq E ≤ h) (hF : hsSq F ≤ 4 * h) :
    (1 - 5 * L / u) * h ≤
      realTrace (Matrix.diagonal d * (kernelProjection E F).toBlocks₂₂) := by
  let P := kernelProjection E F
  have hcap : Matrix.diagonal d ≤ (L / u) • (1 : Matrix ι ι ℝ) := by
    apply Matrix.le_iff.mpr
    rw [← Matrix.diagonal_one, ← Matrix.diagonal_smul, Matrix.diagonal_sub]
    exact Matrix.posSemidef_diagonal_iff.mpr (fun i => by
      simpa using sub_nonneg.mpr (hd i))
  have ht := realTrace_mul_mono (bottom_defect_posSemidef E F) hcap
  rw [realTrace_mul_comm (1 - P.toBlocks₂₂), Matrix.mul_smul, Matrix.mul_one,
    realTrace_smul, Matrix.mul_sub, Matrix.mul_one, realTrace_sub] at ht
  have htrace : realTrace (Matrix.diagonal d) = h := by
    simpa [realTrace] using hsum
  rw [htrace] at ht
  have htracebound : realTrace (1 - P.toBlocks₂₂) ≤ 5 * h :=
    (kernel_projection_block_estimates E F).2.1.trans (by linarith)
  have ht' := mul_le_mul_of_nonneg_left htracebound (div_nonneg hL hu.le)
  have heq : (1 - 5 * L / u) * h = h - (L / u) * (5 * h) := by ring
  rw [heq]
  linarith

/-- All three terms of the legal response, with the general diagonal cap. -/
theorem averaged_upper_bound (E F : Matrix ι ι ℝ) (d z : ι → ℝ)
    (H : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) {h u L : ℝ}
    (hh : 0 ≤ h) (hu : 0 < u) (hL : 0 ≤ L)
    (hd : ∀ i, d i ≤ L / u) (hsum : ∑ i, d i = h)
    (hz : ∀ i, |z i| ≤ 1) (hE : hsSq E ≤ h) (hF : hsSq F ≤ 4 * h)
    (hbase : |realTrace (Matrix.diagonal z * F)| ≤ 2 * h)
    (hH : H.PosSemidef) (htrace : realTrace H ≤ 5 * h) :
    averagedUpper E F d z H u ≤
      -(1 - (5 * L + 7 + 3 * Real.sqrt 5) / u) * h := by
  have hdirect := kernel_direct_bound E F d hu hL hd hsum hE hF
  have hresp := div_le_div_of_nonneg_right (kernel_response_bound E F hH htrace) hu.le
  have hmix := kernel_mixed_bound E F z hz hh hE hF hbase
  have hmdiv := div_le_div_of_nonneg_right (neg_le_of_abs_le hmix) hu.le
  unfold averagedUpper
  have he : -(1 - (5 * L + 7 + 3 * Real.sqrt 5) / u) * h =
      -((1 - 5 * L / u) * h) + 5 * h / u +
        (2 + 3 * Real.sqrt 5) * h / u := by ring
  rw [he]
  simp only [neg_div] at hmdiv
  linarith

/-- The smooth-source constants leave strict slack in the curvature bound. -/
theorem smooth_curvature_coefficient_pos :
    0 < 1 - (5 * (200 / 81 : ℝ) + 7 + 3 * Real.sqrt 5) / 64 := by
  have hs : Real.sqrt 5 < 3 :=
    (Real.sqrt_lt (by norm_num) (by norm_num)).mpr (by norm_num)
  linarith

/-- Strict negative average at the actual smooth-source cap. -/
theorem averaged_upper_negative (E F : Matrix ι ι ℝ) (d z : ι → ℝ)
    (H : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) {h : ℝ}
    (hh : 0 < h) (hd : ∀ i, d i ≤ (200 / 81 : ℝ) / 64)
    (hsum : ∑ i, d i = h) (hz : ∀ i, |z i| ≤ 1)
    (hE : hsSq E ≤ h) (hF : hsSq F ≤ 4 * h)
    (hbase : |realTrace (Matrix.diagonal z * F)| ≤ 2 * h)
    (hH : H.PosSemidef) (htrace : realTrace H ≤ 5 * h) :
    averagedUpper E F d z H 64 < 0 := by
  have hbound := averaged_upper_bound E F d z H hh.le
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 200 / 81)
    hd hsum hz hE hF hbase hH htrace
  exact hbound.trans_lt (mul_neg_of_neg_of_pos
    (neg_neg_of_pos smooth_curvature_coefficient_pos) hh)

section Physical

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The general-cap bound instantiated from actual positive spin atoms.
Every weighted Gram and covariance trace estimate is discharged internally. -/
theorem physical_averaged_upper_bound
    (D : ι → Matrix n n ℂ) (hD : ∀ i, (D i).PosSemidef)
    {P J : Matrix n n ℂ} (hP : P.PosSemidef) (hJ : J.IsHermitian)
    (hJJ : J * J = 1) (hc : ∀ i, J * D i = D i * J)
    (hr : ∀ i, 0 < realTrace (D i)) (hm : ∀ i, 0 < realTrace (P * D i))
    (hfix : P = ∑ i, realTrace (P * D i) • D i) (z : ι → ℝ)
    (hz : ∀ i, |z i| ≤ 1) {u L : ℝ} (hu : 0 < u) (hL : 0 ≤ L)
    (hsmall : ∀ i, realTrace (D i) ^ 2 ≤ L / u) :
    averagedUpper (spinE P D) (spinF P J D z) (fun i => realTrace (D i) ^ 2) z
      (spinResponseGram P J D z) u ≤
      -(1 - (5 * L + 7 + 3 * Real.sqrt 5) / u) * ∑ i, realTrace (D i) ^ 2 := by
  let R := fisherWeight P D
  let T := KSFisher.gram D
  let TJ := KSFisher.spinGram J D
  let Γ := physicalRealGram P D
  let d : ι → ℝ := fun i => realTrace (D i) ^ 2
  have hR := fisherWeight_pos D hr hm
  have hdiag : ∀ i, Γ i i / R i ≤ d i := fun i =>
    physical_weighted_diagonal hP D hD hr hm i
  have ht : Tᵀ = T := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (KSFisher.gram_isHermitian D).eq
  have htj : TJᵀ = TJ := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (KSFisher.spinGram_isHermitian hJ D (fun i => (hD i).isHermitian)).eq
  have hfisher : Tᵀ * Matrix.diagonal R * T ≤ Γ := by
    rw [ht]
    exact KSFisher.gram_fisher D hD (fun i => realTrace (P * D i))
      (fun i => (hm i).le) hr hfix
  have hspin : TJᵀ * Matrix.diagonal R * TJ ≤ Γ := by
    rw [htj]
    exact KSFisher.spin_gram_fisher D hD (fun i => realTrace (P * D i))
      (fun i => (hm i).le) hr hfix hJ hJJ hc
  have henergy := weighted_pair_energy_bounds R d z hR hz T TJ Γ hfisher hspin hdiag
  have hbase := weighted_pair_mixed_baseline R d z hR hz T TJ
    (fun i => realTrace_mul_nonneg (hD i) (hD i))
    (fun i => gram_diagonal_le_trace_sq (hD i))
    (fun i => spin_gram_diagonal_abs_le hJ hJJ (hD i).isHermitian)
  have hresponse : (spinResponseGram P J D z).PosSemidef :=
    KSFisher.physicalGram_posSemidef hP _
      (jointFeatures_isHermitian D (fun i => (hD i).isHermitian) hJ hc R z)
  have htrace : realTrace (spinResponseGram P J D z) ≤ 5 * ∑ i, d i :=
    joint_response_trace_le D (fun i => (hD i).isHermitian) hP hJ hJJ hc R z d hR hz
      (fun i => physical_weighted_diagonal hP D hD hr hm i)
  have hh : 0 ≤ ∑ i, d i := Finset.sum_nonneg (fun i _ => sq_nonneg (realTrace (D i)))
  exact averaged_upper_bound (spinE P D) (spinF P J D z) d z
    (spinResponseGram P J D z) hh hu hL hsmall rfl hz henergy.1 henergy.2
    hbase hresponse htrace

/-- Nonzero source atoms give a strictly negative covariance average. -/
theorem physical_averaged_upper_negative [Nonempty ι]
    (D : ι → Matrix n n ℂ) (hD : ∀ i, (D i).PosSemidef)
    {P J : Matrix n n ℂ} (hP : P.PosSemidef) (hJ : J.IsHermitian)
    (hJJ : J * J = 1) (hc : ∀ i, J * D i = D i * J)
    (hr : ∀ i, 0 < realTrace (D i)) (hm : ∀ i, 0 < realTrace (P * D i))
    (hfix : P = ∑ i, realTrace (P * D i) • D i) (z : ι → ℝ)
    (hz : ∀ i, |z i| ≤ 1)
    (hsmall : ∀ i, realTrace (D i) ^ 2 ≤ (200 / 81 : ℝ) / 64) :
    averagedUpper (spinE P D) (spinF P J D z) (fun i => realTrace (D i) ^ 2) z
      (spinResponseGram P J D z) 64 < 0 := by
  have hbound := physical_averaged_upper_bound D hD hP hJ hJJ hc hr hm hfix z hz
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 200 / 81) hsmall
  have hh : 0 < ∑ i, realTrace (D i) ^ 2 :=
    Finset.sum_pos (fun i _ => sq_pos_of_pos (hr i)) Finset.univ_nonempty
  exact hbound.trans_lt (mul_neg_of_neg_of_pos
    (neg_neg_of_pos smooth_curvature_coefficient_pos) hh)

/-- A concrete nonzero legal direction, obtained from the proved projection.
There is no supplied covariance, spectral gap, or curvature premise. -/
theorem exists_physical_negative_legal_direction [Nonempty ι]
    (D : ι → Matrix n n ℂ) (hD : ∀ i, (D i).PosSemidef)
    {P J : Matrix n n ℂ} (hP : P.PosSemidef) (hJ : J.IsHermitian)
    (hJJ : J * J = 1) (hc : ∀ i, J * D i = D i * J)
    (hr : ∀ i, 0 < realTrace (D i)) (hm : ∀ i, 0 < realTrace (P * D i))
    (hfix : P = ∑ i, realTrace (P * D i) • D i) (z : ι → ℝ)
    (hz : ∀ i, |z i| ≤ 1)
    (hsmall : ∀ i, realTrace (D i) ^ 2 ≤ (200 / 81 : ℝ) / 64) :
    ∃ ω y : ι → ℝ, y ≠ 0 ∧
      (1 - KSFisher.gram D) *ᵥ ω =
        (KSFisher.spinGram J D - KSFisher.gram D * Matrix.diagonal z) *ᵥ y ∧
      legalUpper P J D (fisherWeight P D) (fun i => realTrace (D i) ^ 2) z 64 ω y < 0 := by
  have hneg := physical_averaged_upper_negative D hD hP hJ hJJ hc hr hm hfix z hz hsmall
  obtain ⟨x, hx, hqx⟩ := exists_negative_kernel_direction (spinE P D) (spinF P J D z)
    (fun i => realTrace (D i) ^ 2) z (spinResponseGram P J D z) 64 hneg
  have hR := fisherWeight_pos D hr hm
  have hresponse : (spinResponseGram P J D z).PosSemidef :=
    KSFisher.physicalGram_posSemidef hP _
      (jointFeatures_isHermitian D (fun i => (hD i).isHermitian) hJ hc (fisherWeight P D) z)
  refine ⟨unwhiten (fisherWeight P D) (x ∘ Sum.inl),
    unwhiten (fisherWeight P D) (x ∘ Sum.inr), ?_, ?_, ?_⟩
  · exact unwhiten_ne_zero _ hR
      (negative_kernel_bottom_ne_zero _ _ hresponse (by norm_num) hqx)
  · exact unwhiten_legal _ hR (KSFisher.gram D) (KSFisher.spinGram J D) z hx
  · unfold spinResponseGram at hqx
    rwa [upperMatrix_eq_legalUpper P J D (fisherWeight P D) _ z hR 64 x] at hqx

end Physical

end SeamlessKS.Projection
