import MatrixSpencer.KSFisher
import MatrixSpencer.KSWeightedProjection
import MatrixSpencer.DensityDomain

/-!
# Averaging the legal spin response on its actual joint kernel

All averages are finite covariance trace contractions. The joint covariance is
the kernel projection already constructed in `KSWeightedProjection`.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder
open Matrix

noncomputable section
set_option maxHeartbeats 800000

namespace MatrixSpencer.KSSpinDrift

open KSWeightedProjection

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem hsSq_eq_sum (A : Matrix ι ι ℝ) :
    hsSq A = ∑ j, ∑ i, A i j ^ 2 := by
  simp only [hsSq, realTrace, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.transpose_apply, RCLike.re_to_real, pow_two]

theorem trace_transpose_product (A B : Matrix ι ι ℝ) :
    realTrace (Bᵀ * A) = realTrace (Aᵀ * B) := by
  unfold realTrace
  rw [← Matrix.trace_transpose (Bᵀ * A), Matrix.transpose_mul, Matrix.transpose_transpose]

/-- Hilbert--Schmidt Cauchy--Schwarz for arbitrary real coefficient matrices. -/
theorem trace_transpose_sq_le (A B : Matrix ι ι ℝ) :
    realTrace (Aᵀ * B) ^ 2 ≤ hsSq A * hsSq B := by
  have hp : ∀ t : ℝ, 0 ≤ hsSq B * (t * t) +
      (-2 * realTrace (Aᵀ * B)) * t + hsSq A := by
    intro t
    have h := hsSq_nonneg (A - t • B)
    simp only [hsSq, Matrix.transpose_sub, Matrix.transpose_smul, Matrix.sub_mul,
      Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
      realTrace_sub, realTrace_smul, trace_transpose_product A B] at h
    change 0 ≤ realTrace (Bᵀ * B) * (t * t) +
      (-2 * realTrace (Aᵀ * B)) * t + realTrace (Aᵀ * A)
    nlinarith
  have h := discrim_le_zero hp
  unfold discrim at h
  nlinarith

theorem abs_trace_mul_le_sqrt (A B : Matrix ι ι ℝ) :
    |realTrace (A * B)| ≤ Real.sqrt (hsSq A * hsSq B) := by
  apply (Real.le_sqrt (abs_nonneg _) (mul_nonneg (hsSq_nonneg A) (hsSq_nonneg B))).mpr
  simpa only [sq_abs, Matrix.transpose_transpose, hsSq_transpose] using
    trace_transpose_sq_le Aᵀ B

/-- A bounded real coefficient diagonal contracts squared HS energy. -/
theorem hsSq_diagonal_mul_le (z : ι → ℝ) (hz : ∀ i, |z i| ≤ 1)
    (A : Matrix ι ι ℝ) : hsSq (Matrix.diagonal z * A) ≤ hsSq A := by
  rw [hsSq_eq_sum, hsSq_eq_sum]
  apply Finset.sum_le_sum
  intro j _
  apply Finset.sum_le_sum
  intro i _
  rw [Matrix.diagonal_mul, mul_pow]
  have hzsq : z i ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one _).mpr (hz i)
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hzsq (sq_nonneg (A i j))

theorem hsSq_mul_diagonal_le (z : ι → ℝ) (hz : ∀ i, |z i| ≤ 1)
    (A : Matrix ι ι ℝ) : hsSq (A * Matrix.diagonal z) ≤ hsSq A := by
  rw [← hsSq_transpose (A * Matrix.diagonal z), Matrix.transpose_mul,
    Matrix.diagonal_transpose]
  exact (hsSq_diagonal_mul_le z hz Aᵀ).trans_eq (hsSq_transpose A)

/-- The actual off-diagonal covariance block satisfies the legal equation. -/
theorem kernel_cross_identity (E F : Matrix ι ι ℝ) :
    (kernelProjection E F).toBlocks₁₂ =
      E * (kernelProjection E F).toBlocks₁₂ + F * (kernelProjection E F).toBlocks₂₂ := by
  ext i j
  have h12 := congrArg (fun A => A (Sum.inl i) (Sum.inr j)) (kernelProjection_legal E F)
  simp [topProjection, rowPerturbation, Matrix.mul_apply, Fintype.sum_sum_type,
    sub_mul, Finset.sum_sub_distrib, Matrix.one_apply] at h12
  change (kernelProjection E F) (Sum.inl i) (Sum.inr j) =
    (∑ k, E i k * (kernelProjection E F) (Sum.inl k) (Sum.inr j)) +
    (∑ k, F i k * (kernelProjection E F) (Sum.inr k) (Sum.inr j))
  linarith

theorem sqrt_product_bound {a b A B : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (haA : a ≤ A) (hbB : b ≤ B) : Real.sqrt (a * b) ≤ Real.sqrt (A * B) :=
  Real.sqrt_le_sqrt (mul_le_mul haA hbB hb (ha.trans haA))

/-- The mixed covariance is controlled using its legal equation; the source
cross term is retained with its sign up to this final absolute-value bound. -/
theorem kernel_mixed_bound (E F : Matrix ι ι ℝ) (z : ι → ℝ)
    (hz : ∀ i, |z i| ≤ 1) {h : ℝ} (hh : 0 ≤ h)
    (hE : hsSq E ≤ h) (hF : hsSq F ≤ 4 * h)
    (hbase : |realTrace (Matrix.diagonal z * F)| ≤ 2 * h) :
    |realTrace (Matrix.diagonal z * (kernelProjection E F).toBlocks₁₂)| ≤
      (2 + 3 * Real.sqrt 5) * h := by
  let P := kernelProjection E F
  have hproj := kernel_projection_block_estimates E F
  dsimp only at hproj
  have hcross : hsSq P.toBlocks₁₂ ≤ 5 * h := hproj.2.2.1.trans (by linarith)
  have hdefect : hsSq (1 - P.toBlocks₂₂) ≤ 5 * h := hproj.2.2.2.trans (by linarith)
  have hid : Matrix.diagonal z * P.toBlocks₁₂ = Matrix.diagonal z * F +
      (Matrix.diagonal z * E) * P.toBlocks₁₂ -
      (Matrix.diagonal z * F) * (1 - P.toBlocks₂₂) := by
    have hk := kernel_cross_identity E F
    change P.toBlocks₁₂ = E * P.toBlocks₁₂ + F * P.toBlocks₂₂ at hk
    calc
      _ = Matrix.diagonal z * (E * P.toBlocks₁₂ + F * P.toBlocks₂₂) := by
        exact congrArg (fun A => Matrix.diagonal z * A) hk
      _ = _ := by noncomm_ring
  have he : |realTrace ((Matrix.diagonal z * E) * P.toBlocks₁₂)| ≤
      Real.sqrt (h * (5 * h)) :=
    (abs_trace_mul_le_sqrt _ _).trans (sqrt_product_bound
      (hsSq_nonneg _) (hsSq_nonneg _)
      ((hsSq_diagonal_mul_le z hz E).trans hE) hcross)
  have hf : |realTrace ((Matrix.diagonal z * F) * (1 - P.toBlocks₂₂))| ≤
      Real.sqrt ((4 * h) * (5 * h)) :=
    (abs_trace_mul_le_sqrt _ _).trans (sqrt_product_bound
      (hsSq_nonneg _) (hsSq_nonneg _)
      ((hsSq_diagonal_mul_le z hz F).trans hF) hdefect)
  have hs₁ : Real.sqrt (h * (5 * h)) = Real.sqrt 5 * h := by
    rw [show h * (5 * h) = 5 * h ^ 2 by ring, Real.sqrt_mul (by norm_num),
      Real.sqrt_sq hh]
  have hs₂ : Real.sqrt ((4 * h) * (5 * h)) = 2 * Real.sqrt 5 * h := by
    rw [show (4 * h) * (5 * h) = 4 * (5 * h ^ 2) by ring,
      Real.sqrt_mul (by norm_num), Real.sqrt_mul (by norm_num), Real.sqrt_sq hh]
    norm_num
    ring
  rw [hs₁] at he
  rw [hs₂] at hf
  calc
    _ = |realTrace (Matrix.diagonal z * F) +
        realTrace ((Matrix.diagonal z * E) * P.toBlocks₁₂) -
        realTrace ((Matrix.diagonal z * F) * (1 - P.toBlocks₂₂))| := by
      rw [hid, realTrace_sub, realTrace_add]
    _ ≤ |realTrace (Matrix.diagonal z * F)| +
        |realTrace ((Matrix.diagonal z * E) * P.toBlocks₁₂)| +
        |realTrace ((Matrix.diagonal z * F) * (1 - P.toBlocks₂₂))| :=
      (abs_sub _ _).trans (add_le_add_right (abs_add_le _ _) _)
    _ ≤ _ := by linarith

theorem bottom_defect_posSemidef (E F : Matrix ι ι ℝ) :
    (1 - (kernelProjection E F).toBlocks₂₂).PosSemidef := by
  have h := ((kernelProjection_isStarProjection E F).one_sub.nonneg).posSemidef
  have hs := h.submatrix Sum.inr
  convert hs using 1
  ext i j
  simp [Matrix.toBlocks₂₂, Matrix.submatrix, Matrix.one_apply]

/-- The direct diagonal debit survives averaging against the actual covariance. -/
theorem kernel_direct_bound (E F : Matrix ι ι ℝ) (d : ι → ℝ)
    {h u : ℝ} (hu : 0 < u) (hd : ∀ i, d i ≤ 1 / u)
    (hsum : ∑ i, d i = h) (hE : hsSq E ≤ h) (hF : hsSq F ≤ 4 * h) :
    (1 - 5 / u) * h ≤
      realTrace (Matrix.diagonal d * (kernelProjection E F).toBlocks₂₂) := by
  let P := kernelProjection E F
  have hcap : Matrix.diagonal d ≤ (1 / u) • (1 : Matrix ι ι ℝ) := by
    apply Matrix.le_iff.mpr
    rw [← Matrix.diagonal_one, ← Matrix.diagonal_smul, Matrix.diagonal_sub]
    exact Matrix.posSemidef_diagonal_iff.mpr (fun i => by simpa using sub_nonneg.mpr (hd i))
  have ht := realTrace_mul_mono (bottom_defect_posSemidef E F) hcap
  rw [realTrace_mul_comm (1 - P.toBlocks₂₂), Matrix.mul_smul, Matrix.mul_one,
    realTrace_smul, Matrix.mul_sub, Matrix.mul_one, realTrace_sub] at ht
  have htrace : realTrace (Matrix.diagonal d) = h := by
    simpa [realTrace] using hsum
  rw [htrace] at ht
  have hproj := (kernel_projection_block_estimates E F).2.1
  have htracebound : realTrace (1 - P.toBlocks₂₂) ≤ 5 * h := hproj.trans (by linarith)
  have ht' := mul_le_mul_of_nonneg_left htracebound (by positivity : 0 ≤ 1 / u)
  have heq : (1 - 5 / u) * h = h - (1 / u) * (5 * h) := by ring
  rw [heq]
  linarith

/-- A PSD response quadratic contracts when averaged with an orthogonal projection. -/
theorem kernel_response_bound (E F : Matrix ι ι ℝ)
    {H : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ} (hH : H.PosSemidef)
    {h : ℝ} (htrace : realTrace H ≤ 5 * h) :
    realTrace (H * kernelProjection E F) ≤ 5 * h := by
  have hb := realTrace_mul_mono hH (kernelProjection_isStarProjection E F).le_one
  rw [Matrix.mul_one] at hb
  exact hb.trans htrace

/-- The exact covariance trace expression of the legal upper quadratic. -/
def averagedUpper (E F : Matrix ι ι ℝ) (d z : ι → ℝ)
    (H : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) (u : ℝ) : ℝ :=
  -realTrace (Matrix.diagonal d * (kernelProjection E F).toBlocks₂₂) +
    realTrace (H * kernelProjection E F) / u -
    realTrace (Matrix.diagonal z * (kernelProjection E F).toBlocks₁₂) / u

/-- Equation (41), with all three terms of the legal response retained. -/
theorem averaged_upper_bound (E F : Matrix ι ι ℝ) (d z : ι → ℝ)
    (H : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) {h u : ℝ}
    (hh : 0 ≤ h) (hu : 0 < u) (hd : ∀ i, d i ≤ 1 / u)
    (hsum : ∑ i, d i = h) (hz : ∀ i, |z i| ≤ 1)
    (hE : hsSq E ≤ h) (hF : hsSq F ≤ 4 * h)
    (hbase : |realTrace (Matrix.diagonal z * F)| ≤ 2 * h)
    (hH : H.PosSemidef) (htrace : realTrace H ≤ 5 * h) :
    averagedUpper E F d z H u ≤ -(1 - (12 + 3 * Real.sqrt 5) / u) * h := by
  have hdirect := kernel_direct_bound E F d hu hd hsum hE hF
  have hresp := div_le_div_of_nonneg_right (kernel_response_bound E F hH htrace) hu.le
  have hmix := kernel_mixed_bound E F z hz hh hE hF hbase
  have hmix' := neg_le_of_abs_le hmix
  have hmdiv := div_le_div_of_nonneg_right hmix' hu.le
  unfold averagedUpper
  have he : -(1 - (12 + 3 * Real.sqrt 5) / u) * h =
      -((1 - 5 / u) * h) + 5 * h / u + (2 + 3 * Real.sqrt 5) * h / u := by ring
  rw [he]
  simp only [neg_div] at hmdiv
  linarith

/-- In particular u=64 has a strictly negative averaged legal upper form. -/
theorem averaged_upper_negative_64 (E F : Matrix ι ι ℝ) (d z : ι → ℝ)
    (H : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) {h : ℝ}
    (hh : 0 < h) (hd : ∀ i, d i ≤ 1 / 64)
    (hsum : ∑ i, d i = h) (hz : ∀ i, |z i| ≤ 1)
    (hE : hsSq E ≤ h) (hF : hsSq F ≤ 4 * h)
    (hbase : |realTrace (Matrix.diagonal z * F)| ≤ 2 * h)
    (hH : H.PosSemidef) (htrace : realTrace H ≤ 5 * h) :
    averagedUpper E F d z H 64 < 0 := by
  have hbound := averaged_upper_bound E F d z H hh.le (by norm_num) hd hsum hz hE hF hbase hH htrace
  have hs : Real.sqrt 5 < 3 := (Real.sqrt_lt (by norm_num) (by norm_num)).mpr (by norm_num)
  have hc : 0 < 1 - (12 + 3 * Real.sqrt 5) / 64 := by linarith
  exact hbound.trans_lt (mul_neg_of_neg_of_pos (neg_neg_of_pos hc) hh)

/-- Similarity by the positive diagonal square root of R. -/
def weightedConjugate (R : ι → ℝ) (T : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  Matrix.diagonal (fun i => Real.sqrt (R i)) * T *
    Matrix.diagonal (fun i => (Real.sqrt (R i))⁻¹)

theorem weightedConjugate_hsSq (R : ι → ℝ) (hR : ∀ i, 0 < R i)
    (T : Matrix ι ι ℝ) :
    hsSq (weightedConjugate R T) =
      ∑ j, (Tᵀ * Matrix.diagonal R * T) j j / R j := by
  rw [hsSq_eq_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [weightedConjugate, Matrix.mul_diagonal, Matrix.diagonal_mul,
    mul_pow, inv_pow, Real.sq_sqrt (hR _).le]
  rw [Matrix.mul_apply, Finset.sum_div]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem weightedConjugate_diagonal (R : ι → ℝ) (hR : ∀ i, 0 < R i)
    (T : Matrix ι ι ℝ) (i : ι) : weightedConjugate R T i i = T i i := by
  simp only [weightedConjugate, Matrix.mul_diagonal, Matrix.diagonal_mul]
  field_simp [(Real.sqrt_pos.mpr (hR i)).ne']

theorem weightedConjugate_sub (R : ι → ℝ) (A B : Matrix ι ι ℝ) :
    weightedConjugate R (A - B) = weightedConjugate R A - weightedConjugate R B := by
  simp only [weightedConjugate, Matrix.mul_sub, Matrix.sub_mul]

theorem weightedConjugate_mul_diagonal (R z : ι → ℝ) (T : Matrix ι ι ℝ) :
    weightedConjugate R (T * Matrix.diagonal z) = weightedConjugate R T * Matrix.diagonal z := by
  ext i j
  simp only [weightedConjugate, Matrix.mul_diagonal, Matrix.diagonal_mul]
  ring

/-- The squared weighted Gram energy follows from the actual Fisher matrix
inequality and the weighted diagonal budget. -/
theorem weightedConjugate_hsSq_le (R d : ι → ℝ) (hR : ∀ i, 0 < R i)
    (T Γ : Matrix ι ι ℝ) (hFisher : Tᵀ * Matrix.diagonal R * T ≤ Γ)
    (hdiag : ∀ i, Γ i i / R i ≤ d i) :
    hsSq (weightedConjugate R T) ≤ ∑ i, d i := by
  rw [weightedConjugate_hsSq R hR]
  apply Finset.sum_le_sum
  intro i _
  apply le_trans _ (hdiag i)
  apply div_le_div_of_nonneg_right _ (hR i).le
  have h := (Matrix.le_iff.mp hFisher).2 (Pi.single i 1)
  simpa [Matrix.mulVec_single, single_dotProduct, star_trivial] using h

theorem hsSq_sub_le (A B : Matrix ι ι ℝ) :
    hsSq (A - B) ≤ 2 * (hsSq A + hsSq B) := by
  have h := hsSq_nonneg (A + B)
  have he : hsSq (A - B) + hsSq (A + B) = 2 * (hsSq A + hsSq B) := by
    simp only [hsSq, Matrix.transpose_sub, Matrix.transpose_add, Matrix.sub_mul,
      Matrix.add_mul, Matrix.mul_sub, Matrix.mul_add, realTrace_add, realTrace_sub]
    ring
  linarith

/-- The concrete E,F definitions in (33), with their complete 1h and 4h
squared HS bounds, obtained from the two Fisher inequalities. -/
theorem weighted_pair_energy_bounds (R d z : ι → ℝ) (hR : ∀ i, 0 < R i)
    (hz : ∀ i, |z i| ≤ 1) (T TJ Γ : Matrix ι ι ℝ)
    (hT : Tᵀ * Matrix.diagonal R * T ≤ Γ)
    (hTJ : TJᵀ * Matrix.diagonal R * TJ ≤ Γ)
    (hdiag : ∀ i, Γ i i / R i ≤ d i) :
    hsSq (weightedConjugate R T) ≤ ∑ i, d i ∧
      hsSq (weightedConjugate R (TJ - T * Matrix.diagonal z)) ≤ 4 * ∑ i, d i := by
  have hE := weightedConjugate_hsSq_le R d hR T Γ hT hdiag
  have hJ := weightedConjugate_hsSq_le R d hR TJ Γ hTJ hdiag
  refine ⟨hE, ?_⟩
  rw [weightedConjugate_sub, weightedConjugate_mul_diagonal]
  have hF := hsSq_sub_le (weightedConjugate R TJ)
    (weightedConjugate R T * Matrix.diagonal z)
  have hZ := hsSq_mul_diagonal_le z hz (weightedConjugate R T)
  linarith

/-- The baseline mixed trace is controlled by actual diagonal Gram entries. -/
theorem weighted_pair_mixed_baseline (R d z : ι → ℝ) (hR : ∀ i, 0 < R i)
    (hz : ∀ i, |z i| ≤ 1) (T TJ : Matrix ι ι ℝ)
    (hTnonneg : ∀ i, 0 ≤ T i i) (hTdiag : ∀ i, T i i ≤ d i)
    (hTJdiag : ∀ i, |TJ i i| ≤ T i i) :
    |realTrace (Matrix.diagonal z * weightedConjugate R (TJ - T * Matrix.diagonal z))| ≤
      2 * ∑ i, d i := by
  change |∑ i, (Matrix.diagonal z * weightedConjugate R
    (TJ - T * Matrix.diagonal z)) i i| ≤ _
  simp only [Matrix.diagonal_mul, weightedConjugate_diagonal R hR, Matrix.sub_apply,
    Matrix.mul_diagonal]
  apply le_trans (Finset.abs_sum_le_sum_abs _ _)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  calc
    |z i * (TJ i i - T i i * z i)| = |z i| * |TJ i i - T i i * z i| := abs_mul _ _
    _ ≤ |TJ i i - T i i * z i| := by
      simpa using mul_le_mul_of_nonneg_right (hz i) (abs_nonneg (TJ i i - T i i * z i))
    _ ≤ |TJ i i| + |T i i * z i| := abs_sub _ _
    _ = |TJ i i| + T i i * |z i| := by rw [abs_mul, abs_of_nonneg (hTnonneg i)]
    _ ≤ 2 * d i := by
      have hmul := mul_le_mul_of_nonneg_left (hz i) (hTnonneg i)
      linarith [hTJdiag i, hTdiag i]

/-- A matrix for the legal upper quadratic, before unwhitening. -/
def upperMatrix (d z : ι → ℝ) (H : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) (u : ℝ) :
    Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ :=
  (1 / u) • H - Matrix.fromBlocks 0 ((1 / u) • Matrix.diagonal z) 0 (Matrix.diagonal d)

theorem upperMatrix_quadratic (d z : ι → ℝ)
    (H : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) (u : ℝ) (x : ι ⊕ ι → ℝ) :
    x ⬝ᵥ (upperMatrix d z H u *ᵥ x) =
      -(x ∘ Sum.inr) ⬝ᵥ (Matrix.diagonal d *ᵥ (x ∘ Sum.inr)) +
      (x ⬝ᵥ (H *ᵥ x)) / u -
      ((x ∘ Sum.inl) ⬝ᵥ (Matrix.diagonal z *ᵥ (x ∘ Sum.inr))) / u := by
  rw [upperMatrix, Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul]
  simp only [Matrix.fromBlocks_mulVec, Matrix.zero_mulVec, zero_add, Matrix.smul_mulVec]
  simp only [Matrix.dotProduct_block, Function.comp_def, Sum.elim_inl, Sum.elim_inr,
    dotProduct_smul, neg_dotProduct, smul_eq_mul]
  ring

theorem projection_cross_trace (P : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ)
    (hP : IsStarProjection P) (z : ι → ℝ) :
    realTrace (Matrix.diagonal z * P.toBlocks₂₁) =
      realTrace (Matrix.diagonal z * P.toBlocks₁₂) := by
  change (∑ i, (Matrix.diagonal z * P.toBlocks₂₁) i i) =
    ∑ i, (Matrix.diagonal z * P.toBlocks₁₂) i i
  simp only [Matrix.diagonal_mul]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  have h := congrArg (fun A => A (Sum.inl i) (Sum.inr i)) (projection_transpose hP)
  exact h

theorem upperMatrix_covariance_trace (E F : Matrix ι ι ℝ) (d z : ι → ℝ)
    (H : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) (u : ℝ) :
    realTrace (upperMatrix d z H u * kernelProjection E F) =
      averagedUpper E F d z H u := by
  let P := kernelProjection E F
  rw [upperMatrix, Matrix.sub_mul, Matrix.smul_mul, realTrace_sub, realTrace_smul]
  have hp := Matrix.fromBlocks_toBlocks P
  have he : realTrace (Matrix.fromBlocks 0 ((1 / u) • Matrix.diagonal z) 0
      (Matrix.diagonal d) * P) =
      (1 / u) * realTrace (Matrix.diagonal z * P.toBlocks₁₂) +
      realTrace (Matrix.diagonal d * P.toBlocks₂₂) := by
    conv_lhs => arg 1; arg 2; rw [← hp]
    rw [Matrix.fromBlocks_multiply, realTrace_fromBlocks]
    simp only [Matrix.zero_mul, zero_add, Matrix.smul_mul, realTrace_smul]
    rw [projection_cross_trace P (kernelProjection_isStarProjection E F) z]
  rw [he]
  unfold averagedUpper
  ring

/-- Projection columns form a finite centered covariance realization after
pairing each column with its negative. Only the second moment is needed here. -/
theorem projection_quadratic_sum (P M : Matrix ι ι ℝ) (hP : IsStarProjection P) :
    (∑ j, (P *ᵥ Pi.single j 1) ⬝ᵥ (M *ᵥ (P *ᵥ Pi.single j 1))) =
      realTrace (M * P) := by
  have hquad (j : ι) :
      (P *ᵥ Pi.single j 1) ⬝ᵥ (M *ᵥ (P *ᵥ Pi.single j 1)) = (Pᵀ * M * P) j j := by
    have he : (Pi.single j 1) ⬝ᵥ ((Pᵀ * M * P) *ᵥ Pi.single j 1) =
        (P *ᵥ Pi.single j 1) ⬝ᵥ (M *ᵥ (P *ᵥ Pi.single j 1)) := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
    rw [← he]
    simp [single_dotProduct, Matrix.mulVec_single]
  simp only [hquad]
  change realTrace (Pᵀ * M * P) = realTrace (M * P)
  rw [projection_transpose hP, realTrace_mul_cycle, projection_mul_self hP,
    realTrace_mul_comm]

/-- A negative finite covariance average supplies an actual legal joint vector. -/
theorem exists_negative_kernel_direction (E F : Matrix ι ι ℝ) (d z : ι → ℝ)
    (H : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) (u : ℝ)
    (hneg : averagedUpper E F d z H u < 0) :
    ∃ x : ι ⊕ ι → ℝ,
      constraintMatrix E F *ᵥ x = 0 ∧ x ⬝ᵥ (upperMatrix d z H u *ᵥ x) < 0 := by
  have hsum := projection_quadratic_sum (kernelProjection E F) (upperMatrix d z H u)
    (kernelProjection_isStarProjection E F)
  rw [upperMatrix_covariance_trace] at hsum
  have hex : ∃ j, (kernelProjection E F *ᵥ Pi.single j 1) ⬝ᵥ
      (upperMatrix d z H u *ᵥ (kernelProjection E F *ᵥ Pi.single j 1)) < 0 := by
    by_contra h
    have hp : 0 ≤ ∑ j, (kernelProjection E F *ᵥ Pi.single j 1) ⬝ᵥ
        (upperMatrix d z H u *ᵥ (kernelProjection E F *ᵥ Pi.single j 1)) := by
      apply Finset.sum_nonneg
      intro j _
      exact le_of_not_gt (fun hj => h ⟨j, hj⟩)
    rw [hsum] at hp
    linarith
  obtain ⟨j, hj⟩ := hex
  refine ⟨kernelProjection E F *ᵥ Pi.single j 1, ?_, hj⟩
  rw [Matrix.mulVec_mulVec, kernelProjection_constraint, Matrix.zero_mulVec]

theorem negative_kernel_bottom_ne_zero (d z : ι → ℝ)
    {H : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ} (hH : H.PosSemidef) {u : ℝ} (hu : 0 < u)
    {x : ι ⊕ ι → ℝ} (hneg : x ⬝ᵥ (upperMatrix d z H u *ᵥ x) < 0) :
    x ∘ Sum.inr ≠ 0 := by
  intro hv
  rw [upperMatrix_quadratic, hv] at hneg
  simp only [neg_zero, Matrix.mulVec_zero, dotProduct_zero, zero_add, zero_div, sub_zero] at hneg
  have hq := hH.2 x
  simp only [star_trivial] at hq
  exact (not_lt_of_ge (div_nonneg hq hu.le)) hneg

def unwhiten (R : ι → ℝ) (x : ι → ℝ) : ι → ℝ :=
  Matrix.diagonal (fun i => (Real.sqrt (R i))⁻¹) *ᵥ x

theorem unwhiten_apply (R x : ι → ℝ) (i : ι) :
    unwhiten R x i = x i / Real.sqrt (R i) := by
  simp only [unwhiten, Matrix.mulVec_diagonal]
  ring

theorem unwhiten_sub (R x y : ι → ℝ) :
    unwhiten R (x - y) = unwhiten R x - unwhiten R y := Matrix.mulVec_sub _ _ _

theorem unwhiten_ne_zero (R : ι → ℝ) (hR : ∀ i, 0 < R i)
    {x : ι → ℝ} (hx : x ≠ 0) : unwhiten R x ≠ 0 := by
  intro h
  apply hx
  funext i
  have hi := congrFun h i
  rw [unwhiten_apply] at hi
  exact (div_eq_zero_iff).mp hi |>.resolve_right (Real.sqrt_pos.mpr (hR i)).ne'

theorem unwhiten_weightedConjugate (R : ι → ℝ) (hR : ∀ i, 0 < R i)
    (T : Matrix ι ι ℝ) (x : ι → ℝ) :
    unwhiten R (weightedConjugate R T *ᵥ x) = T *ᵥ unwhiten R x := by
  let W : Matrix ι ι ℝ := Matrix.diagonal (fun i => Real.sqrt (R i))
  let V : Matrix ι ι ℝ := Matrix.diagonal (fun i => (Real.sqrt (R i))⁻¹)
  have hvw : V * W = 1 := by
    change Matrix.diagonal (fun i => (Real.sqrt (R i))⁻¹) *
      Matrix.diagonal (fun i => Real.sqrt (R i)) = 1
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact inv_mul_cancel₀ (Real.sqrt_pos.mpr (hR i)).ne'
  change V *ᵥ ((W * T * V) *ᵥ x) = T *ᵥ (V *ᵥ x)
  rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hvw,
    Matrix.one_mul, Matrix.mulVec_mulVec]

theorem constraint_mulVec (E F : Matrix ι ι ℝ) (x : ι ⊕ ι → ℝ) :
    constraintMatrix E F *ᵥ x =
      (1 - E) *ᵥ (x ∘ Sum.inl) - F *ᵥ (x ∘ Sum.inr) := by
  ext i
  simp only [constraintMatrix, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
    Sum.elim_inl, Sum.elim_inr, Matrix.neg_apply, neg_mul, Finset.sum_neg_distrib,
    Pi.sub_apply, Function.comp_def, sub_eq_add_neg]

/-- The covariance's legal equation becomes exactly equation (28) after
inverting only the strictly positive scalar diagonal R. -/
theorem unwhiten_legal (R : ι → ℝ) (hR : ∀ i, 0 < R i) (T TJ : Matrix ι ι ℝ)
    (z : ι → ℝ) {x : ι ⊕ ι → ℝ}
    (hx : constraintMatrix (weightedConjugate R T)
      (weightedConjugate R (TJ - T * Matrix.diagonal z)) *ᵥ x = 0) :
    (1 - T) *ᵥ unwhiten R (x ∘ Sum.inl) =
      (TJ - T * Matrix.diagonal z) *ᵥ unwhiten R (x ∘ Sum.inr) := by
  rw [constraint_mulVec, sub_eq_zero, Matrix.sub_mulVec, Matrix.one_mulVec] at hx
  have h := congrArg (unwhiten R) hx
  rw [unwhiten_sub, unwhiten_weightedConjugate R hR T,
    unwhiten_weightedConjugate R hR (TJ - T * Matrix.diagonal z)] at h
  simpa only [Matrix.sub_mulVec, Matrix.one_mulVec] using h

end MatrixSpencer.KSSpinDrift

namespace MatrixSpencer.KSSpinDrift

open KSWeightedProjection

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

section Physical

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Every PSD atom obeys D² ≤ Tr(D)D, with no rank restriction. -/
theorem atom_square_le_trace {D : Matrix n n ℂ} (hD : D.PosSemidef) :
    D * D ≤ realTrace D • D := by
  let S := CFC.sqrt D
  have hS : S.IsHermitian := (CFC.sqrt_nonneg D).posSemidef.isHermitian
  have hSS : S * S = D := CFC.sqrt_mul_sqrt_self D hD.nonneg
  have hSDS : S * D * S = D * D := by
    calc
      _ = S * (S * S) * S := congrArg (fun X => S * X * S) hSS.symm
      _ = (S * S) * (S * S) := by noncomm_ring
      _ = _ := by rw [hSS]
  have h := (Matrix.le_iff.mp (posSemidef_le_trace_identity hD)).conjTranspose_mul_mul_same S
  apply Matrix.le_iff.mpr
  simpa only [hS.eq, Algebra.algebraMap_eq_smul_one, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hSS, hSDS] using h

theorem gram_diagonal_le_trace_sq {D : Matrix n n ℂ} (hD : D.PosSemidef) :
    realTrace (D * D) ≤ realTrace D ^ 2 := by
  have h := realTrace_mul_mono hD (posSemidef_le_trace_identity hD)
  simpa only [Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, Matrix.mul_one,
    realTrace_smul, pow_two] using h

theorem physical_gram_diagonal_le {P D : Matrix n n ℂ}
    (hP : P.PosSemidef) (hD : D.PosSemidef) :
    realTrace (P * D * D) ≤ realTrace D * realTrace (P * D) := by
  have h := realTrace_mul_mono hP (atom_square_le_trace hD)
  simpa only [Matrix.mul_smul, realTrace_smul, Matrix.mul_assoc] using h

theorem spin_gram_diagonal_abs_le {J D : Matrix n n ℂ}
    (hJ : J.IsHermitian) (hJJ : J * J = 1) (hD : D.IsHermitian) :
    |realTrace (D * J * D)| ≤ realTrace (D * D) := by
  have hDD : (D * D).PosSemidef := by
    simpa only [hD.eq] using Matrix.posSemidef_conjTranspose_mul_self D
  have h := DyadicTraceInterpolation.weightedTrace_sq_le hDD hJ
  rw [hJJ, Matrix.mul_one] at h
  have he : realTrace (D * J * D) = realTrace (D * D * J) := by
    simpa only [Matrix.mul_assoc] using realTrace_mul_cycle D J D
  rw [he]
  apply (sq_le_sq₀ (abs_nonneg _) (realTrace_nonneg hDD)).mp
  rw [sq_abs]
  simpa only [pow_two] using h

theorem spin_atom_isHermitian {J D : Matrix n n ℂ}
    (hJ : J.IsHermitian) (hD : D.IsHermitian) (hc : J * D = D * J) :
    (J * D).IsHermitian := by
  simp only [Matrix.IsHermitian, Matrix.conjTranspose_mul, hD.eq, hJ.eq]
  exact hc.symm

theorem spin_atom_square {J D : Matrix n n ℂ}
    (hJJ : J * J = 1) (hc : J * D = D * J) : (J * D) * (J * D) = D * D := by
  calc
    _ = J * (D * J) * D := by noncomm_ring
    _ = J * (J * D) * D := by rw [← hc]
    _ = _ := by rw [← Matrix.mul_assoc J J, hJJ, Matrix.one_mul]

theorem weighted_square_sub_le {P X Y : Matrix n n ℂ}
    (hP : P.PosSemidef) (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    realTrace (P * ((X - Y) * (X - Y))) ≤
      2 * (realTrace (P * (X * X)) + realTrace (P * (Y * Y))) := by
  have hsum : ((X + Y) * (X + Y)).PosSemidef := by
    simpa only [(hX.add hY).eq] using Matrix.posSemidef_conjTranspose_mul_self (X + Y)
  have h := realTrace_mul_nonneg hP hsum
  have he : realTrace (P * ((X - Y) * (X - Y))) +
      realTrace (P * ((X + Y) * (X + Y))) =
      2 * (realTrace (P * (X * X)) + realTrace (P * (Y * Y))) := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.add_mul, Matrix.mul_add,
      realTrace_sub, realTrace_add]
    ring
  linarith

/-- The actual spin source feature has at most four times the weighted atom
energy. This only uses commutation of the atom with the involution. -/
theorem spin_feature_energy_le {P J D : Matrix n n ℂ}
    (hP : P.PosSemidef) (hJ : J.IsHermitian) (hJJ : J * J = 1)
    (hD : D.IsHermitian) (hc : J * D = D * J) {z : ℝ} (hz : |z| ≤ 1) :
    realTrace (P * ((J * D - z • D) * (J * D - z • D))) ≤
      4 * realTrace (P * (D * D)) := by
  have hzD : (z • D).IsHermitian := by
    simp only [Matrix.IsHermitian, Matrix.conjTranspose_smul, hD.eq, star_trivial]
  have h := weighted_square_sub_le hP (spin_atom_isHermitian hJ hD hc) hzD
  rw [spin_atom_square hJJ hc] at h
  simp only [Matrix.smul_mul, Matrix.mul_smul, realTrace_smul] at h
  have hDD : (D * D).PosSemidef := by
    simpa only [hD.eq] using Matrix.posSemidef_conjTranspose_mul_self D
  have hnonneg := realTrace_mul_nonneg hP hDD
  have hzsq : z ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one _).mpr hz
  have hmul := mul_le_mul_of_nonneg_right hzsq hnonneg
  nlinarith

/-- Both physical features in the order `(w,v)` of the joint covariance. -/
def jointFeatures (D : ι → Matrix n n ℂ) (J : Matrix n n ℂ) (R z : ι → ℝ) :
    (ι ⊕ ι) → Matrix n n ℂ :=
  Sum.elim (fun i => (Real.sqrt (R i))⁻¹ • D i)
    (fun i => (Real.sqrt (R i))⁻¹ • (J * D i - z i • D i))

theorem jointFeatures_isHermitian (D : ι → Matrix n n ℂ) (hD : ∀ i, (D i).IsHermitian)
    {J : Matrix n n ℂ} (hJ : J.IsHermitian) (hc : ∀ i, J * D i = D i * J)
    (R z : ι → ℝ) (i : ι ⊕ ι) : (jointFeatures D J R z i).IsHermitian := by
  have hsmul (c : ℝ) {X : Matrix n n ℂ} (hX : X.IsHermitian) : (c • X).IsHermitian := by
    simp only [Matrix.IsHermitian, Matrix.conjTranspose_smul, hX.eq, star_trivial]
  cases i with
  | inl i => exact hsmul _ (hD i)
  | inr i => exact hsmul _ ((spin_atom_isHermitian hJ (hD i) (hc i)).sub (hsmul _ (hD i)))

theorem weighted_scaled_energy (P D : Matrix n n ℂ) {R : ℝ} (hR : 0 < R) :
    realTrace (P * ((Real.sqrt R)⁻¹ • D) * ((Real.sqrt R)⁻¹ • D)) =
      realTrace (P * D * D) / R := by
  simp only [Matrix.smul_mul, Matrix.mul_smul, realTrace_smul]
  have hs := Real.sq_sqrt hR.le
  field_simp [(Real.sqrt_pos.mpr hR).ne', hR.ne']
  rw [hs]
  ring

/-- The PSD physical response Gram has the exact 5h trace budget. -/
theorem joint_response_trace_le (D : ι → Matrix n n ℂ)
    (hD : ∀ i, (D i).IsHermitian) {P J : Matrix n n ℂ}
    (hP : P.PosSemidef) (hJ : J.IsHermitian) (hJJ : J * J = 1)
    (hc : ∀ i, J * D i = D i * J) (R z d : ι → ℝ)
    (hR : ∀ i, 0 < R i) (hz : ∀ i, |z i| ≤ 1)
    (hdiag : ∀ i, realTrace (P * D i * D i) / R i ≤ d i) :
    realTrace (physicalRealGram P (jointFeatures D J R z)) ≤ 5 * ∑ i, d i := by
  change (∑ k, realTrace (P * jointFeatures D J R z k * jointFeatures D J R z k)) ≤ _
  rw [Fintype.sum_sum_type]
  have hw : (∑ i, realTrace (P * jointFeatures D J R z (Sum.inl i) *
      jointFeatures D J R z (Sum.inl i))) ≤ ∑ i, d i := by
    apply Finset.sum_le_sum
    intro i _
    change realTrace (P * ((Real.sqrt (R i))⁻¹ • D i) * ((Real.sqrt (R i))⁻¹ • D i)) ≤ _
    rw [weighted_scaled_energy P (D i) (hR i)]
    exact hdiag i
  have hv : (∑ i, realTrace (P * jointFeatures D J R z (Sum.inr i) *
      jointFeatures D J R z (Sum.inr i))) ≤ 4 * ∑ i, d i := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    change realTrace (P * ((Real.sqrt (R i))⁻¹ • (J * D i - z i • D i)) *
      ((Real.sqrt (R i))⁻¹ • (J * D i - z i • D i))) ≤ _
    rw [weighted_scaled_energy P _ (hR i)]
    have he := div_le_div_of_nonneg_right
      (spin_feature_energy_le hP hJ hJJ (hD i) (hc i) (hz i)) (hR i).le
    have hd := mul_le_mul_of_nonneg_left (hdiag i) (by norm_num : (0 : ℝ) ≤ 4)
    simp only [← Matrix.mul_assoc] at he
    rw [mul_div_assoc] at he
    exact he.trans hd
  linarith

/-- The strictly positive coefficient Fisher weights of a physical state. -/
def fisherWeight (P : Matrix n n ℂ) (D : ι → Matrix n n ℂ) (i : ι) : ℝ :=
  realTrace (P * D i) / realTrace (D i)

def spinE (P : Matrix n n ℂ) (D : ι → Matrix n n ℂ) : Matrix ι ι ℝ :=
  weightedConjugate (fisherWeight P D) (KSFisher.gram D)

def spinF (P J : Matrix n n ℂ) (D : ι → Matrix n n ℂ) (z : ι → ℝ) : Matrix ι ι ℝ :=
  weightedConjugate (fisherWeight P D) (KSFisher.spinGram J D - KSFisher.gram D * Matrix.diagonal z)

def spinResponseGram (P J : Matrix n n ℂ) (D : ι → Matrix n n ℂ) (z : ι → ℝ) :
    Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ :=
  physicalRealGram P (jointFeatures D J (fisherWeight P D) z)

theorem jointFeatures_synthesis (D : ι → Matrix n n ℂ) (J : Matrix n n ℂ)
    (R z : ι → ℝ) (x : ι ⊕ ι → ℝ) :
    KSFisher.synthesis (jointFeatures D J R z) x =
      J * KSFisher.synthesis D (unwhiten R (x ∘ Sum.inr)) -
      KSFisher.synthesis D (Matrix.diagonal z *ᵥ unwhiten R (x ∘ Sum.inr)) +
      KSFisher.synthesis D (unwhiten R (x ∘ Sum.inl)) := by
  simp only [KSFisher.synthesis, Fintype.sum_sum_type, jointFeatures,
    Sum.elim_inl, Sum.elim_inr, smul_smul, smul_sub, Finset.sum_sub_distrib,
    Matrix.mul_sum, Matrix.mul_smul, Matrix.mulVec_diagonal, unwhiten_apply,
    Function.comp_apply, div_eq_mul_inv]
  have he : (∑ i, (z i * (x (Sum.inr i) * (Real.sqrt (R i))⁻¹)) • D i) =
      ∑ i, ((x (Sum.inr i) * (Real.sqrt (R i))⁻¹) * z i) • D i := by
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_comm (z i)]
  rw [he]
  simp only [mul_assoc]
  abel

theorem unwhiten_weighted_product (R : ι → ℝ) (hR : ∀ i, 0 < R i)
    (a b : ι → ℝ) (i : ι) :
    R i * unwhiten R a i * unwhiten R b i = a i * b i := by
  rw [unwhiten_apply, unwhiten_apply]
  have hs := Real.sq_sqrt (hR i).le
  field_simp [(Real.sqrt_pos.mpr (hR i)).ne']
  rw [hs]
  ring

/-- The exact legal upper form (30) in unwhitened coefficient variables. -/
def legalUpper (P J : Matrix n n ℂ) (D : ι → Matrix n n ℂ)
    (R d z : ι → ℝ) (u : ℝ) (δ y : ι → ℝ) : ℝ :=
  -(∑ i, R i * d i * y i ^ 2) +
    realTrace (P * ((J * KSFisher.synthesis D y - KSFisher.synthesis D (Matrix.diagonal z *ᵥ y) +
      KSFisher.synthesis D δ) *
      (J * KSFisher.synthesis D y - KSFisher.synthesis D (Matrix.diagonal z *ᵥ y) +
      KSFisher.synthesis D δ))) / u -
    (∑ i, δ i * R i * z i * y i) / u

theorem upperMatrix_eq_legalUpper (P J : Matrix n n ℂ) (D : ι → Matrix n n ℂ)
    (R d z : ι → ℝ) (hR : ∀ i, 0 < R i) (u : ℝ) (x : ι ⊕ ι → ℝ) :
    x ⬝ᵥ (upperMatrix d z (physicalRealGram P (jointFeatures D J R z)) u *ᵥ x) =
      legalUpper P J D R d z u (unwhiten R (x ∘ Sum.inl)) (unwhiten R (x ∘ Sum.inr)) := by
  rw [upperMatrix_quadratic, KSFisher.physicalGram_quadratic, jointFeatures_synthesis]
  unfold legalUpper
  have hd : (x ∘ Sum.inr) ⬝ᵥ (Matrix.diagonal d *ᵥ (x ∘ Sum.inr)) =
      ∑ i, R i * d i * unwhiten R (x ∘ Sum.inr) i ^ 2 := by
    simp only [dotProduct, Matrix.mulVec_diagonal]
    apply Finset.sum_congr rfl
    intro i _
    have hi := unwhiten_weighted_product R hR (x ∘ Sum.inr) (x ∘ Sum.inr) i
    linear_combination -(d i) * hi
  have hm : (x ∘ Sum.inl) ⬝ᵥ (Matrix.diagonal z *ᵥ (x ∘ Sum.inr)) =
      ∑ i, unwhiten R (x ∘ Sum.inl) i * R i * z i * unwhiten R (x ∘ Sum.inr) i := by
    simp only [dotProduct, Matrix.mulVec_diagonal]
    apply Finset.sum_congr rfl
    intro i _
    have hi := unwhiten_weighted_product R hR (x ∘ Sum.inl) (x ∘ Sum.inr) i
    linear_combination -(z i) * hi
  rw [neg_dotProduct, hd, hm]

theorem fisherWeight_pos {P : Matrix n n ℂ} (D : ι → Matrix n n ℂ)
    (hr : ∀ i, 0 < realTrace (D i)) (hm : ∀ i, 0 < realTrace (P * D i)) (i : ι) :
    0 < fisherWeight P D i := div_pos (hm i) (hr i)

theorem physical_weighted_diagonal {P : Matrix n n ℂ} (hP : P.PosSemidef)
    (D : ι → Matrix n n ℂ) (hD : ∀ i, (D i).PosSemidef)
    (hr : ∀ i, 0 < realTrace (D i)) (hm : ∀ i, 0 < realTrace (P * D i)) (i : ι) :
    realTrace (P * D i * D i) / fisherWeight P D i ≤ realTrace (D i) ^ 2 := by
  apply (div_le_iff₀ (fisherWeight_pos D hr hm i)).mpr
  calc
    _ ≤ realTrace (D i) * realTrace (P * D i) := physical_gram_diagonal_le hP (hD i)
    _ = _ := by unfold fisherWeight; field_simp [(hr i).ne']

/-- Equation (41) instantiated by actual complex PSD spin atoms and their
physical trace-and-prepare fixed point. Every weighted matrix and trace budget
is proved from these data. -/
theorem physical_averaged_upper_negative_64 [Nonempty ι]
    (D : ι → Matrix n n ℂ) (hD : ∀ i, (D i).PosSemidef)
    {P J : Matrix n n ℂ} (hP : P.PosSemidef) (hJ : J.IsHermitian)
    (hJJ : J * J = 1) (hc : ∀ i, J * D i = D i * J)
    (hr : ∀ i, 0 < realTrace (D i)) (hm : ∀ i, 0 < realTrace (P * D i))
    (hfix : P = ∑ i, realTrace (P * D i) • D i) (z : ι → ℝ)
    (hz : ∀ i, |z i| ≤ 1) (hsmall : ∀ i, realTrace (D i) ^ 2 ≤ 1 / 64) :
    averagedUpper (spinE P D) (spinF P J D z) (fun i => realTrace (D i) ^ 2) z
      (spinResponseGram P J D z) 64 < 0 := by
  let R := fisherWeight P D
  let T := KSFisher.gram D
  let TJ := KSFisher.spinGram J D
  let Γ := physicalRealGram P D
  let d : ι → ℝ := fun i => realTrace (D i) ^ 2
  have hR := fisherWeight_pos D hr hm
  have hdiag : ∀ i, Γ i i / R i ≤ d i := by
    intro i
    exact physical_weighted_diagonal hP D hD hr hm i
  have ht : Tᵀ = T := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using (KSFisher.gram_isHermitian D).eq
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
  have hh : 0 < ∑ i, d i := Finset.sum_pos (fun i _ => sq_pos_of_pos (hr i)) Finset.univ_nonempty
  exact averaged_upper_negative_64 (spinE P D) (spinF P J D z) d z
    (spinResponseGram P J D z) hh hsmall rfl hz henergy.1 henergy.2 hbase hresponse htrace

theorem fisherWeight_mul_trace_sq (P : Matrix n n ℂ) (D : ι → Matrix n n ℂ)
    (hr : ∀ i, 0 < realTrace (D i)) (i : ι) :
    fisherWeight P D i * realTrace (D i) ^ 2 =
      realTrace (D i) * realTrace (P * D i) := by
  unfold fisherWeight
  field_simp [(hr i).ne']
  <;> ring

/-- The full physical drift argument supplies an actual nonzero legal
coefficient direction with strictly negative upper form (30). -/
theorem exists_physical_negative_legal_direction [Nonempty ι]
    (D : ι → Matrix n n ℂ) (hD : ∀ i, (D i).PosSemidef)
    {P J : Matrix n n ℂ} (hP : P.PosSemidef) (hJ : J.IsHermitian)
    (hJJ : J * J = 1) (hc : ∀ i, J * D i = D i * J)
    (hr : ∀ i, 0 < realTrace (D i)) (hm : ∀ i, 0 < realTrace (P * D i))
    (hfix : P = ∑ i, realTrace (P * D i) • D i) (z : ι → ℝ)
    (hz : ∀ i, |z i| ≤ 1) (hsmall : ∀ i, realTrace (D i) ^ 2 ≤ 1 / 64) :
    ∃ δ y : ι → ℝ, y ≠ 0 ∧
      (1 - KSFisher.gram D) *ᵥ δ =
        (KSFisher.spinGram J D - KSFisher.gram D * Matrix.diagonal z) *ᵥ y ∧
      legalUpper P J D (fisherWeight P D) (fun i => realTrace (D i) ^ 2) z 64 δ y < 0 := by
  have hneg := physical_averaged_upper_negative_64 D hD hP hJ hJJ hc hr hm hfix z hz hsmall
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

end MatrixSpencer.KSSpinDrift
