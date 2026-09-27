import MatrixSpencer.KSSpinDrift

/-!
# Averaging the higher-rank two-frame response

The existence proof uses the actual projection onto legal pairs with no
extra linear constraint. The additional owner curvature pays the diagonal
mixed term even when the two frames are different.
-/

open Matrix MatrixSpencer MatrixSpencer.KSSpinDrift MatrixSpencer.KSWeightedProjection
open scoped BigOperators MatrixOrder

noncomputable section
namespace HigherRankKS.ProjectionAveraging

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem kernel_mixed_bound_with_baseline (E F : Matrix ι ι ℝ) (z : ι → ℝ)
    (hz : ∀ i, |z i| ≤ 1) {h : ℝ} (hh : 0 ≤ h)
    (hE : hsSq E ≤ h) (hF : hsSq F ≤ 4 * h) :
    |realTrace (Matrix.diagonal z * (kernelProjection E F).toBlocks₁₂)| ≤
      |realTrace (Matrix.diagonal z * F)| + 3 * Real.sqrt 5 * h := by
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

theorem diagonal_sq_sum_le_hsSq (B : Matrix ι ι ℝ) :
    ∑ i, (B i i) ^ 2 ≤ hsSq B := by
  rw [hsSq_eq_sum]
  apply Finset.sum_le_sum
  intro i _
  exact Finset.single_le_sum (fun j _ => sq_nonneg (B j i)) (Finset.mem_univ i)

theorem two_frame_mixed_baseline (E B : Matrix ι ι ℝ) (z : ι → ℝ)
    (hdiag : ∀ i, 0 ≤ E i i ∧ E i i ≤ 1)
    {h : ℝ} (hB : hsSq B ≤ h) :
    |realTrace (Matrix.diagonal z * (B - E * Matrix.diagonal z))| ≤
      (3 / 2 : ℝ) * (∑ i, (z i) ^ 2) + h / 2 := by
  have htrace : realTrace (Matrix.diagonal z * (B - E * Matrix.diagonal z)) =
      ∑ i, (z i * B i i - (z i) ^ 2 * E i i) := by
    simp only [realTrace, Matrix.trace, Matrix.diag, Matrix.diagonal_mul,
      Matrix.sub_apply, Matrix.mul_diagonal, RCLike.re_to_real]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [htrace]
  calc
    _ ≤ ∑ i, |z i * B i i - (z i) ^ 2 * E i i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ((3 / 2 : ℝ) * (z i) ^ 2 + (B i i) ^ 2 / 2) := by
      apply Finset.sum_le_sum
      intro i _
      apply (abs_sub _ _).trans
      rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (z i)),
        abs_of_nonneg (hdiag i).1]
      have hsq := sq_nonneg (|z i| - |B i i|)
      have hterm := mul_le_mul_of_nonneg_left (hdiag i).2 (sq_nonneg (z i))
      nlinarith [sq_abs (z i), sq_abs (B i i)]
    _ ≤ (3 / 2 : ℝ) * (∑ i, (z i) ^ 2) + h / 2 := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div]
      have hsum := (diagonal_sq_sum_le_hsSq B).trans hB
      linarith

theorem kernel_diagonal_retention (E F : Matrix ι ι ℝ) (d : ι → ℝ)
    {h c : ℝ} (hc : 0 ≤ c) (hd : ∀ i, d i ≤ c)
    (hE : hsSq E ≤ h) (hF : hsSq F ≤ 4 * h) :
    (∑ i, d i) - c * (5 * h) ≤
      realTrace (Matrix.diagonal d * (kernelProjection E F).toBlocks₂₂) := by
  let P := kernelProjection E F
  have hcap : Matrix.diagonal d ≤ c • (1 : Matrix ι ι ℝ) := by
    apply Matrix.le_iff.mpr
    rw [← Matrix.diagonal_one, ← Matrix.diagonal_smul, Matrix.diagonal_sub]
    exact Matrix.posSemidef_diagonal_iff.mpr (fun i => by simpa using sub_nonneg.mpr (hd i))
  have ht := realTrace_mul_mono (bottom_defect_posSemidef E F) hcap
  rw [realTrace_mul_comm (1 - P.toBlocks₂₂), Matrix.mul_smul, Matrix.mul_one,
    realTrace_smul, Matrix.mul_sub, Matrix.mul_one, realTrace_sub] at ht
  have hproj := (kernel_projection_block_estimates E F).2.1
  have htracebound : realTrace (1 - P.toBlocks₂₂) ≤ 5 * h := hproj.trans (by linarith)
  have hmul := mul_le_mul_of_nonneg_left htracebound hc
  have htrace : realTrace (Matrix.diagonal d) = ∑ i, d i := by simp [realTrace]
  rw [htrace] at ht
  linarith

def higherAveraged (E F : Matrix ι ι ℝ) (d z : ι → ℝ)
    (H : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) (β u : ℝ) : ℝ :=
  -realTrace (Matrix.diagonal d * (kernelProjection E F).toBlocks₂₂) -
    (2 / u) * realTrace (Matrix.diagonal (fun i => (z i) ^ 2) *
      (kernelProjection E F).toBlocks₂₂) +
    realTrace (H * kernelProjection E F) / (β * u) -
    realTrace (Matrix.diagonal z * (kernelProjection E F).toBlocks₁₂) / u

theorem higher_averaged_bound (E B : Matrix ι ι ℝ) (d z : ι → ℝ)
    (H : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) {h L β u : ℝ}
    (hh : 0 ≤ h) (hL : 0 ≤ L) (hβ : 0 < β) (hu : 0 < u)
    (hd : ∀ i, d i ≤ L / u) (hsum : ∑ i, d i = h)
    (hz : ∀ i, |z i| ≤ 1)
    (hE : hsSq E ≤ h) (hB : hsSq B ≤ h)
    (hF : hsSq (B - E * Matrix.diagonal z) ≤ 4 * h)
    (hdiag : ∀ i, 0 ≤ E i i ∧ E i i ≤ 1)
    (hH : H.PosSemidef) (htrace : realTrace H ≤ 5 * h) :
    higherAveraged E (B - E * Matrix.diagonal z) d z H β u ≤
      -(1 - (5 * L + 5 / β + 10 + 1 / 2 + 3 * Real.sqrt 5) / u) * h -
        (∑ i, (z i) ^ 2) / (2 * u) := by
  let F := B - E * Matrix.diagonal z
  let az := ∑ i, (z i) ^ 2
  have hdir := kernel_diagonal_retention E F d (div_nonneg hL hu.le) hd hE hF
  rw [hsum] at hdir
  have hzsq : ∀ i, (z i) ^ 2 ≤ 1 := by
    intro i
    nlinarith [hz i, sq_abs (z i), abs_nonneg (z i)]
  have howner := kernel_diagonal_retention E F (fun i => (z i) ^ 2)
    (by norm_num : (0 : ℝ) ≤ 1) hzsq hE hF
  have hresp := kernel_response_bound E F hH htrace
  have hmix := (kernel_mixed_bound_with_baseline E F z hz hh hE hF).trans
    (add_le_add_right (two_frame_mixed_baseline E B z hdiag hB) _)
  have hmneg := neg_le_of_abs_le hmix
  have hupper :
      higherAveraged E F d z H β u ≤
        -(h - (L / u) * (5 * h)) -
          (2 / u) * (az - 5 * h) +
          (5 * h) / (β * u) +
          ((3 / 2 : ℝ) * az + h / 2 + 3 * Real.sqrt 5 * h) / u := by
    unfold higherAveraged
    have ho := mul_le_mul_of_nonneg_left howner (by positivity : 0 ≤ 2 / u)
    have hr := div_le_div_of_nonneg_right hresp (mul_pos hβ hu).le
    have hm := div_le_div_of_nonneg_right hmneg hu.le
    dsimp [az] at *
    simp only [one_mul, neg_div] at *
    linarith
  apply hupper.trans_eq
  dsimp [az]
  field_simp
  ring

theorem higher_averaged_negative (E B : Matrix ι ι ℝ) (d z : ι → ℝ)
    (H : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) {h L β : ℝ}
    (hh : 0 < h) (hL : 0 ≤ L) (hβ : 0 < β) (hβhalf : β ≤ 1 / 2)
    (hLcap : L ≤ 1 / (2 * β))
    (hd : ∀ i, d i ≤ L / (100 / β)) (hsum : ∑ i, d i = h)
    (hz : ∀ i, |z i| ≤ 1)
    (hE : hsSq E ≤ h) (hB : hsSq B ≤ h)
    (hF : hsSq (B - E * Matrix.diagonal z) ≤ 4 * h)
    (hdiag : ∀ i, 0 ≤ E i i ∧ E i i ≤ 1)
    (hH : H.PosSemidef) (htrace : realTrace H ≤ 5 * h) :
    higherAveraged E (B - E * Matrix.diagonal z) d z H β (100 / β) < 0 := by
  have hu : 0 < 100 / β := div_pos (by norm_num) hβ
  have hbound := higher_averaged_bound E B d z H hh.le hL hβ hu
    hd hsum hz hE hB hF hdiag hH htrace
  have hsqrt : Real.sqrt 5 ≤ 3 :=
    (Real.sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hLmul : L * (2 * β) ≤ 1 := (le_div_iff₀ (by positivity)).mp hLcap
  have hc : (5 * L + 5 / β + 10 + 1 / 2 + 3 * Real.sqrt 5) / (100 / β) < 1 := by
    apply (div_lt_one hu).mpr
    apply (lt_div_iff₀ hβ).mpr
    have hid : 5 / β * β = 5 := div_mul_cancel₀ _ hβ.ne'
    nlinarith [mul_le_mul_of_nonneg_left hsqrt hβ.le]
  have ha : 0 ≤ (∑ i, (z i) ^ 2) / (2 * (100 / β)) := by positivity
  exact hbound.trans_lt (by nlinarith)

theorem higherAveraged_eq_averagedUpper (E F : Matrix ι ι ℝ) (d z : ι → ℝ)
    (H : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) (β u : ℝ) :
    higherAveraged E F d z H β u =
      averagedUpper E F (fun i => d i + (2 / u) * (z i) ^ 2) z ((1 / β) • H) u := by
  have hd : Matrix.diagonal (fun i => d i + (2 / u) * (z i) ^ 2) =
      Matrix.diagonal d + (2 / u) • Matrix.diagonal (fun i => (z i) ^ 2) := by
    rw [← Matrix.diagonal_smul, ← Matrix.diagonal_add]
    rfl
  simp only [higherAveraged, averagedUpper, hd, Matrix.add_mul, Matrix.smul_mul,
    realTrace_add, realTrace_smul]
  ring

/-- A negative higher-rank average supplies a legal pair with a nonzero
physical component. The response matrix is the same positive quadratic
form used in the averaged bound. -/
theorem exists_negative_legal_pair (E F : Matrix ι ι ℝ) (d z : ι → ℝ)
    {H : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ} (hH : H.PosSemidef)
    {β u : ℝ} (hβ : 0 < β) (hu : 0 < u)
    (hneg : higherAveraged E F d z H β u < 0) :
    ∃ x : ι ⊕ ι → ℝ,
      constraintMatrix E F *ᵥ x = 0 ∧ x ∘ Sum.inr ≠ 0 ∧
      -(x ∘ Sum.inr) ⬝ᵥ (Matrix.diagonal d *ᵥ (x ∘ Sum.inr)) -
        (2 / u) * ((x ∘ Sum.inr) ⬝ᵥ
          (Matrix.diagonal (fun i => (z i) ^ 2) *ᵥ (x ∘ Sum.inr))) +
        (x ⬝ᵥ (H *ᵥ x)) / (β * u) -
        ((x ∘ Sum.inl) ⬝ᵥ (Matrix.diagonal z *ᵥ (x ∘ Sum.inr))) / u < 0 := by
  rw [higherAveraged_eq_averagedUpper] at hneg
  obtain ⟨x, hx, hqx⟩ := exists_negative_kernel_direction E F
    (fun i => d i + (2 / u) * (z i) ^ 2) z ((1 / β) • H) u hneg
  have hscaled : ((1 / β) • H).PosSemidef := hH.smul (by positivity : 0 ≤ 1 / β)
  refine ⟨x, hx, negative_kernel_bottom_ne_zero _ _ hscaled hu hqx, ?_⟩
  rw [upperMatrix_quadratic] at hqx
  have hd : Matrix.diagonal (fun i => d i + (2 / u) * (z i) ^ 2) =
      Matrix.diagonal d + (2 / u) • Matrix.diagonal (fun i => (z i) ^ 2) := by
    rw [← Matrix.diagonal_smul, ← Matrix.diagonal_add]
    rfl
  rw [hd, Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add, dotProduct_smul,
    Matrix.smul_mulVec, dotProduct_smul] at hqx
  simp only [smul_eq_mul, neg_dotProduct] at hqx ⊢
  convert hqx using 1
  ring

end HigherRankKS.ProjectionAveraging
