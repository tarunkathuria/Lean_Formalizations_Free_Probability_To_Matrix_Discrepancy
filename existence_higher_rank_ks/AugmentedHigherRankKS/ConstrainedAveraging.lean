import AugmentedHigherRankKS.ConstrainedProjection
import MatrixSpencer.KSSpinDrift

/-! Finite projection averaging with an additional scalar movement constraint.
These are matrix inequalities, independent of the particular source model. -/

open Matrix MatrixSpencer MatrixSpencer.KSWeightedProjection
open scoped BigOperators MatrixOrder

noncomputable section
namespace AugmentedHigherRankKS.ConstrainedAveraging
open ConstrainedProjection

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem bottom_defect_posSemidef (E F : Matrix ι ι ℝ) (z : ι → ℝ) :
    (1 - (projection E F z).toBlocks₂₂).PosSemidef := by
  have h := ((isStarProjection E F z).one_sub.nonneg).posSemidef
  have hs := h.submatrix Sum.inr
  convert hs using 1
  ext i j
  simp [Matrix.toBlocks₂₂, Matrix.submatrix, Matrix.one_apply]

theorem debit_survives (E F : Matrix ι ι ℝ) (z d : ι → ℝ) {h : ℝ}
    (hh : 1 / 4 ≤ h) (hd : ∀ i, d i ≤ 1 / 48) (hsum : ∑ i, d i = h)
    (hE : hsSq E ≤ 4 * h) (hF : hsSq F ≤ 16 * h) :
    h / 2 ≤ realTrace (Matrix.diagonal d * (projection E F z).toBlocks₂₂) := by
  let P := projection E F z
  have hcap : Matrix.diagonal d ≤ (1 / 48 : ℝ) • (1 : Matrix ι ι ℝ) := by
    apply Matrix.le_iff.mpr
    rw [← Matrix.diagonal_one, ← Matrix.diagonal_smul, Matrix.diagonal_sub]
    exact Matrix.posSemidef_diagonal_iff.mpr (fun i => by simpa using sub_nonneg.mpr (hd i))
  have ht := realTrace_mul_mono (bottom_defect_posSemidef E F z) hcap
  rw [realTrace_mul_comm (1 - P.toBlocks₂₂), Matrix.mul_smul, Matrix.mul_one,
    realTrace_smul, Matrix.mul_sub, Matrix.mul_one, realTrace_sub] at ht
  have htrace : realTrace (Matrix.diagonal d) = h := by
    simpa [realTrace] using hsum
  rw [htrace] at ht
  have hproj := (block_estimates E F z).2.1
  linarith

theorem response_contracts (E F : Matrix ι ι ℝ) (z : ι → ℝ)
    {H : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ} (hH : H.PosSemidef)
    {h : ℝ} (htrace : realTrace H ≤ 20 * h) :
    realTrace (H * projection E F z) ≤ 20 * h := by
  have hb := realTrace_mul_mono hH (isStarProjection E F z).le_one
  rw [Matrix.mul_one] at hb
  exact hb.trans htrace

def debitMatrix (d : ι → ℝ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ :=
  Matrix.fromBlocks 0 0 0 (Matrix.diagonal d)

def upperMatrix (d : ι → ℝ) (H : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ)
    (σ a : ℝ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ := (1 / σ) • H - a • debitMatrix d

theorem debit_trace (d : ι → ℝ) (P : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) :
    realTrace (debitMatrix d * P) = realTrace (Matrix.diagonal d * P.toBlocks₂₂) := by
  conv_lhs => arg 1; arg 2; rw [← Matrix.fromBlocks_toBlocks P]
  simp [debitMatrix, Matrix.fromBlocks_multiply, realTrace_fromBlocks]

theorem averaged_gap (E F : Matrix ι ι ℝ) (z d : ι → ℝ)
    {H : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ} {h β σ a : ℝ}
    (hh : 1 / 4 ≤ h) (hd : ∀ i, d i ≤ 1 / 48) (hsum : ∑ i, d i = h)
    (hE : hsSq E ≤ 4 * h) (hF : hsSq F ≤ 16 * h)
    (hH : H.PosSemidef) (htrace : realTrace H ≤ 20 * h)
    (hβ : 0 < β) (hσ : 4 * β / 3 ≤ σ) (ha : 60 / β ≤ a) :
    realTrace (upperMatrix d H σ a * projection E F z) ≤ -a * h / 4 := by
  have hσpos : 0 < σ := lt_of_lt_of_le (by positivity) hσ
  have hapos : 0 < a := lt_of_lt_of_le (by positivity) ha
  have hdebit := debit_survives E F z d hh hd hsum hE hF
  have hresp := response_contracts E F z hH htrace
  have hab : 60 ≤ a * β := (div_le_iff₀ hβ).mp ha
  have has : 80 ≤ a * σ := by nlinarith [mul_le_mul_of_nonneg_left hσ hapos.le]
  have hpay : 20 / σ ≤ a / 4 := (div_le_iff₀ hσpos).mpr (by nlinarith)
  have hpayh := mul_le_mul_of_nonneg_right hpay (by linarith : 0 ≤ h)
  have hr := mul_le_mul_of_nonneg_left hresp (by positivity : 0 ≤ 1 / σ)
  have hd' := mul_le_mul_of_nonneg_left hdebit hapos.le
  rw [upperMatrix, Matrix.sub_mul, Matrix.smul_mul, Matrix.smul_mul,
    realTrace_sub, realTrace_smul, realTrace_smul, debit_trace]
  ring_nf at hpayh hr hd' ⊢
  linarith

theorem upper_quadratic (d : ι → ℝ) (H : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ)
    (σ a : ℝ) (x : ι ⊕ ι → ℝ) :
    x ⬝ᵥ (upperMatrix d H σ a *ᵥ x) =
      (x ⬝ᵥ (H *ᵥ x)) / σ - a *
        ((x ∘ Sum.inr) ⬝ᵥ (Matrix.diagonal d *ᵥ (x ∘ Sum.inr))) := by
  rw [upperMatrix, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
    dotProduct_sub, dotProduct_smul, dotProduct_smul]
  simp only [debitMatrix, Matrix.fromBlocks_mulVec, Matrix.zero_mulVec, zero_add,
    Matrix.dotProduct_block, Function.comp_def, Sum.elim_inl, Sum.elim_inr,
    dotProduct_zero, zero_add, smul_eq_mul]
  ring

theorem exists_negative_legal (E F : Matrix ι ι ℝ) (z d : ι → ℝ)
    {H : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ} {h β σ a : ℝ}
    (hh : 1 / 4 ≤ h) (hd : ∀ i, d i ≤ 1 / 48) (hsum : ∑ i, d i = h)
    (hE : hsSq E ≤ 4 * h) (hF : hsSq F ≤ 16 * h)
    (hH : H.PosSemidef) (htrace : realTrace H ≤ 20 * h)
    (hβ : 0 < β) (hσ : 4 * β / 3 ≤ σ) (ha : 60 / β ≤ a) :
    ∃ x : ι ⊕ ι → ℝ,
      constraintMatrix E F *ᵥ x = 0 ∧
      (∑ i, z i * x (Sum.inr i)) = 0 ∧
      x ∘ Sum.inr ≠ 0 ∧ x ⬝ᵥ (upperMatrix d H σ a *ᵥ x) < 0 := by
  have hσpos : 0 < σ := lt_of_lt_of_le (by positivity) hσ
  have hapos : 0 < a := lt_of_lt_of_le (by positivity) ha
  have hneg := averaged_gap E F z d hh hd hsum hE hF hH htrace hβ hσ ha
  have hstrict : realTrace (upperMatrix d H σ a * projection E F z) < 0 :=
    hneg.trans_lt (by nlinarith)
  have hsumq := KSSpinDrift.projection_quadratic_sum (projection E F z)
    (upperMatrix d H σ a) (isStarProjection E F z)
  have hex : ∃ j, (projection E F z *ᵥ Pi.single j 1) ⬝ᵥ
      (upperMatrix d H σ a *ᵥ (projection E F z *ᵥ Pi.single j 1)) < 0 := by
    by_contra hn
    have hp : 0 ≤ ∑ j, (projection E F z *ᵥ Pi.single j 1) ⬝ᵥ
        (upperMatrix d H σ a *ᵥ (projection E F z *ᵥ Pi.single j 1)) := by
      apply Finset.sum_nonneg
      intro j _
      exact le_of_not_gt (fun hj => hn ⟨j, hj⟩)
    rw [hsumq] at hp
    linarith
  obtain ⟨j, hj⟩ := hex
  let x := projection E F z *ᵥ Pi.single j 1
  have hc : constraint E F z *ᵥ x = 0 := by
    rw [Matrix.mulVec_mulVec, constraint_mul, Matrix.zero_mulVec]
  refine ⟨x, ?_, ?_, ?_, hj⟩
  · funext i
    have he := congrFun hc (Sum.inl i)
    simpa [Matrix.mulVec, dotProduct, constraint] using he
  · have he := congrFun hc (Sum.inr ())
    simpa [Matrix.mulVec, dotProduct, constraint, Fintype.sum_sum_type] using he
  · intro hv
    have hq := hH.2 x
    simp only [star_trivial] at hq
    have he := upper_quadratic d H σ a x
    rw [hv] at he
    simp only [Matrix.mulVec_zero, dotProduct_zero, mul_zero, sub_zero] at he
    change x ⬝ᵥ (upperMatrix d H σ a *ᵥ x) < 0 at hj
    rw [he] at hj
    exact (not_lt_of_ge (div_nonneg hq hσpos.le)) hj

theorem hsSq_ge_one_of_fixed {E : Matrix ι ι ℝ} {v : ι → ℝ}
    (hv : v ≠ 0) (hfix : E *ᵥ v = v) : 1 ≤ hsSq E := by
  have hsum : 0 < ∑ i, v i ^ 2 := by
    apply Finset.sum_pos'
    · intro i _; positivity
    · obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
      exact ⟨i, Finset.mem_univ _, sq_pos_of_ne_zero hi⟩
  have hcs : ∑ i, (∑ j, E i j * v j) ^ 2 ≤
      (∑ i, ∑ j, E i j ^ 2) * ∑ j, v j ^ 2 := by
    calc
      _ ≤ ∑ i, (∑ j, E i j ^ 2) * ∑ j, v j ^ 2 :=
        Finset.sum_le_sum (fun i _ => Finset.sum_mul_sq_le_sq_mul_sq _ _ _)
      _ = _ := by rw [Finset.sum_mul]
  have he : (∑ i, (∑ j, E i j * v j) ^ 2) = ∑ i, v i ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    rw [← congrFun hfix i]
    rfl
  rw [he] at hcs
  have hh : (∑ i, ∑ j, E i j ^ 2) = hsSq E := by
    rw [KSSpinDrift.hsSq_eq_sum, Finset.sum_comm]
  rw [hh] at hcs
  nlinarith

theorem weighted_transpose_hsSq_ge_one (R : ι → ℝ) (hR : ∀ i, 0 < R i)
    (T : Matrix ι ι ℝ) {μ : ι → ℝ} (hμ : μ ≠ 0) (hfix : T *ᵥ μ = μ) :
    1 ≤ hsSq (KSSpinDrift.weightedConjugate R Tᵀ) := by
  let W : Matrix ι ι ℝ := Matrix.diagonal (fun i => Real.sqrt (R i))
  let V : Matrix ι ι ℝ := Matrix.diagonal (fun i => (Real.sqrt (R i))⁻¹)
  have hwv : W * V = 1 := by
    change Matrix.diagonal (fun i => Real.sqrt (R i)) *
      Matrix.diagonal (fun i => (Real.sqrt (R i))⁻¹) = 1
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact mul_inv_cancel₀ (Real.sqrt_pos.mpr (hR i)).ne'
  have ht : (KSSpinDrift.weightedConjugate R Tᵀ)ᵀ = V * T * W := by
    simp only [KSSpinDrift.weightedConjugate, Matrix.transpose_mul,
      Matrix.diagonal_transpose, Matrix.transpose_transpose]
    exact (Matrix.mul_assoc _ _ _).symm
  have hv : (KSSpinDrift.weightedConjugate R Tᵀ)ᵀ *ᵥ
      KSSpinDrift.unwhiten R μ = KSSpinDrift.unwhiten R μ := by
    rw [ht]
    change (V * T * W) *ᵥ (V *ᵥ μ) = V *ᵥ μ
    rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, hwv,
      Matrix.mul_one, ← Matrix.mulVec_mulVec, hfix]
  simpa only [hsSq_transpose] using
    hsSq_ge_one_of_fixed (KSSpinDrift.unwhiten_ne_zero R hR hμ) hv

end AugmentedHigherRankKS.ConstrainedAveraging
