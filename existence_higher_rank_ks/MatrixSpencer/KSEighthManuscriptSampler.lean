import MatrixSpencer.KSEighthManuscriptLDL
import MatrixSpencer.KSSymmetricProgress



open Matrix
open scoped BigOperators MatrixOrder
noncomputable section
namespace MatrixSpencer.KSEighthManuscriptSampler

variable {d : ℕ}

def weight (_ : Fin d × Bool) : ℝ := 1 / (2 * (d : ℝ))

def unsigned (P : Matrix (Fin d) (Fin d) ℝ) (j : Fin d) : EuclideanSpace ℝ (Fin d) :=
  Real.sqrt ((d : ℝ) * KSEighthManuscriptLDL.pivot P j) • WithLp.toLp 2 (KSEighthManuscriptLDL.lowerColumn P j)

def increment (P : Matrix (Fin d) (Fin d) ℝ) (s : Fin d × Bool) : EuclideanSpace ℝ (Fin d) :=
  if s.2 then unsigned P s.1 else -unsigned P s.1

theorem weight_pos (hd : 0 < d) (s : Fin d × Bool) : 0 < weight s := by
  unfold weight
  positivity

theorem weight_sum (hd : 0 < d) : (∑ s : Fin d × Bool, weight s) = 1 := by
  simp only [weight, Finset.sum_const, Finset.card_univ, Fintype.card_prod,
    Fintype.card_fin, Fintype.card_bool, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  field_simp

theorem mean_zero (P : Matrix (Fin d) (Fin d) ℝ) :
    (∑ s, weight s • increment P s) = 0 := by
  rw [Fintype.sum_prod_type]
  simp [weight, increment]

theorem unsigned_eq (P : Matrix (Fin d) (Fin d) ℝ) (j : Fin d) :
    unsigned P j = Real.sqrt (d : ℝ) • WithLp.toLp 2 (KSEighthManuscriptLDL.factorColumn P j) := by
  simp only [unsigned, KSEighthManuscriptLDL.factorColumn, Real.sqrt_mul (Nat.cast_nonneg d),
    WithLp.toLp_smul, smul_smul]

theorem unsigned_outer {P : Matrix (Fin d) (Fin d) ℝ} (hP : P.PosSemidef) (j : Fin d) :
    realRankOne (WithLp.ofLp (unsigned P j)) = (d : ℝ) • KSEighthManuscriptLDL.term P j := by
  rw [unsigned_eq, WithLp.ofLp_smul, WithLp.ofLp_toLp, realRankOne_smul,
    Real.sq_sqrt (Nat.cast_nonneg d)]
  congr 1
  exact KSEighthManuscriptLDL.factorColumn_outer hP j

theorem increment_outer {P : Matrix (Fin d) (Fin d) ℝ} (hP : P.PosSemidef)
    (s : Fin d × Bool) :
    realRankOne (WithLp.ofLp (increment P s)) = (d : ℝ) • KSEighthManuscriptLDL.term P s.1 := by
  unfold increment
  split
  · exact unsigned_outer hP _
  · rw [WithLp.ofLp_neg, realRankOne_neg, unsigned_outer hP]

/-- The sampled covariance is exactly the input, including its zero eigenspace. -/
theorem covariance {P : Matrix (Fin d) (Fin d) ℝ} (hP : P.PosSemidef) (hd : 0 < d) :
    (∑ s, weight s • realRankOne (WithLp.ofLp (increment P s))) = P := by
  rw [Fintype.sum_prod_type]
  simp only [increment_outer hP, weight, Fintype.sum_bool, smul_smul, ← add_smul]
  have hcoef : 1 / (2 * (d : ℝ)) * d + 1 / (2 * (d : ℝ)) * d = 1 := by
    have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
    field_simp
    norm_num
  simp only [hcoef, one_smul]
  exact KSEighthManuscriptLDL.sum_terms hP

theorem quadratic_mean {P : Matrix (Fin d) (Fin d) ℝ} (hP : P.PosSemidef)
    (hd : 0 < d) (G : Matrix (Fin d) (Fin d) ℝ) :
    (∑ s, weight s * (WithLp.ofLp (increment P s) ⬝ᵥ
      (G *ᵥ WithLp.ofLp (increment P s)))) = realTrace (P * G) := by
  conv_rhs => rw [← covariance hP hd]
  rw [Matrix.sum_mul, realTrace_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [Matrix.smul_mul, realTrace_smul, realTrace_rankOne_mul]

theorem factorColumn_norm_le_one {P : Matrix (Fin d) (Fin d) ℝ}
    (hP : P.PosSemidef) (hP1 : P ≤ 1) (j : Fin d) :
    ‖(WithLp.toLp 2 (KSEighthManuscriptLDL.factorColumn P j) : EuclideanSpace ℝ (Fin d))‖ ≤ 1 := by
  let u := KSEighthManuscriptLDL.factorColumn P j
  have ht := (KSEighthManuscriptLDL.term_le hP j).trans hP1
  have h := (Matrix.le_iff.mp ht).2 u
  have he : KSEighthManuscriptLDL.term P j = realRankOne u := (KSEighthManuscriptLDL.factorColumn_outer hP j).symm
  rw [he] at h
  simp only [star_trivial, Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec,
    realRankOne_pairing] at h
  have hn : u ⬝ᵥ u = ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin d))‖^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    change (∑ i, u i * u i) = ∑ i, |u i|^2
    simp only [sq_abs]
    simp only [pow_two]
  rw [hn] at h
  change ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin d))‖ ≤ 1
  have hs : ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin d))‖^2 ≤ 1 := by
    nlinarith [sq_nonneg (‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin d))‖^2 - 1)]
  nlinarith [norm_nonneg (WithLp.toLp 2 u : EuclideanSpace ℝ (Fin d))]

/-- Every branch has length at most `sqrt d`, even a zero-weight LDL term. -/
theorem increment_norm_le {P : Matrix (Fin d) (Fin d) ℝ}
    (hP : P.PosSemidef) (hP1 : P ≤ 1) (s : Fin d × Bool) :
    ‖increment P s‖ ≤ Real.sqrt (d : ℝ) := by
  have hu : ‖unsigned P s.1‖ ≤ Real.sqrt (d : ℝ) := by
    rw [unsigned_eq, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (factorColumn_norm_le_one hP hP1 s.1) (Real.sqrt_nonneg (d : ℝ))
  unfold increment
  split
  · exact hu
  · simpa only [norm_neg] using hu

theorem factorColumn_zero_row {P : Matrix (Fin d) (Fin d) ℝ}
    (hP : P.PosSemidef) (i : Fin d) (hi : P i i = 0) (j : Fin d) :
    KSEighthManuscriptLDL.factorColumn P j i = 0 := by
  have h := (Matrix.le_iff.mp (KSEighthManuscriptLDL.term_le hP j)).2 (Pi.single i 1)
  rw [← KSEighthManuscriptLDL.factorColumn_outer hP j] at h
  simp only [Matrix.sub_mulVec, dotProduct_sub, star_trivial, Matrix.mulVec_single_one,
    single_dotProduct, one_mul, Matrix.vecMulVec_apply] at h
  change 0 ≤ P i i - KSEighthManuscriptLDL.factorColumn P j i * KSEighthManuscriptLDL.factorColumn P j i at h
  rw [hi] at h
  nlinarith [sq_nonneg (KSEighthManuscriptLDL.factorColumn P j i)]

/-- An original zero covariance row cannot move on any draw. -/
theorem increment_zero_row {P : Matrix (Fin d) (Fin d) ℝ}
    (hP : P.PosSemidef) (i : Fin d) (hi : P i i = 0) (s : Fin d × Bool) :
    increment P s i = 0 := by
  have hu : unsigned P s.1 i = 0 := by
    rw [unsigned_eq]
    change Real.sqrt (d : ℝ) * KSEighthManuscriptLDL.factorColumn P s.1 i = 0
    rw [factorColumn_zero_row hP i hi, mul_zero]
  unfold increment
  split
  · exact hu
  · simpa only [PiLp.neg_apply, hu, neg_zero]

/-- Exact conditional squared-norm progress of the actual arithmetic sampler. -/
theorem mean_norm_sq {P : Matrix (Fin d) (Fin d) ℝ} (hP : P.PosSemidef) (hd : 0 < d)
    (x : EuclideanSpace ℝ (Fin d)) (h : ℝ) :
    (∑ s, weight s * ‖x + h • increment P s‖^2) = ‖x‖^2 + h^2 * realTrace P :=
  KSSymmetricProgress.finite_covariance_mean_norm_sq weight (increment P) x h P
    (weight_sum hd) (mean_zero P) (covariance hP hd)


theorem eighth_progress (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : Q.PosSemidef)
    (hd : 0 < d) (x : EuclideanSpace ℝ (Fin d)) (hx : ∀ i, |x i| ≤ 1/8)
    (htrace : 3 * (d : ℝ) / 4 ≤ realTrace Q) (h : ℝ) :
    ‖x‖^2 + h^2/2 ≤ ∑ s, weight s * ‖x + h •
      increment (KSSymmetricProgress.scaledCovariance (WithLp.ofLp x) Q) s‖^2 := by
  rw [mean_norm_sq (KSSymmetricProgress.scaledCovariance_posSemidef _ hQ) hd]
  have ht := KSSymmetricProgress.eighth_scaledCovariance_trace_lower (WithLp.ofLp x)
    hQ hx (by simpa using hd) (by simpa using htrace)
  nlinarith [mul_le_mul_of_nonneg_left ht (sq_nonneg h)]

end MatrixSpencer.KSEighthManuscriptSampler
