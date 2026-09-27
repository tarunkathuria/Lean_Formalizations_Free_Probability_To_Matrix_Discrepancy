import MatrixSpencer.DyadicTraceInterpolation
import MatrixSpencer.WeightedKraus

/-!
# Fisher bounds for the actual positive balanced atoms

The atoms are complex positive semidefinite matrices, and all coefficient spaces
are real.  The proof works for rank one and rank two, without replacing the
physical weighted trace by an abstract quadratic form.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder
open Matrix

noncomputable section

set_option maxHeartbeats 800000

namespace MatrixSpencer.KSFisher

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]

/-- The physical synthesis map on real coefficient vectors. -/
def synthesis (D : ι → Matrix n n ℂ) (x : ι → ℝ) : Matrix n n ℂ :=
  ∑ i, x i • D i

/-- Its real Hilbert--Schmidt Gram. -/
def gram (D : ι → Matrix n n ℂ) : Matrix ι ι ℝ :=
  fun i j => realTrace (D i * D j)

theorem synthesis_isHermitian (D : ι → Matrix n n ℂ)
    (hD : ∀ i, (D i).IsHermitian) (x : ι → ℝ) :
    (synthesis D x).IsHermitian := by
  simp only [synthesis, Matrix.IsHermitian, Matrix.conjTranspose_sum,
    Matrix.conjTranspose_smul, star_trivial, (hD _).eq]

/-- Cauchy--Schwarz summed against the actual fixed-point decomposition of P.
No rank assumption and no commutation between P and Y is required. -/
theorem weighted_trace_fisher (D : ι → Matrix n n ℂ)
    (hD : ∀ i, (D i).PosSemidef) (m : ι → ℝ) (hm : ∀ i, 0 ≤ m i)
    (hr : ∀ i, 0 < realTrace (D i)) {P Y : Matrix n n ℂ}
    (hP : P = ∑ i, m i • D i) (hY : Y.IsHermitian) :
    (∑ i, (m i / realTrace (D i)) * realTrace (D i * Y) ^ 2) ≤
      realTrace (P * (Y * Y)) := by
  calc
    _ ≤ ∑ i, m i * realTrace (D i * (Y * Y)) := by
      apply Finset.sum_le_sum
      intro i _
      have h := mul_le_mul_of_nonneg_left
        (DyadicTraceInterpolation.weightedTrace_sq_le (hD i) hY)
        (div_nonneg (hm i) (hr i).le)
      have he : (m i / realTrace (D i)) *
          (realTrace (D i) * realTrace (D i * (Y * Y))) =
          m i * realTrace (D i * (Y * Y)) := by
        field_simp [(hr i).ne']
      rwa [he] at h
    _ = _ := by
      rw [hP]
      simp only [Matrix.sum_mul, Matrix.smul_mul, realTrace_sum, realTrace_smul]

theorem gram_mulVec (D : ι → Matrix n n ℂ) (x : ι → ℝ) (i : ι) :
    (gram D *ᵥ x) i = realTrace (D i * synthesis D x) := by
  simp only [gram, Matrix.mulVec, dotProduct, synthesis, Matrix.mul_sum,
    Matrix.mul_smul, realTrace_sum, realTrace_smul]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The weighted physical Gram is exactly the squared synthesis energy. -/
theorem physicalGram_quadratic (P : Matrix n n ℂ)
    (D : ι → Matrix n n ℂ) (x : ι → ℝ) :
    x ⬝ᵥ (physicalRealGram P D *ᵥ x) =
      realTrace (P * (synthesis D x * synthesis D x)) := by
  change (∑ i, x i * ∑ j, realTrace (P * D i * D j) * x j) = _
  simp only [synthesis,
    Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul,
    realTrace_sum, realTrace_smul, Finset.mul_sum, Matrix.mul_assoc]
  rw [Finset.sum_comm (f := fun i j => x i * (x j * realTrace (P * (D j * D i))))]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem gram_isHermitian (D : ι → Matrix n n ℂ) :
    (gram D).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, star_trivial, gram]
  exact realTrace_mul_comm _ _

theorem physicalGram_isHermitian {P : Matrix n n ℂ} (hP : P.IsHermitian)
    (D : ι → Matrix n n ℂ) (hD : ∀ i, (D i).IsHermitian) :
    (physicalRealGram P D).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, star_trivial, physicalRealGram]
  change realTrace (P * D j * D i) = realTrace (P * D i * D j)
  calc
    _ = realTrace ((D j * D i) * P) := by
      simpa only [Matrix.mul_assoc] using realTrace_mul_comm P (D j * D i)
    _ = realTrace ((P * D i * D j)ᴴ) := by
      simp only [Matrix.conjTranspose_mul, hP.eq, (hD i).eq, (hD j).eq,
        Matrix.mul_assoc]
    _ = _ := by
      unfold realTrace
      rw [Matrix.trace_conjTranspose]
      rfl

theorem physicalGram_posSemidef {P : Matrix n n ℂ} (hP : P.PosSemidef)
    (D : ι → Matrix n n ℂ) (hD : ∀ i, (D i).IsHermitian) :
    (physicalRealGram P D).PosSemidef := by
  refine ⟨physicalGram_isHermitian hP.isHermitian D hD, fun x => ?_⟩
  simp only [star_trivial]
  rw [physicalGram_quadratic]
  apply realTrace_mul_nonneg hP
  simpa only [(synthesis_isHermitian D hD x).eq] using
    Matrix.posSemidef_conjTranspose_mul_self (synthesis D x)

variable [DecidableEq ι]

/-- The diagonal weighted sandwich is a sum of scalar squares. -/
theorem diagonal_sandwich_quadratic (T : Matrix ι ι ℝ) (r x : ι → ℝ) :
    x ⬝ᵥ ((Tᵀ * Matrix.diagonal r * T) *ᵥ x) =
      ∑ i, r i * (T *ᵥ x) i ^ 2 := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dotProduct_mulVec]
  simp only [vecMul_transpose, Matrix.mulVec_diagonal, dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The genuine coefficient matrix Fisher inequality T R T ≤ Γ. -/
theorem gram_fisher (D : ι → Matrix n n ℂ)
    (hD : ∀ i, (D i).PosSemidef) (m : ι → ℝ) (hm : ∀ i, 0 ≤ m i)
    (hr : ∀ i, 0 < realTrace (D i)) {P : Matrix n n ℂ}
    (hP : P = ∑ i, m i • D i) :
    gram D * Matrix.diagonal (fun i => m i / realTrace (D i)) * gram D ≤
      physicalRealGram P D := by
  have hPH : P.IsHermitian := by
    rw [hP]
    exact synthesis_isHermitian D (fun i => (hD i).isHermitian) m
  have hG := gram_isHermitian D
  apply Matrix.le_iff.mpr
  refine ⟨(physicalGram_isHermitian hPH D (fun i => (hD i).isHermitian)).sub ?_,
    fun x => ?_⟩
  · have hR : (Matrix.diagonal (fun i => m i / realTrace (D i))).IsHermitian := by
      exact Matrix.isHermitian_diagonal _
    simpa only [hG.eq] using Matrix.isHermitian_conjTranspose_mul_mul (gram D) hR
  · simp only [star_trivial, Matrix.sub_mulVec, dotProduct_sub, sub_nonneg]
    have ht : (gram D)ᵀ = gram D := by simpa only [Matrix.conjTranspose] using hG.eq
    have he := diagonal_sandwich_quadratic (gram D)
      (fun i => m i / realTrace (D i)) x
    rw [ht] at he
    rw [he, physicalGram_quadratic]
    simpa only [gram_mulVec] using weighted_trace_fisher D hD m hm hr hP
      (synthesis_isHermitian D (fun i => (hD i).isHermitian) x)

/-- The spin Gram, with the involution acting on the physical source space. -/
def spinGram (J : Matrix n n ℂ) (D : ι → Matrix n n ℂ) : Matrix ι ι ℝ :=
  fun i j => realTrace (D i * J * D j)

theorem spinGram_mulVec (J : Matrix n n ℂ) (D : ι → Matrix n n ℂ)
    (x : ι → ℝ) (i : ι) :
    (spinGram J D *ᵥ x) i = realTrace (D i * (J * synthesis D x)) := by
  simp only [spinGram, Matrix.mulVec, dotProduct, synthesis, Matrix.mul_sum,
    Matrix.mul_smul, realTrace_sum, realTrace_smul, ← Matrix.mul_assoc]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem spinGram_isHermitian {J : Matrix n n ℂ} (hJ : J.IsHermitian)
    (D : ι → Matrix n n ℂ) (hD : ∀ i, (D i).IsHermitian) :
    (spinGram J D).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, star_trivial, spinGram]
  calc
    _ = realTrace ((D i * J * D j)ᴴ) := by
      simp only [Matrix.conjTranspose_mul, hJ.eq, (hD i).eq, (hD j).eq,
        Matrix.mul_assoc]
    _ = _ := by
      unfold realTrace
      rw [Matrix.trace_conjTranspose]
      rfl

theorem spin_synthesis_isHermitian {J : Matrix n n ℂ} (hJ : J.IsHermitian)
    (D : ι → Matrix n n ℂ) (hD : ∀ i, (D i).IsHermitian)
    (hc : ∀ i, J * D i = D i * J) (x : ι → ℝ) :
    (J * synthesis D x).IsHermitian := by
  have hcomm : J * synthesis D x = synthesis D x * J := by
    simp only [synthesis, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul,
      Matrix.smul_mul, hc]
  rw [Matrix.IsHermitian, Matrix.conjTranspose_mul,
    (synthesis_isHermitian D hD x).eq, hJ.eq]
  exact hcomm.symm

theorem spin_synthesis_square {J : Matrix n n ℂ}
    (hJJ : J * J = 1) (D : ι → Matrix n n ℂ)
    (hc : ∀ i, J * D i = D i * J) (x : ι → ℝ) :
    (J * synthesis D x) * (J * synthesis D x) =
      synthesis D x * synthesis D x := by
  have hcomm : J * synthesis D x = synthesis D x * J := by
    simp only [synthesis, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul,
      Matrix.smul_mul, hc]
  calc
    _ = J * (synthesis D x * J) * synthesis D x := by noncomm_ring
    _ = J * (J * synthesis D x) * synthesis D x := by rw [← hcomm]
    _ = _ := by rw [← Matrix.mul_assoc J J, hJJ, Matrix.one_mul]

/-- The spin Fisher inequality in the full-cube proof, derived on the actual
commuting Hermitian source space. -/
theorem spin_gram_fisher (D : ι → Matrix n n ℂ)
    (hD : ∀ i, (D i).PosSemidef) (m : ι → ℝ) (hm : ∀ i, 0 ≤ m i)
    (hr : ∀ i, 0 < realTrace (D i)) {P J : Matrix n n ℂ}
    (hP : P = ∑ i, m i • D i) (hJ : J.IsHermitian)
    (hJJ : J * J = 1) (hc : ∀ i, J * D i = D i * J) :
    spinGram J D * Matrix.diagonal (fun i => m i / realTrace (D i)) *
      spinGram J D ≤ physicalRealGram P D := by
  have hPH : P.IsHermitian := by
    rw [hP]
    exact synthesis_isHermitian D (fun i => (hD i).isHermitian) m
  have hG := spinGram_isHermitian hJ D (fun i => (hD i).isHermitian)
  apply Matrix.le_iff.mpr
  refine ⟨(physicalGram_isHermitian hPH D (fun i => (hD i).isHermitian)).sub ?_,
    fun x => ?_⟩
  · simpa only [hG.eq] using Matrix.isHermitian_conjTranspose_mul_mul
      (spinGram J D) (Matrix.isHermitian_diagonal (fun i => m i / realTrace (D i)))
  · simp only [star_trivial, Matrix.sub_mulVec, dotProduct_sub, sub_nonneg]
    have ht : (spinGram J D)ᵀ = spinGram J D := by
      simpa only [Matrix.conjTranspose] using hG.eq
    have he := diagonal_sandwich_quadratic (spinGram J D)
      (fun i => m i / realTrace (D i)) x
    rw [ht] at he
    rw [he, physicalGram_quadratic]
    have hf := weighted_trace_fisher D hD m hm hr hP
      (spin_synthesis_isHermitian hJ D (fun i => (hD i).isHermitian) hc x)
    simpa only [← spinGram_mulVec, spin_synthesis_square hJJ D hc x] using hf

/-- An entrywise nonnegative symmetric matrix with a strictly positive fixed
vector is a Euclidean contraction from above.  This direct weighted-square
argument avoids a spectral-radius or irreducibility hypothesis. -/
theorem le_one_of_positive_fixed_vector (T : Matrix ι ι ℝ)
    (hT : T.IsHermitian) (hTnonneg : ∀ i j, 0 ≤ T i j)
    (m : ι → ℝ) (hm : ∀ i, 0 < m i) (hfix : T *ᵥ m = m) :
    T ≤ 1 := by
  have hsym (i j : ι) : T j i = T i j := by
    have h := congrFun (congrFun hT.eq i) j
    simpa only [Matrix.conjTranspose_apply, star_trivial] using h
  have hrow (i : ι) : ∑ j, T i j * m j = m i := congrFun hfix i
  apply Matrix.le_iff.mpr
  refine ⟨Matrix.isHermitian_one.sub hT, fun x => ?_⟩
  simp only [star_trivial, Matrix.sub_mulVec, Matrix.one_mulVec,
    dotProduct_sub, sub_nonneg]
  have he : (∑ i, ∑ j, T i j * (m j / m i * x i ^ 2)) = ∑ i, x i ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    calc
      _ = (∑ j, T i j * m j) * (x i ^ 2 / m i) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := by rw [hrow]; field_simp [(hm i).ne']
  have he' : (∑ i, ∑ j, T i j * (m i / m j * x j ^ 2)) = ∑ i, x i ^ 2 := by
    rw [Finset.sum_comm]
    simpa only [hsym] using he
  have hbound : (∑ i, ∑ j, T i j * (2 * x i * x j)) ≤
      ∑ i, ∑ j, T i j * (m j / m i * x i ^ 2 + m i / m j * x j ^ 2) := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    apply mul_le_mul_of_nonneg_left _ (hTnonneg i j)
    apply (mul_le_mul_iff_of_pos_right (mul_pos (hm i) (hm j))).mp
    have hnorm : (m j / m i * x i ^ 2 + m i / m j * x j ^ 2) * (m i * m j) =
        m j ^ 2 * x i ^ 2 + m i ^ 2 * x j ^ 2 := by
      field_simp [(hm i).ne', (hm j).ne']
      <;> ring
    rw [hnorm]
    nlinarith [sq_nonneg (m j * x i - m i * x j)]
  have hleft : (∑ i, ∑ j, T i j * (2 * x i * x j)) =
      2 * (x ⬝ᵥ (T *ᵥ x)) := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hleft] at hbound
  simp only [mul_add, Finset.sum_add_distrib] at hbound
  rw [he, he'] at hbound
  have hxx : x ⬝ᵥ x = ∑ i, x i ^ 2 := by simp only [dotProduct, pow_two]
  rw [hxx]
  linarith

/-- The physical Gram is positive semidefinite. -/
theorem gram_posSemidef (D : ι → Matrix n n ℂ)
    (hD : ∀ i, (D i).IsHermitian) : (gram D).PosSemidef := by
  have he : gram D = physicalRealGram (1 : Matrix n n ℂ) D := by
    ext i j
    simp only [gram, physicalRealGram, Matrix.one_mul, realTrace,
      RCLike.re_eq_complex_re]
  rw [he]
  exact physicalGram_posSemidef Matrix.PosSemidef.one D hD

/-- The concrete balanced fixed-point decomposition implies Tm=m. -/
theorem gram_fixed_vector (D : ι → Matrix n n ℂ) (m : ι → ℝ)
    {P : Matrix n n ℂ} (hP : P = ∑ i, m i • D i)
    (hm : ∀ i, m i = realTrace (P * D i)) : gram D *ᵥ m = m := by
  funext i
  rw [gram_mulVec]
  change realTrace (D i * ∑ j, m j • D j) = m i
  rw [← hP, realTrace_mul_comm, ← hm]

/-- The complete ordinary Gram contraction for the actual PSD atom family.
This proof needs no rank restriction and therefore also applies to spin atoms. -/
theorem gram_contraction (D : ι → Matrix n n ℂ)
    (hD : ∀ i, (D i).PosSemidef) (m : ι → ℝ) (hm : ∀ i, 0 < m i)
    {P : Matrix n n ℂ} (hP : P = ∑ i, m i • D i)
    (hmP : ∀ i, m i = realTrace (P * D i)) :
    0 ≤ gram D ∧ gram D ≤ 1 := by
  refine ⟨(gram_posSemidef D (fun i => (hD i).isHermitian)).nonneg, ?_⟩
  apply le_one_of_positive_fixed_vector (gram D) (gram_isHermitian D)
    (fun i j => realTrace_mul_nonneg (hD i) (hD j)) m hm
  exact gram_fixed_vector D m hP hmP

/-- The trace-and-prepare channel, valid for both balanced atom ranks. -/
def prepare (D : ι → Matrix n n ℂ) (Y : Matrix n n ℂ) : Matrix n n ℂ :=
  synthesis D (fun i => realTrace (D i * Y))

theorem prepare_synthesis (D : ι → Matrix n n ℂ) (x : ι → ℝ) :
    prepare D (synthesis D x) = synthesis D (gram D *ᵥ x) := by
  simp only [prepare, synthesis, gram_mulVec]

/-- Exact intertwining (I−Φ)D=D(I−T), without inverting the defect. -/
theorem defect_intertwining (D : ι → Matrix n n ℂ) (x : ι → ℝ) :
    synthesis D x - prepare D (synthesis D x) =
      synthesis D ((1 - gram D) *ᵥ x) := by
  rw [prepare_synthesis, Matrix.sub_mulVec, Matrix.one_mulVec]
  simp only [synthesis, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]

end MatrixSpencer.KSFisher
