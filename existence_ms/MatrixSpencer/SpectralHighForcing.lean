import MatrixSpencer.ProjectionSuper
import MatrixSpencer.SpectralLowForcing
import MatrixSpencer.TensorOperator
import MatrixSpencer.KrausCoordinateEnergy

/-!
# High-spectrum Choi compression and Kraus forcing
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder
open Matrix

noncomputable section
namespace MatrixSpencer
namespace SpectralHighForcing

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n]

/-- The retained high-high block of the physical force. -/
def highForce {P : Matrix n n ℂ} (hP : P.IsHermitian) (ε : ℝ) (D : Matrix n n ℂ) :
    Matrix n n ℂ := SpectralCutoff.high hP ε * D * SpectralCutoff.high hP ε

lemma highForce_hermitian {P D : Matrix n n ℂ} (hP : P.IsHermitian)
    (hD : D.IsHermitian) (ε : ℝ) : (highForce hP ε D).IsHermitian := by
  simpa only [(SpectralCutoff.high_hermitian hP ε).eq] using
    Matrix.isHermitian_mul_mul_conjTranspose (SpectralCutoff.high hP ε) hD

lemma high_smul_le {P : Matrix n n ℂ} (hP : P.PosSemidef) {ε : ℝ} (hε : 0 < ε) :
    ε • SpectralCutoff.high hP.isHermitian ε ≤ P := by
  have h := smul_le_smul_of_nonneg_left (SpectralCutoff.high_le_inv_smul hP hε) hε.le
  simpa only [smul_smul, mul_inv_cancel₀ hε.ne', one_smul] using h

omit [Fintype ι] [DecidableEq ι] in
lemma highForce_synthesis {P : Matrix n n ℂ} (hP : P.IsHermitian) (ε : ℝ)
    (D : ι → Matrix n n ℂ) :
    krausSynthesis (fun a => highForce hP ε (D a)) =
      ProjectionSuper.compression (SpectralCutoff.high hP ε) * krausSynthesis D := by
  simpa only [(SpectralCutoff.high_hermitian hP ε).eq, highForce] using
    (ProjectionSuper.compression_synthesis (SpectralCutoff.high hP ε) D).symm

/-- The actual high coefficient Gram has cap t/ε, with no factor loss. -/
lemma highForce_gram_cap (D : ι → Matrix n n ℂ) (hD : ∀ a, (D a).IsHermitian)
    {P : Matrix n n ℂ} (hP : P.PosSemidef) {t ε : ℝ} (hε : 0 < ε)
    (hcap : physicalRealGram P D ≤ algebraMap ℝ (Matrix ι ι ℝ) t) :
    (krausSynthesis (fun a => highForce hP.isHermitian ε (D a)))ᴴ *
      krausSynthesis (fun a => highForce hP.isHermitian ε (D a)) ≤
        (t / ε) • (1 : Matrix ι ι ℂ) := by
  let H := SpectralCutoff.high hP.isHermitian ε
  let E := ProjectionSuper.compression H
  let U := krausSynthesis D
  have hH : H.IsHermitian := SpectralCutoff.high_hermitian hP.isHermitian ε
  have hHH : H * H = H := SpectralCutoff.high_idempotent hP.isHermitian ε
  have hE : E.IsHermitian := ProjectionSuper.compression_hermitian hH
  have hEE : E * E = E := ProjectionSuper.compression_idempotent hH hHH
  have hJE := ProjectionSuper.compression_le_jordan hP.isHermitian hH hHH
    (SpectralCutoff.high_le_one hP.isHermitian ε) hε.le (high_smul_le hP hε)
  have hc : (2 * ε) • (Uᴴ * E * U) ≤ Uᴴ * jordanSuper P * U := by
    apply Matrix.le_iff.mpr
    have h := (Matrix.le_iff.mp hJE).conjTranspose_mul_mul_same U
    simpa only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul] using h
  have hbound : (2 * ε) • (Uᴴ * E * U) ≤ (2 * t) • (1 : Matrix ι ι ℂ) := by
    have hh := smul_le_smul_of_nonneg_left (realMatrixEmbedding_mono hcap) (by norm_num : (0:ℝ) ≤ 2)
    rw [realMatrixEmbedding_algebraMap, Algebra.algebraMap_eq_smul_one, smul_smul] at hh
    exact hc.trans (by simpa only [U, jordanSuper_krausGram hP.isHermitian D hD] using hh)
  have hs := smul_le_smul_of_nonneg_left hbound
    (show (0 : ℝ) ≤ (2 * ε)⁻¹ from inv_nonneg.mpr (mul_nonneg (by norm_num) hε.le))
  have hcancel : (2 * ε)⁻¹ * (2 * ε) = 1 := inv_mul_cancel₀ (mul_ne_zero (by norm_num) hε.ne')
  have hcoef : (2 * ε)⁻¹ * (2 * t) = t / ε := by field_simp
  rw [smul_smul, smul_smul, hcancel, one_smul, hcoef] at hs
  rw [highForce_synthesis, Matrix.conjTranspose_mul, hE.eq]
  have heq : Uᴴ * E * (E * U) = Uᴴ * E * U := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc E, hEE, ← Matrix.mul_assoc]
  exact heq ▸ hs

/-- The actual high Choi operator has an identity cap. -/
lemma highForce_choi_cap_one (D : ι → Matrix n n ℂ) (hD : ∀ a, (D a).IsHermitian)
    {P : Matrix n n ℂ} (hP : P.PosSemidef) {t ε : ℝ} (ht : 0 ≤ t) (hε : 0 < ε)
    (hcap : physicalRealGram P D ≤ algebraMap ℝ (Matrix ι ι ℝ) t) :
    krausChoi (fun a => highForce hP.isHermitian ε (D a)) ≤
      (t / ε) • (1 : Matrix (n × n) (n × n) ℂ) := by
  rw [krausChoi_eq_synthesis_mul_adjoint]
  have h := synthesis_cap_of_gram_cap (krausSynthesis (fun a => highForce hP.isHermitian ε (D a)))
    (div_nonneg ht hε.le) (by
      simpa only [Algebra.algebraMap_eq_smul_one] using highForce_gram_cap D hD hP hε hcap)
  simpa only [Algebra.algebraMap_eq_smul_one] using h

/-- The Choi cap lives on the actual matrix compression projection E. -/
theorem highForce_choi_cap (D : ι → Matrix n n ℂ) (hD : ∀ a, (D a).IsHermitian)
    {P : Matrix n n ℂ} (hP : P.PosSemidef) {t ε : ℝ} (ht : 0 ≤ t) (hε : 0 < ε)
    (hcap : physicalRealGram P D ≤ algebraMap ℝ (Matrix ι ι ℝ) t) :
    krausChoi (fun a => highForce hP.isHermitian ε (D a)) ≤
      (t / ε) • ProjectionSuper.compression (SpectralCutoff.high hP.isHermitian ε) := by
  let H := SpectralCutoff.high hP.isHermitian ε
  let E := ProjectionSuper.compression H
  have hE : E.IsHermitian := ProjectionSuper.compression_hermitian (SpectralCutoff.high_hermitian hP.isHermitian ε)
  have hEE : E * E = E := ProjectionSuper.compression_idempotent
    (SpectralCutoff.high_hermitian hP.isHermitian ε) (SpectralCutoff.high_idempotent hP.isHermitian ε)
  have heq : E * krausChoi (fun a => highForce hP.isHermitian ε (D a)) * E =
      krausChoi (fun a => highForce hP.isHermitian ε (D a)) := by
    rw [krausChoi_eq_synthesis_mul_adjoint, highForce_synthesis, Matrix.conjTranspose_mul, hE.eq]
    change E * (E * krausSynthesis D * ((krausSynthesis D)ᴴ * E)) * E =
      E * krausSynthesis D * ((krausSynthesis D)ᴴ * E)
    simp only [← Matrix.mul_assoc, hEE]
    rw [Matrix.mul_assoc, Matrix.mul_assoc, hEE]
    simp only [Matrix.mul_assoc]
  have h := KrausContraction.congruence_mono (highForce_choi_cap_one D hD hP ht hε hcap) E hE
  simpa only [heq, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hEE] using h

omit [Fintype ι] [DecidableEq ι] in
lemma left_weighted_realGram {P : Matrix n n ℂ} (hP : P.PosSemidef)
    (D : ι → Matrix n n ℂ) (hD : ∀ a, (D a).IsHermitian) :
    realKrausGram (fun a => CFC.sqrt P * D a) = (physicalRealGram P D)ᵀ := by
  ext a b
  simp only [realKrausGram, physicalRealGram, Matrix.transpose_apply,
    Matrix.conjTranspose_mul, (hD a).eq,
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg P)).isHermitian.eq]
  have he : D a * CFC.sqrt P * (CFC.sqrt P * D b) = D a * P * D b := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (CFC.sqrt P),
      CFC.sqrt_mul_sqrt_self P hP.nonneg, ← Matrix.mul_assoc]
  rw [he, Matrix.trace_mul_cycle, Matrix.trace_mul_cycle]

lemma transpose_mono {m : Type*} [Fintype m] {A B : Matrix m m ℂ} (h : A ≤ B) : Aᵀ ≤ Bᵀ := by
  apply Matrix.le_iff.mpr
  simpa only [Matrix.transpose_sub] using (Matrix.le_iff.mp h).transpose

lemma real_transpose_mono {m : Type*} [Fintype m] {A B : Matrix m m ℝ} (h : A ≤ B) : Aᵀ ≤ Bᵀ := by
  apply Matrix.le_iff.mpr
  simpa only [Matrix.transpose_sub] using (Matrix.le_iff.mp h).transpose

/-- The first tensor flattening is obtained from the actual physical Gram cap. -/
lemma first_flattening_cap (D : ι → Matrix n n ℂ) (hD : ∀ a, (D a).IsHermitian)
    {P : Matrix n n ℂ} (hP : P.PosSemidef) {t ε : ℝ}
    (hcap : physicalRealGram P D ≤ algebraMap ℝ (Matrix ι ι ℝ) t) :
    let F := krausSynthesis (fun a => CFC.sqrt P * D a * SpectralCutoff.high hP.isHermitian ε)
    Fᴴ * F ≤ (2 * t) • (1 : Matrix ι ι ℂ) := by
  have hbase : (krausSynthesis (fun a => CFC.sqrt P * D a))ᴴ *
      krausSynthesis (fun a => CFC.sqrt P * D a) ≤ (2 * t) • (1 : Matrix ι ι ℂ) := by
    have hreal : (((krausSynthesis (fun a => CFC.sqrt P * D a))ᴴ *
        krausSynthesis (fun a => CFC.sqrt P * D a)).map Complex.re) =
          (physicalRealGram P D)ᵀ := by
      calc
        _ = realKrausGram (fun a => CFC.sqrt P * D a) := by
          ext a b
          simp only [Matrix.map_apply, krausGram_entry, realKrausGram]
        _ = _ := left_weighted_realGram hP D hD
    have htcap := real_transpose_mono hcap
    have h := complexGram_cap_of_realPart_cap _ (Matrix.posSemidef_conjTranspose_mul_self _) t (by
      rw [hreal]
      simpa only [Algebra.algebraMap_eq_smul_one, Matrix.transpose_smul, Matrix.transpose_one] using htcap)
    simpa only [Algebra.algebraMap_eq_smul_one] using h
  exact (ProjectionSuper.synthesis_right_projection_gram_le (fun a => CFC.sqrt P * D a)
    (SpectralCutoff.high_hermitian hP.isHermitian ε) (SpectralCutoff.high_idempotent hP.isHermitian ε)
    (SpectralCutoff.high_le_one hP.isHermitian ε)).trans hbase

/-- The second flattening is the transpose of the high synthesis matrix. -/
lemma second_flattening_cap (D : ι → Matrix n n ℂ) (hD : ∀ a, (D a).IsHermitian)
    {P : Matrix n n ℂ} (hP : P.PosSemidef) {t ε : ℝ} (ht : 0 ≤ t) (hε : 0 < ε)
    (hcap : physicalRealGram P D ≤ algebraMap ℝ (Matrix ι ι ℝ) t) :
    let G := (krausSynthesis (fun a => highForce hP.isHermitian ε (D a)))ᵀ
    Gᴴ * G ≤ (t / ε) • (1 : Matrix (n × n) (n × n) ℂ) := by
  have h := transpose_mono (highForce_choi_cap_one D hD hP ht hε hcap)
  rw [krausChoi_eq_synthesis_mul_adjoint, Matrix.transpose_mul] at h
  simpa only [Matrix.transpose_smul, Matrix.transpose_one, Matrix.transpose_conjTranspose] using h

omit [DecidableEq ι] [DecidableEq n] in
lemma channel_hermitian (D : ι → Matrix n n ℂ) {X : Matrix n n ℂ} (hX : X.IsHermitian) :
    (krausChannel D X).IsHermitian := by
  rw [Matrix.IsHermitian, ← KrausContraction.channel_adjoint, hX.eq]

lemma highForce_sandwich {P : Matrix n n ℂ} (hP : P.IsHermitian) (ε : ℝ) (D : Matrix n n ℂ) :
    SpectralCutoff.high hP ε * highForce hP ε D * SpectralCutoff.high hP ε = highForce hP ε D := by
  dsimp [highForce]
  simp only [← Matrix.mul_assoc, SpectralCutoff.high_idempotent]
  rw [Matrix.mul_assoc, SpectralCutoff.high_idempotent]

/-- The actual high output covariance in physical matrix space. -/
def outputGram {P : Matrix n n ℂ} (hP : P.IsHermitian) (ε : ℝ) (D : ι → Matrix n n ℂ) :
    Matrix n n ℂ := ∑ a, krausChannel D (highForce hP ε (D a)) * P *
      krausChannel D (highForce hP ε (D a))

omit [DecidableEq ι] in
lemma outputGram_eq_gramSum {P : Matrix n n ℂ} (hP : P.PosSemidef) (ε : ℝ)
    (D : ι → Matrix n n ℂ) (hD : ∀ a, (D a).IsHermitian) :
    outputGram hP.isHermitian ε D =
      gramSum (fun a => CFC.sqrt P * krausChannel D (highForce hP.isHermitian ε (D a))) := by
  unfold outputGram gramSum
  apply Finset.sum_congr rfl
  intro a _
  dsimp only
  have hY := channel_hermitian D (highForce_hermitian hP.isHermitian (hD a) ε)
  rw [Matrix.conjTranspose_mul, hY.eq,
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg P)).isHermitian.eq]
  conv_rhs => rw [Matrix.mul_assoc, ← Matrix.mul_assoc (CFC.sqrt P),
    CFC.sqrt_mul_sqrt_self P hP.nonneg, ← Matrix.mul_assoc]

omit [DecidableEq ι] in
lemma outputGram_posSemidef {P : Matrix n n ℂ} (hP : P.PosSemidef) (ε : ℝ)
    (D : ι → Matrix n n ℂ) (hD : ∀ a, (D a).IsHermitian) :
    (outputGram hP.isHermitian ε D).PosSemidef := by
  rw [outputGram_eq_gramSum hP ε D hD]
  apply Matrix.nonneg_iff_posSemidef.mp
  exact Finset.sum_nonneg (fun a _ => (Matrix.posSemidef_conjTranspose_mul_self _).nonneg)

omit [DecidableEq ι] in
/-- The concrete tensor composition is exactly the high channel output. -/
lemma mixedProduct_eq_output {P : Matrix n n ℂ} (hP : P.IsHermitian) (ε : ℝ)
    (D : ι → Matrix n n ℂ) (hD : ∀ a, (D a).IsHermitian) (a : ι) :
    (∑ b, (CFC.sqrt P * D b * SpectralCutoff.high hP ε) * highForce hP ε (D a) *
      (SpectralCutoff.high hP ε * D b)) = CFC.sqrt P * krausChannel D (highForce hP ε (D a)) := by
  rw [krausChannel, Matrix.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [(hD b).eq]
  calc
    _ = CFC.sqrt P * D b * (SpectralCutoff.high hP ε * highForce hP ε (D a) *
      SpectralCutoff.high hP ε) * D b := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [highForce_sandwich]; simp only [Matrix.mul_assoc]

omit [DecidableEq ι] in
lemma gramSum_high_inputs {P : Matrix n n ℂ} (hP : P.IsHermitian) (ε : ℝ)
    (D : ι → Matrix n n ℂ) (hD : ∀ a, (D a).IsHermitian) :
    gramSum (fun b => SpectralCutoff.high hP ε * D b) = krausChannel D (SpectralCutoff.high hP ε) := by
  unfold gramSum krausChannel
  apply Finset.sum_congr rfl
  intro b _
  rw [Matrix.conjTranspose_mul, (hD b).eq, (SpectralCutoff.high_hermitian hP ε).eq,
    Matrix.mul_assoc, ← Matrix.mul_assoc (SpectralCutoff.high hP ε),
    SpectralCutoff.high_idempotent, ← Matrix.mul_assoc]

/-- The first high-output matrix-order estimate, from the two actual flattenings. -/
theorem outputGram_le_channel_high (D : ι → Matrix n n ℂ) (hD : ∀ a, (D a).IsHermitian)
    {P : Matrix n n ℂ} (hP : P.PosSemidef) {t ε : ℝ} (ht : 0 ≤ t) (hε : 0 < ε)
    (hcap : physicalRealGram P D ≤ algebraMap ℝ (Matrix ι ι ℝ) t) :
    outputGram hP.isHermitian ε D ≤
      (2 * t * (t / ε)) • krausChannel D (SpectralCutoff.high hP.isHermitian ε) := by
  have h := mixedProduct_gramSum_le
    (fun b => CFC.sqrt P * D b * SpectralCutoff.high hP.isHermitian ε)
    (fun a => highForce hP.isHermitian ε (D a))
    (fun b => SpectralCutoff.high hP.isHermitian ε * D b)
    (div_nonneg ht hε.le) (first_flattening_cap D hD hP hcap)
    (second_flattening_cap D hD hP ht hε hcap)
  simpa only [mixedProduct_eq_output hP.isHermitian ε D hD, ← outputGram_eq_gramSum hP ε D hD,
    gramSum_high_inputs hP.isHermitian ε D hD, mul_comm (t / ε)] using h

omit [DecidableEq ι] in
lemma channel_high_le {P : Matrix n n ℂ} (hP : P.PosSemidef) (D : ι → Matrix n n ℂ)
    (hfix : krausChannel D P = P) {ε : ℝ} (hε : 0 < ε) :
    krausChannel D (SpectralCutoff.high hP.isHermitian ε) ≤ ε⁻¹ • P := by
  have h := KrausContraction.channel_mono D (SpectralCutoff.high_le_inv_smul hP hε)
  simpa only [KrausContraction.channel_real_smul, hfix] using h

/-- The high-output covariance has the asserted cap by P. -/
theorem outputGram_le_P (D : ι → Matrix n n ℂ) (hD : ∀ a, (D a).IsHermitian)
    {P : Matrix n n ℂ} (hP : P.PosSemidef) {t ε : ℝ} (ht : 0 ≤ t) (hε : 0 < ε)
    (hcap : physicalRealGram P D ≤ algebraMap ℝ (Matrix ι ι ℝ) t)
    (hfix : krausChannel D P = P) :
    outputGram hP.isHermitian ε D ≤ (2 * (t / ε) ^ 2) • P := by
  have h := smul_le_smul_of_nonneg_left (channel_high_le hP D hfix hε)
    (show (0 : ℝ) ≤ 2 * t * (t / ε) from
      mul_nonneg (mul_nonneg (by norm_num) ht) (div_nonneg ht hε.le))
  have hc : (2 * t * (t / ε)) * ε⁻¹ = 2 * (t / ε) ^ 2 := by ring
  rw [smul_smul, hc] at h
  exact (outputGram_le_channel_high D hD hP ht hε hcap).trans h

omit [DecidableEq ι] in
/-- The physical trace of the output covariance is exactly a coordinate-frame energy. -/
lemma outputGram_trace_eq_energy (D : ι → Matrix n n ℂ) (hD : ∀ a, (D a).IsHermitian)
    {P : Matrix n n ℂ} (hP : P.PosSemidef) (ε : ℝ) :
    realTrace (P * outputGram hP.isHermitian ε D) =
      entryEnergy ((ProjectionSuper.compression (CFC.sqrt P) * krausSuper D) *
        krausSynthesis (fun a => highForce hP.isHermitian ε (D a))) := by
  rw [Matrix.mul_assoc, KrausCoordinateEnergy.super_synthesis,
    ProjectionSuper.compression_synthesis,
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg P)).isHermitian.eq,
    KrausCoordinateEnergy.entryEnergy_synthesis]
  simp only [outputGram, Matrix.mul_sum, realTrace_sum]
  apply Finset.sum_congr rfl
  intro a _
  simpa only [Matrix.mul_assoc] using
    (KrausCoordinateEnergy.sandwiched_energy hP
      (channel_hermitian D (highForce_hermitian hP.isHermitian (hD a) ε))).symm

omit [DecidableEq ι] in
/-- The adjoint weighted channel has the same entry energy as the realigned weighted Kraus map. -/
lemma weighted_output_operator_energy (D : ι → Matrix n n ℂ) (hD : ∀ a, (D a).IsHermitian)
    {P : Matrix n n ℂ} (_hP : P.PosSemidef) :
    entryEnergy (ProjectionSuper.compression (CFC.sqrt P) * krausSuper D) =
      entryEnergy (krausSuper (fun a => D a * CFC.sqrt P)) := by
  have hS : (CFC.sqrt P).IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg P)).isHermitian
  rw [← KrausCoordinateEnergy.entryEnergy_adjoint
      (ProjectionSuper.compression (CFC.sqrt P) * krausSuper D),
    Matrix.conjTranspose_mul, (KrausContraction.super_hermitian D hD).eq,
    (ProjectionSuper.compression_hermitian hS).eq, ← KrausCoordinateEnergy.right_weighted_super]

/-- The independent weighted-frame estimate gives the high covariance trace bound. -/
theorem outputGram_trace_le (D : ι → Matrix n n ℂ) (hD : ∀ a, (D a).IsHermitian)
    {P : Matrix n n ℂ} (hP : P.PosSemidef) {t ε : ℝ} (ht : 0 ≤ t) (hε : 0 < ε)
    (hcap : physicalRealGram P D ≤ algebraMap ℝ (Matrix ι ι ℝ) t)
    (hfix : krausChannel D P = P) :
    realTrace (P * outputGram hP.isHermitian ε D) ≤ (2 * t * (t / ε)) * realTrace P := by
  have hc := highForce_choi_cap_one D hD hP ht hε hcap
  rw [krausChoi_eq_synthesis_mul_adjoint] at hc
  have he := KrausCoordinateEnergy.entryEnergy_mul_le
    (ProjectionSuper.compression (CFC.sqrt P) * krausSuper D)
    (krausSynthesis (fun a => highForce hP.isHermitian ε (D a))) hc
  rw [← outputGram_trace_eq_energy D hD hP ε, weighted_output_operator_energy D hD hP] at he
  have hf : (∑ a, D a * P * D a) = P := by
    simpa only [krausChannel, (hD _).eq] using hfix
  have hw := weightedKraus_realignment_bound hP D hD hf ht hcap
  have h := he.trans (mul_le_mul_of_nonneg_left hw (div_nonneg ht hε.le))
  convert h using 1; ring

/-- The squared output trace follows from matrix order and the independent trace estimate. -/
theorem outputGram_trace_sq_le (D : ι → Matrix n n ℂ) (hD : ∀ a, (D a).IsHermitian)
    {P : Matrix n n ℂ} (hP : P.PosSemidef) {t ε : ℝ} (ht : 0 ≤ t) (hε : 0 < ε)
    (hcap : physicalRealGram P D ≤ algebraMap ℝ (Matrix ι ι ℝ) t)
    (hfix : krausChannel D P = P) :
    realTrace (outputGram hP.isHermitian ε D * outputGram hP.isHermitian ε D) ≤
      (4 * t * (t / ε) ^ 3) * realTrace P := by
  have h := realTrace_mul_mono (outputGram_posSemidef hP ε D hD)
    (outputGram_le_P D hD hP ht hε hcap hfix)
  rw [Matrix.mul_smul, realTrace_smul,
    realTrace_mul_comm (outputGram hP.isHermitian ε D) P] at h
  have htrace := outputGram_trace_le D hD hP ht hε hcap hfix
  have hb := h.trans (mul_le_mul_of_nonneg_left htrace
    (mul_nonneg (by norm_num) (sq_nonneg (t / ε))))
  convert hb using 1; ring

end SpectralHighForcing
end MatrixSpencer
