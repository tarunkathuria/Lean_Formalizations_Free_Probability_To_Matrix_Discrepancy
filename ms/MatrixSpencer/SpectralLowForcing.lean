import MatrixSpencer.SpectralCutoff
import Mathlib.Algebra.QuadraticDiscriminant

/-!
# Low-spectrum forcing with noncommuting weights

This uses the actual Kraus channel, its proved ordinary HS contraction, and
explicit spectral cutoffs. No commutation between the weight R and P occurs.
-/

open scoped BigOperators ComplexConjugate MatrixOrder ComplexOrder Matrix

noncomputable section
namespace MatrixSpencer
namespace SpectralLowForcing

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]

/-- A weighted squared Hilbert--Schmidt energy, valid for non-Hermitian X. -/
def weightedEnergy (P R X : Matrix n n ℂ) : ℝ := realTrace (R * (Xᴴ * P * X))

lemma weightedEnergy_nonneg {P R : Matrix n n ℂ}
    (hP : P.PosSemidef) (hR : R.PosSemidef) (X : Matrix n n ℂ) :
    0 ≤ weightedEnergy P R X := realTrace_mul_nonneg hR (hP.conjTranspose_mul_mul_same X)

lemma weightedEnergy_add_le {P R : Matrix n n ℂ}
    (hP : P.PosSemidef) (hR : R.PosSemidef) (X Y : Matrix n n ℂ) :
    weightedEnergy P R (X + Y) ≤ 2 * (weightedEnergy P R X + weightedEnergy P R Y) := by
  have hid : weightedEnergy P R (X + Y) + weightedEnergy P R (X - Y) =
      2 * (weightedEnergy P R X + weightedEnergy P R Y) := by
    simp only [weightedEnergy, Matrix.conjTranspose_add, Matrix.conjTranspose_sub,
      Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub,
      realTrace_add, realTrace_sub]
    ring
  linarith [weightedEnergy_nonneg hP hR (X - Y)]

omit [DecidableEq n] in
lemma weightedEnergy_eq_trace {P R D : Matrix n n ℂ} (hD : D.IsHermitian) :
    weightedEnergy P R D = realTrace (P * D * R * D) := by
  rw [weightedEnergy, hD.eq]
  simpa only [Matrix.mul_assoc] using realTrace_mul_comm (R * D) (P * D)

omit [DecidableEq n] in
/-- Hilbert--Schmidt Cauchy--Schwarz proved from positivity of every scalar square. -/
lemma trace_mul_sq_le {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    realTrace (A * B) ^ 2 ≤ realTrace (A * A) * realTrace (B * B) := by
  have hpoly : ∀ t : ℝ, 0 ≤ realTrace (B * B) * (t * t) +
      (-2 * realTrace (A * B)) * t + realTrace (A * A) := by
    intro t
    have h := realTrace_conjTranspose_mul_self_nonneg (A - t • B)
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, hA.eq, hB.eq,
      star_trivial, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
      realTrace_sub, realTrace_smul] at h
    rw [realTrace_mul_comm B A] at h
    nlinarith
  have hd := discrim_le_zero hpoly
  unfold discrim at hd
  nlinarith

lemma trace_mul_le_sqrt {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    realTrace (A * B) ≤ Real.sqrt (realTrace (A * A) * realTrace (B * B)) := by
  apply (Real.le_sqrt (realTrace_mul_nonneg hA hB)
    (mul_nonneg (realTrace_mul_nonneg hA hA) (realTrace_mul_nonneg hB hB))).mpr
  exact trace_mul_sq_le hA.isHermitian hB.isHermitian

/-- The discarded part of a Hermitian force. -/
def lowForce {P : Matrix n n ℂ} (hP : P.IsHermitian) (ε : ℝ) (D : Matrix n n ℂ) :
    Matrix n n ℂ := SpectralCutoff.low hP ε * D +
      SpectralCutoff.high hP ε * D * SpectralCutoff.low hP ε

lemma lowForce_eq_sub {P : Matrix n n ℂ} (hP : P.IsHermitian) (ε : ℝ) (D : Matrix n n ℂ) :
    lowForce hP ε D = D - SpectralCutoff.high hP ε * D * SpectralCutoff.high hP ε := by
  dsimp [lowForce, SpectralCutoff.low]
  noncomm_ring

lemma lowForce_hermitian {P D : Matrix n n ℂ} (hP : P.IsHermitian)
    (hD : D.IsHermitian) (ε : ℝ) : (lowForce hP ε D).IsHermitian := by
  rw [lowForce_eq_sub]
  exact hD.sub (by simpa only [(SpectralCutoff.high_hermitian hP ε).eq] using
    Matrix.isHermitian_mul_mul_conjTranspose (SpectralCutoff.high hP ε) hD)

lemma low_left_energy {P D : Matrix n n ℂ} (hP : P.IsHermitian)
    (hD : D.IsHermitian) (ε : ℝ) (R : Matrix n n ℂ) :
    weightedEnergy P R (SpectralCutoff.low hP ε * D) =
      realTrace (R * (D * SpectralCutoff.lowPart hP ε * D)) := by
  simp only [weightedEnergy, Matrix.conjTranspose_mul, (SpectralCutoff.low_hermitian hP ε).eq,
    hD.eq, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (SpectralCutoff.low hP ε),
    ← Matrix.mul_assoc (SpectralCutoff.low hP ε * P), SpectralCutoff.low_mul_P_mul_low]

lemma low_right_energy {P D : Matrix n n ℂ} (hP : P.IsHermitian)
    (hD : D.IsHermitian) (ε : ℝ) (R : Matrix n n ℂ) :
    weightedEnergy P R (SpectralCutoff.high hP ε * D * SpectralCutoff.low hP ε) =
      realTrace ((SpectralCutoff.low hP ε * R * SpectralCutoff.low hP ε) *
        (D * (P - SpectralCutoff.lowPart hP ε) * D)) := by
  simp only [weightedEnergy, Matrix.conjTranspose_mul, (SpectralCutoff.high_hermitian hP ε).eq,
    (SpectralCutoff.low_hermitian hP ε).eq, hD.eq, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (SpectralCutoff.high hP ε),
    ← Matrix.mul_assoc (SpectralCutoff.high hP ε * P), SpectralCutoff.high_mul_P_mul_high]
  simpa only [Matrix.mul_assoc] using
    realTrace_mul_comm (R * (SpectralCutoff.low hP ε * (D * ((P - SpectralCutoff.lowPart hP ε) * D))))
      (SpectralCutoff.low hP ε)

lemma sum_low_left_energy (D : ι → Matrix n n ℂ) (hD : ∀ a, (D a).IsHermitian)
    {P : Matrix n n ℂ} (hP : P.IsHermitian) (ε : ℝ) (R : Matrix n n ℂ) :
    (∑ a, weightedEnergy P R (SpectralCutoff.low hP ε * D a)) =
      realTrace (R * krausChannel D (SpectralCutoff.lowPart hP ε)) := by
  simp only [low_left_energy hP (hD _), krausChannel, (hD _).eq,
    Matrix.mul_sum, realTrace_sum]

lemma sum_low_right_energy_le (D : ι → Matrix n n ℂ) (hD : ∀ a, (D a).IsHermitian)
    {P R : Matrix n n ℂ} (hP : P.PosSemidef) (hR : R.PosSemidef)
    (hfix : krausChannel D P = P) (ε : ℝ) :
    (∑ a, weightedEnergy P R (SpectralCutoff.high hP.isHermitian ε * D a *
      SpectralCutoff.low hP.isHermitian ε)) ≤ realTrace (R * SpectralCutoff.lowPart hP.isHermitian ε) := by
  let L := SpectralCutoff.low hP.isHermitian ε
  let Pl := SpectralCutoff.lowPart hP.isHermitian ε
  have hcap : krausChannel D (P - Pl) ≤ P := by
    exact (KrausContraction.channel_mono D
      (sub_le_self P (SpectralCutoff.lowPart_posSemidef hP ε).nonneg)).trans_eq hfix
  have hL : Lᴴ = L := (SpectralCutoff.low_hermitian hP.isHermitian ε).eq
  have hLRL : (L * R * L).PosSemidef := by
    simpa only [hL] using
      hR.mul_mul_conjTranspose_same L
  have hb := realTrace_mul_mono hLRL hcap
  have hid : realTrace (L * R * L * P) = realTrace (R * Pl) := by
    calc
      _ = realTrace (R * L * P * L) := by
        simpa only [Matrix.mul_assoc] using realTrace_mul_comm L (R * L * P)
      _ = _ := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc L,
          SpectralCutoff.low_mul_P_mul_low]
  rw [hid] at hb
  convert hb using 1
  simp only [low_right_energy hP.isHermitian (hD _), krausChannel, (hD _).eq,
    Matrix.mul_sum, realTrace_sum]
  rfl

/-- The exact low-spectrum intermediate forcing estimate. -/
theorem low_forcing_intermediate (D : ι → Matrix n n ℂ) (hD : ∀ a, (D a).IsHermitian)
    {P R : Matrix n n ℂ} (hP : P.PosSemidef) (hR : R.PosSemidef)
    (hfix : krausChannel D P = P) (ε : ℝ) :
    (∑ a, realTrace (P * lowForce hP.isHermitian ε (D a) * R * lowForce hP.isHermitian ε (D a))) ≤
      2 * (realTrace (R * krausChannel D (SpectralCutoff.lowPart hP.isHermitian ε)) +
        realTrace (R * SpectralCutoff.lowPart hP.isHermitian ε)) := by
  have htri : (∑ a, weightedEnergy P R (lowForce hP.isHermitian ε (D a))) ≤
      2 * ((∑ a, weightedEnergy P R (SpectralCutoff.low hP.isHermitian ε * D a)) +
        ∑ a, weightedEnergy P R (SpectralCutoff.high hP.isHermitian ε * D a *
          SpectralCutoff.low hP.isHermitian ε)) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, mul_add]
    apply Finset.sum_le_sum
    intro a _
    simpa only [lowForce, mul_add] using weightedEnergy_add_le hP hR
      (SpectralCutoff.low hP.isHermitian ε * D a)
      (SpectralCutoff.high hP.isHermitian ε * D a * SpectralCutoff.low hP.isHermitian ε)
  simp only [weightedEnergy_eq_trace (lowForce_hermitian hP.isHermitian (hD _) ε)] at htri
  rw [sum_low_left_energy D hD hP.isHermitian ε R] at htri
  exact htri.trans (by linarith [sum_low_right_energy_le D hD hP hR hfix ε])

omit [DecidableEq n] in
lemma channel_posSemidef (D : ι → Matrix n n ℂ) {X : Matrix n n ℂ}
    (hX : X.PosSemidef) : (krausChannel D X).PosSemidef := by
  apply Matrix.nonneg_iff_posSemidef.mp
  have h := KrausContraction.channel_mono D hX.nonneg
  simpa only [krausChannel, Matrix.mul_zero, Matrix.zero_mul, Finset.sum_const_zero] using h

lemma channel_lowPart_trace_sq_le (D : ι → Matrix n n ℂ) (hD : ∀ a, (D a).IsHermitian)
    {P : Matrix n n ℂ} (hP : P.PosDef) (hfix : krausChannel D P = P)
    {ε : ℝ} (hε : 0 < ε) :
    realTrace (krausChannel D (SpectralCutoff.lowPart hP.isHermitian ε) *
      krausChannel D (SpectralCutoff.lowPart hP.isHermitian ε)) ≤ ε * realTrace P := by
  have hPl := SpectralCutoff.lowPart_posSemidef hP.posSemidef ε
  have hPhi := channel_posSemidef D hPl
  have hc := KrausContraction.channel_hilbertSchmidt_trace_le D hD hP hfix
    (SpectralCutoff.lowPart hP.isHermitian ε)
  rw [hPhi.isHermitian.eq, hPl.isHermitian.eq] at hc
  exact hc.trans (SpectralCutoff.lowPart_trace_sq_le hP.posSemidef hε)

lemma trace_lowPart_le (R : Matrix n n ℂ) (hR : R.PosSemidef)
    {P : Matrix n n ℂ} (hP : P.PosSemidef) {ε : ℝ} (hε : 0 < ε) :
    realTrace (R * SpectralCutoff.lowPart hP.isHermitian ε) ≤
      Real.sqrt (realTrace (R * R) * ε * realTrace P) := by
  have h := trace_mul_le_sqrt hR (SpectralCutoff.lowPart_posSemidef hP ε)
  apply h.trans
  apply Real.sqrt_le_sqrt
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
    (SpectralCutoff.lowPart_trace_sq_le hP hε) (realTrace_mul_nonneg hR hR)

lemma trace_channel_lowPart_le (D : ι → Matrix n n ℂ) (hD : ∀ a, (D a).IsHermitian)
    {P R : Matrix n n ℂ} (hP : P.PosDef) (hR : R.PosSemidef)
    (hfix : krausChannel D P = P) {ε : ℝ} (hε : 0 < ε) :
    realTrace (R * krausChannel D (SpectralCutoff.lowPart hP.isHermitian ε)) ≤
      Real.sqrt (realTrace (R * R) * ε * realTrace P) := by
  have h := trace_mul_le_sqrt hR
    (channel_posSemidef D (SpectralCutoff.lowPart_posSemidef hP.posSemidef ε))
  apply h.trans
  apply Real.sqrt_le_sqrt
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
    (channel_lowPart_trace_sq_le D hD hP hfix hε) (realTrace_mul_nonneg hR hR)

/-- The low-spectrum forcing bound, with every matrix and parameter explicit. -/
theorem low_forcing_le (D : ι → Matrix n n ℂ) (hD : ∀ a, (D a).IsHermitian)
    {P R : Matrix n n ℂ} (hP : P.PosDef) (hR : R.PosSemidef)
    (hfix : krausChannel D P = P) {ε : ℝ} (hε : 0 < ε) :
    (∑ a, realTrace (P * lowForce hP.isHermitian ε (D a) * R * lowForce hP.isHermitian ε (D a))) ≤
      4 * Real.sqrt (realTrace (R * R) * ε * realTrace P) := by
  have h := low_forcing_intermediate D hD hP.posSemidef hR hfix ε
  have h₁ := trace_lowPart_le R hR hP.posSemidef hε
  have h₂ := trace_channel_lowPart_le D hD hP hR hfix hε
  linarith

end SpectralLowForcing
end MatrixSpencer
