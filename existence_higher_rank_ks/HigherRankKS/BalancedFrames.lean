import HigherRankKS.TwoFrameDirection
import MatrixSpencer.KSBalancedSpin

/-!
# Balanced frames for a nonlinear source

At a fixed density the source atoms are fixed matrices, although their
derivatives need not be rank-one trace-and-prepare maps. These definitions
retain separate input probes and source atoms.
-/

open Matrix MatrixSpencer
open scoped BigOperators MatrixOrder ComplexOrder

noncomputable section
namespace HigherRankKS.BalancedFrames

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]

def carrierMass (B : ι → Matrix n n ℂ) (S : Matrix n n ℂ) (i : ι) : ℝ :=
  realTrace (S * B i)

def transportMass (O : ι → Matrix n n ℂ) (Z : Matrix n n ℂ) (i : ι) : ℝ :=
  realTrace (Z * O i)

def measurementFrame (B : ι → Matrix n n ℂ) (c : ι → ℝ) (Z : Matrix n n ℂ)
    (i : ι) : Matrix n n ℂ := Real.sqrt (c i) • balancedKraus B Z i

def preparationFrame (B O : ι → Matrix n n ℂ) (c : ι → ℝ)
    (S Z : Matrix n n ℂ) (i : ι) : Matrix n n ℂ :=
  (Real.sqrt (c i) / carrierMass B S i) • balancedKraus O Z i

def coefficientMass (B : ι → Matrix n n ℂ) (c : ι → ℝ)
    (S : Matrix n n ℂ) (i : ι) : ℝ := Real.sqrt (c i) * carrierMass B S i

def probeScale (B O : ι → Matrix n n ℂ) (c : ι → ℝ)
    (S Z : Matrix n n ℂ) (i : ι) : ℝ :=
  Real.sqrt (c i) * transportMass O Z i / carrierMass B S i

omit [Fintype ι] in
theorem carrierMass_pos (B : ι → Matrix n n ℂ)
    (hB : ∀ i, (B i).PosSemidef) (hBne : ∀ i, B i ≠ 0)
    {S : Matrix n n ℂ} (hS : S.PosDef) (i : ι) : 0 < carrierMass B S i :=
  KSBalancedSpin.realTrace_mul_pos_of_posDef hS (hB i) (hBne i)

omit [Fintype ι] in
theorem transportMass_pos (O : ι → Matrix n n ℂ)
    (hO : ∀ i, (O i).PosSemidef) (hOne : ∀ i, O i ≠ 0)
    {Z : Matrix n n ℂ} (hZ : Z.PosDef) (i : ι) : 0 < transportMass O Z i :=
  KSBalancedSpin.realTrace_mul_pos_of_posDef hZ (hO i) (hOne i)

theorem measurementFrame_posSemidef (B : ι → Matrix n n ℂ)
    (hB : ∀ i, (B i).PosSemidef) (c : ι → ℝ) (Z : Matrix n n ℂ) (i : ι) :
    (measurementFrame B c Z i).PosSemidef :=
  KSBalancedSpin.atom_posSemidef B c hB Z i

omit [Fintype ι] in
theorem preparationFrame_posSemidef (B O : ι → Matrix n n ℂ)
    (hO : ∀ i, (O i).PosSemidef) (c : ι → ℝ) (S Z : Matrix n n ℂ)
    (hp : ∀ i, 0 ≤ carrierMass B S i) (i : ι) :
    (preparationFrame B O c S Z i).PosSemidef := by
  apply Matrix.PosSemidef.smul _ (div_nonneg (Real.sqrt_nonneg _) (hp i))
  simpa only [balancedKraus, (CFC.sqrt_nonneg Z).posSemidef.isHermitian.eq] using
    (hO i).conjTranspose_mul_mul_same (CFC.sqrt Z)

omit [Fintype ι] [DecidableEq n] in
theorem coefficientMass_pos (B : ι → Matrix n n ℂ) (c : ι → ℝ) (S : Matrix n n ℂ)
    (hc : ∀ i, 0 < c i) (hp : ∀ i, 0 < carrierMass B S i) (i : ι) :
    0 < coefficientMass B c S i :=
  mul_pos (Real.sqrt_pos.mpr (hc i)) (hp i)

omit [Fintype ι] [DecidableEq n] in
theorem probeScale_pos (B O : ι → Matrix n n ℂ) (c : ι → ℝ) (S Z : Matrix n n ℂ)
    (hc : ∀ i, 0 < c i) (hp : ∀ i, 0 < carrierMass B S i)
    (hτ : ∀ i, 0 < transportMass O Z i) (i : ι) : 0 < probeScale B O c S Z i :=
  div_pos (mul_pos (Real.sqrt_pos.mpr (hc i)) (hτ i)) (hp i)

omit [Fintype ι] in
theorem trace_preparationFrame (B O : ι → Matrix n n ℂ) (c : ι → ℝ)
    (S : Matrix n n ℂ) {Z : Matrix n n ℂ} (hZ : Z.PosDef) (i : ι) :
    realTrace (preparationFrame B O c S Z i) = probeScale B O c S Z i := by
  rw [preparationFrame, realTrace_smul]
  have ht : realTrace (balancedKraus O Z i) = transportMass O Z i := by
    rw [balancedKraus, realTrace_mul_cycle,
      CFC.sqrt_mul_sqrt_self Z hZ.posSemidef.nonneg]
    rfl
  rw [ht, probeScale]
  ring

theorem balancedDensity_eq_frameSum (B O : ι → Matrix n n ℂ) (c : ι → ℝ)
    (hc : ∀ i, 0 ≤ c i) {S Z : Matrix n n ℂ} (hZ : Z.PosDef)
    (hp : ∀ i, carrierMass B S i ≠ 0)
    (htransport : Z * (∑ i, c i • O i) * Z = S) :
    balancedDensity S Z = TwoFrames.frameSum (preparationFrame B O c S Z)
      (coefficientMass B c S) := by
  rw [balancedDensity_eq_source_congruence hZ htransport]
  simp only [TwoFrames.frameSum, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul,
    Matrix.smul_mul, preparationFrame, coefficientMass, smul_smul]
  apply Finset.sum_congr rfl
  intro i _
  have hs : Real.sqrt (c i) * carrierMass B S i *
      (Real.sqrt (c i) / carrierMass B S i) = c i := by
    field_simp [hp i]
    nlinarith [Real.sq_sqrt (hc i)]
  rw [hs]
  rfl

omit [Fintype ι] in
theorem measurement_pairing (B : ι → Matrix n n ℂ) (c : ι → ℝ)
    (S : Matrix n n ℂ) {Z : Matrix n n ℂ} (hZ : Z.PosDef) (i : ι) :
    realTrace (measurementFrame B c Z i * balancedDensity S Z) =
      coefficientMass B c S i := by
  rw [realTrace_mul_comm, measurementFrame, Matrix.mul_smul, realTrace_smul]
  rw [balancedKraus, KSBalancedSpin.trace_balanced_pair S (B i) hZ]
  rfl

omit [Fintype ι] in
theorem physical_diagonal (B : ι → Matrix n n ℂ) (c : ι → ℝ)
    (hc : ∀ i, 0 ≤ c i) (S : Matrix n n ℂ) {Z : Matrix n n ℂ}
    (hZ : Z.PosDef) (i : ι) :
    realTrace (balancedDensity S Z * measurementFrame B c Z i * measurementFrame B c Z i) =
      c i * realTrace (S * B i * Z * B i) := by
  simp only [measurementFrame, Matrix.mul_smul, Matrix.smul_mul, realTrace_smul]
  rw [← mul_assoc, Real.mul_self_sqrt (hc i)]
  congr 1
  exact balanced_physicalGram_entry B S hZ i i

omit [Fintype ι] in
theorem weighted_diagonal_le_probe (B O : ι → Matrix n n ℂ) (c : ι → ℝ)
    (hc : ∀ i, 0 < c i) (S : Matrix n n ℂ) {Z : Matrix n n ℂ}
    (hZ : Z.PosDef) (hp : ∀ i, 0 < carrierMass B S i)
    (hτ : ∀ i, 0 < transportMass O Z i)
    (hdiag : ∀ i, realTrace (S * B i * Z * B i) ≤ transportMass O Z i) (i : ι) :
    realTrace (balancedDensity S Z * measurementFrame B c Z i * measurementFrame B c Z i) /
      (coefficientMass B c S i / probeScale B O c S Z i) ≤ probeScale B O c S Z i ^ 2 := by
  rw [physical_diagonal B c (fun i => (hc i).le) S hZ]
  have hR : 0 < coefficientMass B c S i / probeScale B O c S Z i :=
    div_pos (coefficientMass_pos B c S hc hp i) (probeScale_pos B O c S Z hc hp hτ i)
  calc
    _ ≤ c i * transportMass O Z i /
        (coefficientMass B c S i / probeScale B O c S Z i) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hdiag i) (hc i).le) hR.le
    _ = _ := by
      unfold coefficientMass probeScale
      field_simp [(hp i).ne', (hτ i).ne', (Real.sqrt_pos.mpr (hc i)).ne']
      nlinarith [Real.sq_sqrt (hc i).le]

end HigherRankKS.BalancedFrames
