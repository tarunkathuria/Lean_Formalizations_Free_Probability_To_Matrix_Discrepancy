import MatrixSpencer.CovarianceSource
import MatrixSpencer.FidelityBounds
import MatrixSpencer.WeightedKraus

/-!
# The concrete balanced transport frame

Congruence factors are frozen at the current transport point. The identities
below require no commutation between the density and transport matrices.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder
open Matrix

noncomputable section

namespace MatrixSpencer

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]

def transportInverseSqrt (Z : Matrix n n ℂ) : Matrix n n ℂ := (CFC.sqrt Z)⁻¹

def balancedDensity (S Z : Matrix n n ℂ) : Matrix n n ℂ :=
  transportInverseSqrt Z * S * transportInverseSqrt Z

def balancedRoot (S Z : Matrix n n ℂ) : Matrix n n ℂ :=
  transportInverseSqrt Z * CFC.sqrt S * transportInverseSqrt Z

def balancedKraus (B : ι → Matrix n n ℂ) (Z : Matrix n n ℂ) (a : ι) : Matrix n n ℂ :=
  CFC.sqrt Z * B a * CFC.sqrt Z

theorem transportInverseSqrt_posDef {Z : Matrix n n ℂ} (hZ : Z.PosDef) :
    (transportInverseSqrt Z).PosDef := hZ.posDef_sqrt.inv

theorem sqrt_mul_transportInverseSqrt {Z : Matrix n n ℂ} (hZ : Z.PosDef) :
    CFC.sqrt Z * transportInverseSqrt Z = 1 := by
  letI : Invertible (CFC.sqrt Z) := hZ.posDef_sqrt.isUnit.invertible
  exact Matrix.mul_inv_of_invertible _

theorem transportInverseSqrt_mul_sqrt {Z : Matrix n n ℂ} (hZ : Z.PosDef) :
    transportInverseSqrt Z * CFC.sqrt Z = 1 := by
  letI : Invertible (CFC.sqrt Z) := hZ.posDef_sqrt.isUnit.invertible
  exact Matrix.inv_mul_of_invertible _

theorem transportInverseSqrt_mul_self_matrix {Z : Matrix n n ℂ} (hZ : Z.PosDef) :
    transportInverseSqrt Z * Z = CFC.sqrt Z := by
  conv_lhs => rhs; rw [← CFC.sqrt_mul_sqrt_self Z hZ.posSemidef.nonneg]
  rw [← Matrix.mul_assoc, transportInverseSqrt_mul_sqrt hZ, Matrix.one_mul]

theorem matrix_mul_transportInverseSqrt {Z : Matrix n n ℂ} (hZ : Z.PosDef) :
    Z * transportInverseSqrt Z = CFC.sqrt Z := by
  conv_lhs => lhs; rw [← CFC.sqrt_mul_sqrt_self Z hZ.posSemidef.nonneg]
  rw [Matrix.mul_assoc, sqrt_mul_transportInverseSqrt hZ, Matrix.mul_one]

theorem balancedDensity_posDef {S Z : Matrix n n ℂ} (hS : S.PosDef) (hZ : Z.PosDef) :
    (balancedDensity S Z).PosDef := by
  have hi := Matrix.mulVec_injective_iff_isUnit.mpr (transportInverseSqrt_posDef hZ).isUnit
  simpa only [(transportInverseSqrt_posDef hZ).isHermitian.eq, balancedDensity] using
    hS.conjTranspose_mul_mul_same hi

theorem balancedRoot_posDef {S Z : Matrix n n ℂ} (hS : S.PosDef) (hZ : Z.PosDef) :
    (balancedRoot S Z).PosDef := by
  have hi := Matrix.mulVec_injective_iff_isUnit.mpr (transportInverseSqrt_posDef hZ).isUnit
  simpa only [(transportInverseSqrt_posDef hZ).isHermitian.eq, balancedRoot] using
    hS.posDef_sqrt.conjTranspose_mul_mul_same hi

omit [Fintype ι] in
theorem balancedKraus_isHermitian (B : ι → Matrix n n ℂ)
    (hB : ∀ i, (B i).IsHermitian) (Z : Matrix n n ℂ) (a : ι) :
    (balancedKraus B Z a).IsHermitian := by
  unfold balancedKraus Matrix.IsHermitian
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    (CFC.sqrt_nonneg Z).posSemidef.isHermitian.eq, (hB a).eq]
  simp only [Matrix.mul_assoc]

/-- Transport makes the balanced density the source congruence as well. -/
theorem balancedDensity_eq_source_congruence {S M Z : Matrix n n ℂ}
    (hZ : Z.PosDef) (htransport : Z * M * Z = S) :
    balancedDensity S Z = CFC.sqrt Z * M * CFC.sqrt Z := by
  unfold balancedDensity
  rw [← htransport]
  calc
    _ = (transportInverseSqrt Z * Z) * M * (Z * transportInverseSqrt Z) := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [transportInverseSqrt_mul_self_matrix hZ, matrix_mul_transportInverseSqrt hZ]

/-- Exact Kraus conjugation, retaining all matrix multiplication order. -/
theorem balancedKraus_channel (B : ι → Matrix n n ℂ) {S Z : Matrix n n ℂ} (hZ : Z.PosDef) :
    krausChannel (balancedKraus B Z) (balancedDensity S Z) =
      CFC.sqrt Z * krausChannel B S * CFC.sqrt Z := by
  simp only [krausChannel, Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  simp only [balancedKraus, balancedDensity, Matrix.conjTranspose_mul,
    (CFC.sqrt_nonneg Z).posSemidef.isHermitian.eq]
  calc
    _ = CFC.sqrt Z * B a * (CFC.sqrt Z * transportInverseSqrt Z) * S *
        (transportInverseSqrt Z * CFC.sqrt Z) * (B a)ᴴ * CFC.sqrt Z := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [sqrt_mul_transportInverseSqrt hZ, transportInverseSqrt_mul_sqrt hZ,
      Matrix.mul_one, Matrix.mul_one]; simp only [Matrix.mul_assoc]

/-- The concrete balanced channel fixes the positive balanced density. -/
theorem balancedKraus_fixedPoint (B : ι → Matrix n n ℂ) {S Z : Matrix n n ℂ}
    (hZ : Z.PosDef) (htransport : Z * krausChannel B S * Z = S) :
    krausChannel (balancedKraus B Z) (balancedDensity S Z) = balancedDensity S Z := by
  rw [balancedKraus_channel B hZ, balancedDensity_eq_source_congruence hZ htransport]

/-- The balanced density trace equals the unnormalized fidelity at actual transport. -/
theorem realTrace_balancedDensity_actual (B : ι → Matrix n n ℂ) {S : Matrix n n ℂ}
    (hS : S.PosDef) (hM : (krausChannel B S).PosDef) :
    realTrace (balancedDensity S (transportOptimizer S (krausChannel B S))) =
      fidelity S (krausChannel B S) := by
  let Z := transportOptimizer S (krausChannel B S)
  have hZ := transportOptimizer_posDef hS hM
  rw [balancedDensity_eq_source_congruence hZ (transportOptimizer_solve hS hM)]
  rw [realTrace_mul_cycle, CFC.sqrt_mul_sqrt_self _ hZ.posSemidef.nonneg, realTrace_mul_comm]
  exact trace_transportOptimizer_eq_fidelity hS hM

/-- The balanced root square has at most the source trace, without a commutation hypothesis. -/
theorem realTrace_balancedRoot_square_le {S M Z : Matrix n n ℂ}
    (hS : S.PosSemidef) (hZ : Z.PosDef) (htransport : Z * M * Z = S) :
    realTrace (balancedRoot S Z * balancedRoot S Z) ≤ realTrace M := by
  have h := realTrace_balanced_square_le (transportInverseSqrt_posDef hZ).isHermitian hS
  have heq : (transportInverseSqrt Z * transportInverseSqrt Z) * S *
      (transportInverseSqrt Z * transportInverseSqrt Z) = M := by
    rw [← htransport]
    calc
      _ = transportInverseSqrt Z * (transportInverseSqrt Z * Z) * M *
          (Z * transportInverseSqrt Z) * transportInverseSqrt Z := by simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [transportInverseSqrt_mul_self_matrix hZ, matrix_mul_transportInverseSqrt hZ,
          transportInverseSqrt_mul_sqrt hZ, Matrix.one_mul, Matrix.mul_assoc,
          sqrt_mul_transportInverseSqrt hZ, Matrix.mul_one]
  simpa only [heq, balancedRoot] using h

omit [Fintype ι] in
/-- The balanced physical Gram equals the original transport trace Gram. -/
theorem balanced_physicalGram_entry (B : ι → Matrix n n ℂ) (S : Matrix n n ℂ)
    {Z : Matrix n n ℂ} (hZ : Z.PosDef) (a b : ι) :
    physicalRealGram (balancedDensity S Z) (balancedKraus B Z) a b =
      realTrace (S * B a * Z * B b) := by
  change realTrace (balancedDensity S Z * balancedKraus B Z a * balancedKraus B Z b) = _
  unfold balancedDensity balancedKraus
  calc
    _ = realTrace (transportInverseSqrt Z * S * (transportInverseSqrt Z * CFC.sqrt Z) *
        B a * (CFC.sqrt Z * CFC.sqrt Z) * B b * CFC.sqrt Z) := by
      simp only [Matrix.mul_assoc]
    _ = realTrace (transportInverseSqrt Z * S * B a * Z * B b * CFC.sqrt Z) := by
      rw [transportInverseSqrt_mul_sqrt hZ, Matrix.mul_one,
        CFC.sqrt_mul_sqrt_self Z hZ.posSemidef.nonneg]
    _ = realTrace ((CFC.sqrt Z * transportInverseSqrt Z) * S * B a * Z * B b) := by
      simpa only [Matrix.mul_assoc] using realTrace_mul_comm
        (transportInverseSqrt Z * S * B a * Z * B b) (CFC.sqrt Z)
    _ = _ := by rw [sqrt_mul_transportInverseSqrt hZ, Matrix.one_mul]

/-- The trace of the actual balanced real Gram is the fixed-point trace. -/
theorem balanced_physicalGram_trace (B : ι → Matrix n n ℂ)
    (hB : ∀ a, (B a).IsHermitian) {S Z : Matrix n n ℂ}
    (hZ : Z.PosDef) (htransport : Z * krausChannel B S * Z = S) :
    realTrace (physicalRealGram (balancedDensity S Z) (balancedKraus B Z)) =
      realTrace (balancedDensity S Z) := by
  have hfix := balancedKraus_fixedPoint B hZ htransport
  have hD := balancedKraus_isHermitian B hB Z
  have ht := realTrace_kraus_sum (balancedKraus B Z) (balancedDensity S Z)
  have hchannel : (∑ a, balancedKraus B Z a * balancedDensity S Z * balancedKraus B Z a) =
      balancedDensity S Z := by
    simpa only [krausChannel, fun a => (hD a).eq] using hfix
  rw [hchannel] at ht
  rw [ht]
  change (∑ a, realTrace (balancedDensity S Z * balancedKraus B Z a * balancedKraus B Z a)) = _
  simp only [Matrix.mul_sum, realTrace_sum, Matrix.mul_assoc]

/-- All basic balanced-frame identities hold for the explicitly constructed transport. -/
theorem balancedTransport_actual_data (B : ι → Matrix n n ℂ)
    (hB : ∀ a, (B a).IsHermitian) {S : Matrix n n ℂ} (hS : S.PosDef)
    (hM : (krausChannel B S).PosDef) :
    let Z := transportOptimizer S (krausChannel B S)
    (balancedDensity S Z).PosDef ∧ (balancedRoot S Z).PosDef ∧
      (∀ a, (balancedKraus B Z a).IsHermitian) ∧
      krausChannel (balancedKraus B Z) (balancedDensity S Z) = balancedDensity S Z ∧
      realTrace (balancedDensity S Z) = fidelity S (krausChannel B S) ∧
      realTrace (balancedRoot S Z * balancedRoot S Z) ≤ realTrace (krausChannel B S) := by
  dsimp only
  have hZ := transportOptimizer_posDef hS hM
  have htrans := transportOptimizer_solve hS hM
  exact ⟨balancedDensity_posDef hS hZ, balancedRoot_posDef hS hZ,
    balancedKraus_isHermitian B hB _, balancedKraus_fixedPoint B hZ htrans,
    realTrace_balancedDensity_actual B hS hM,
    realTrace_balancedRoot_square_le hS.posSemidef hZ htrans⟩

end MatrixSpencer
