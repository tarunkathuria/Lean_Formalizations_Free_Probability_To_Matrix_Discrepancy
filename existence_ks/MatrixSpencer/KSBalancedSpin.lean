import MatrixSpencer.BalancedTransport
import MatrixSpencer.KSFisher
import MatrixSpencer.KSMovingOwnerHessian
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute

/-!
# Actual balanced trace-and-prepare source

The atoms below are constructed from the positive transport and the original
positive source atoms. No rank-one identity is imposed on the balanced atoms.
-/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

noncomputable section
namespace MatrixSpencer.KSBalancedSpin

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
local instance : CStarAlgebra (Matrix n n ℂ) := {}

def source (B : ι → Matrix n n ℂ) (c : ι → ℝ) (X : Matrix n n ℂ) : Matrix n n ℂ :=
  ∑ i, (c i * realTrace (B i * X)) • B i

def atom (B : ι → Matrix n n ℂ) (c : ι → ℝ) (Z : Matrix n n ℂ)
    (i : ι) : Matrix n n ℂ := Real.sqrt (c i) • balancedKraus B Z i

def mass (B : ι → Matrix n n ℂ) (c : ι → ℝ) (S Z : Matrix n n ℂ)
    (i : ι) : ℝ := realTrace (balancedDensity S Z * atom B c Z i)

omit [Fintype ι] in
theorem realTrace_mul_pos_of_posDef {P A : Matrix n n ℂ}
    (hP : P.PosDef) (hA : A.PosSemidef) (hne : A ≠ 0) :
    0 < realTrace (P * A) := by
  have hnonneg := realTrace_mul_nonneg hP.posSemidef hA
  refine lt_of_le_of_ne hnonneg ?_
  intro hz
  have hcong : (CFC.sqrt P * A * CFC.sqrt P).PosSemidef := by
    simpa only [hP.posDef_sqrt.isHermitian.eq] using
      hA.conjTranspose_mul_mul_same (CFC.sqrt P)
  have ht : realTrace (CFC.sqrt P * A * CFC.sqrt P) = 0 := by
    rw [realTrace_mul_cycle, CFC.sqrt_mul_sqrt_self P hP.posSemidef.nonneg,
      realTrace_mul_comm]
    simpa only [realTrace_mul_comm A P] using hz.symm
  have hzero := posSemidef_eq_zero_of_realTrace_eq_zero hcong ht
  have hleft : CFC.sqrt P * A = 0 := hP.posDef_sqrt.isUnit.mul_right_cancel (by
    simpa only [Matrix.zero_mul] using hzero)
  exact hne (hP.posDef_sqrt.isUnit.mul_left_cancel (by
    simpa only [Matrix.mul_zero] using hleft))

theorem atom_posSemidef (B : ι → Matrix n n ℂ) (c : ι → ℝ)
    (hB : ∀ i, (B i).PosSemidef) (Z : Matrix n n ℂ) (i : ι) :
    (atom B c Z i).PosSemidef := by
  apply Matrix.PosSemidef.smul _ (Real.sqrt_nonneg _)
  simpa only [balancedKraus, (CFC.sqrt_nonneg Z).posSemidef.isHermitian.eq] using
    (hB i).conjTranspose_mul_mul_same (CFC.sqrt Z)

theorem trace_atom (B : ι → Matrix n n ℂ) (c : ι → ℝ)
    {Z : Matrix n n ℂ} (hZ : Z.PosDef) (i : ι) :
    realTrace (atom B c Z i) = Real.sqrt (c i) * realTrace (Z * B i) := by
  rw [atom, realTrace_smul]
  unfold balancedKraus
  rw [realTrace_mul_cycle, CFC.sqrt_mul_sqrt_self Z hZ.posSemidef.nonneg,
    realTrace_mul_comm]

theorem trace_balanced_pair (S : Matrix n n ℂ) (B : Matrix n n ℂ)
    {Z : Matrix n n ℂ} (hZ : Z.PosDef) :
    realTrace (balancedDensity S Z * (CFC.sqrt Z * B * CFC.sqrt Z)) =
      realTrace (S * B) := by
  unfold balancedDensity
  calc
    _ = realTrace (transportInverseSqrt Z * S *
        (transportInverseSqrt Z * CFC.sqrt Z) * B * CFC.sqrt Z) := by
      simp only [Matrix.mul_assoc]
    _ = realTrace (transportInverseSqrt Z * S * B * CFC.sqrt Z) := by
      rw [transportInverseSqrt_mul_sqrt hZ, Matrix.mul_one]
    _ = realTrace ((CFC.sqrt Z * transportInverseSqrt Z) * S * B) := by
      simpa only [Matrix.mul_assoc] using realTrace_mul_comm
        (transportInverseSqrt Z * S * B) (CFC.sqrt Z)
    _ = _ := by rw [sqrt_mul_transportInverseSqrt hZ, Matrix.one_mul]

theorem mass_eq (B : ι → Matrix n n ℂ) (c : ι → ℝ)
    (S : Matrix n n ℂ) {Z : Matrix n n ℂ} (hZ : Z.PosDef) (i : ι) :
    mass B c S Z i = Real.sqrt (c i) * realTrace (S * B i) := by
  rw [mass, atom, Matrix.mul_smul, realTrace_smul]
  rw [balancedKraus, trace_balanced_pair S (B i) hZ]

theorem trace_atom_pos (B : ι → Matrix n n ℂ) (c : ι → ℝ)
    (hB : ∀ i, (B i).PosSemidef) (hBne : ∀ i, B i ≠ 0)
    (hc : ∀ i, 0 < c i) {Z : Matrix n n ℂ} (hZ : Z.PosDef) (i : ι) :
    0 < realTrace (atom B c Z i) := by
  rw [trace_atom B c hZ]
  exact mul_pos (Real.sqrt_pos.mpr (hc i)) (realTrace_mul_pos_of_posDef hZ (hB i) (hBne i))

theorem mass_pos (B : ι → Matrix n n ℂ) (c : ι → ℝ)
    (hB : ∀ i, (B i).PosSemidef) (hBne : ∀ i, B i ≠ 0)
    (hc : ∀ i, 0 < c i) {S Z : Matrix n n ℂ} (hS : S.PosDef)
    (hZ : Z.PosDef) (i : ι) : 0 < mass B c S Z i := by
  rw [mass_eq B c S hZ]
  exact mul_pos (Real.sqrt_pos.mpr (hc i)) (realTrace_mul_pos_of_posDef hS (hB i) (hBne i))

/-- The trace-and-prepare transport equation gives the exact Fisher fixed point. -/
theorem balancedDensity_eq_sum (B : ι → Matrix n n ℂ) (c : ι → ℝ)
    (hc : ∀ i, 0 ≤ c i) {S Z : Matrix n n ℂ} (hZ : Z.PosDef)
    (htransport : Z * source B c S * Z = S) :
    balancedDensity S Z = ∑ i, mass B c S Z i • atom B c Z i := by
  rw [balancedDensity_eq_source_congruence hZ htransport]
  simp only [source, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [mass_eq B c S hZ, atom, smul_smul]
  have heq : Real.sqrt (c i) * realTrace (S * B i) * Real.sqrt (c i) =
      c i * realTrace (B i * S) := by
    rw [realTrace_mul_comm (S) (B i)]
    calc
      _ = (Real.sqrt (c i) * Real.sqrt (c i)) * realTrace (B i * S) := by ring
      _ = _ := by rw [Real.mul_self_sqrt (hc i)]
  rw [heq]
  rfl

/-- All ordinary Gram assumptions follow from actual positive transport data. -/
theorem actual_gram_contraction [DecidableEq ι]
    (B : ι → Matrix n n ℂ) (c : ι → ℝ)
    (hB : ∀ i, (B i).PosSemidef) (hBne : ∀ i, B i ≠ 0)
    (hc : ∀ i, 0 < c i) {S Z : Matrix n n ℂ} (hS : S.PosDef)
    (hZ : Z.PosDef) (htransport : Z * source B c S * Z = S) :
    0 ≤ KSFisher.gram (atom B c Z) ∧ KSFisher.gram (atom B c Z) ≤ 1 := by
  exact KSFisher.gram_contraction (atom B c Z) (atom_posSemidef B c hB Z)
    (mass B c S Z) (mass_pos B c hB hBne hc hS hZ)
    (balancedDensity_eq_sum B c (fun i => (hc i).le) hZ htransport) (fun _ => rfl)

theorem atom_commute (B : ι → Matrix n n ℂ) (c : ι → ℝ)
    {J Z : Matrix n n ℂ} (hJZ : J * Z = Z * J)
    (hJB : ∀ i, J * B i = B i * J) (i : ι) :
    J * atom B c Z i = atom B c Z i * J := by
  have hsq : J * CFC.sqrt Z = CFC.sqrt Z * J := by
    exact ((show Commute Z J from hJZ.symm).cfcₙ_nnreal NNReal.sqrt).symm.eq
  simp only [atom, balancedKraus, Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  calc
    _ = (J * CFC.sqrt Z) * B i * CFC.sqrt Z := by simp only [Matrix.mul_assoc]
    _ = CFC.sqrt Z * (J * B i) * CFC.sqrt Z := by rw [hsq]; simp only [Matrix.mul_assoc]
    _ = CFC.sqrt Z * B i * (J * CFC.sqrt Z) := by rw [hJB]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [hsq]; simp only [Matrix.mul_assoc]

def liftTransport (Z Y : Matrix n n ℂ) : Matrix n n ℂ := CFC.sqrt Z * Y * CFC.sqrt Z

theorem liftTransport_isHermitian (Z : Matrix n n ℂ) {Y : Matrix n n ℂ}
    (hY : Y.IsHermitian) : (liftTransport Z Y).IsHermitian := by
  simpa only [liftTransport, (CFC.sqrt_nonneg Z).posSemidef.isHermitian.eq] using
    Matrix.isHermitian_conjTranspose_mul_mul (CFC.sqrt Z) hY

theorem liftTransport_injective {Z : Matrix n n ℂ} (hZ : Z.PosDef) :
    Function.Injective (liftTransport Z) := by
  intro Y W heq
  exact hZ.posDef_sqrt.isUnit.mul_left_cancel (hZ.posDef_sqrt.isUnit.mul_right_cancel heq)

theorem sqrt_mul_inverse_mul_sqrt {Z : Matrix n n ℂ} (hZ : Z.PosDef) :
    CFC.sqrt Z * Z⁻¹ * CFC.sqrt Z = 1 := by
  have hleft : CFC.sqrt Z * Z⁻¹ = transportInverseSqrt Z := by
    letI : Invertible Z := hZ.isUnit.invertible
    apply hZ.isUnit.mul_right_cancel
    rw [Matrix.mul_assoc, Matrix.inv_mul_of_invertible,
      Matrix.mul_one, transportInverseSqrt_mul_self_matrix hZ]
  rw [hleft, transportInverseSqrt_mul_sqrt hZ]

theorem liftTransport_inverse_term {Z : Matrix n n ℂ} (hZ : Z.PosDef)
    (Y : Matrix n n ℂ) :
    liftTransport Z (Z⁻¹ * liftTransport Z Y * Z⁻¹) = Y := by
  unfold liftTransport
  calc
    _ = (CFC.sqrt Z * Z⁻¹ * CFC.sqrt Z) * Y *
        (CFC.sqrt Z * Z⁻¹ * CFC.sqrt Z) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [sqrt_mul_inverse_mul_sqrt hZ, Matrix.one_mul, Matrix.mul_one]

theorem trace_liftTransport (Z B Y : Matrix n n ℂ) :
    realTrace (B * liftTransport Z Y) = realTrace (liftTransport Z B * Y) := by
  unfold liftTransport
  simpa only [Matrix.mul_assoc] using
    realTrace_mul_comm (B * CFC.sqrt Z * Y) (CFC.sqrt Z)

/-- Exact intertwining of the physical source with the balanced prepare map. -/
theorem liftTransport_source (B : ι → Matrix n n ℂ) (c : ι → ℝ)
    (hc : ∀ i, 0 ≤ c i) (Z Y : Matrix n n ℂ) :
    liftTransport Z (source B c (liftTransport Z Y)) =
      KSFisher.prepare (atom B c Z) Y := by
  simp only [liftTransport, source, KSFisher.prepare, KSFisher.synthesis,
    Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
    atom, balancedKraus, realTrace_smul, smul_smul]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  have htrace := trace_liftTransport Z (B i) Y
  change realTrace (B i * (CFC.sqrt Z * Y * CFC.sqrt Z)) =
    realTrace (CFC.sqrt Z * B i * CFC.sqrt Z * Y) at htrace
  rw [htrace]
  calc
    _ = (Real.sqrt (c i) * Real.sqrt (c i)) *
      realTrace (CFC.sqrt Z * B i * CFC.sqrt Z * Y) := by rw [Real.mul_self_sqrt (hc i)]
    _ = _ := by ring

/-- A balanced source completion annihilates the actual physical center velocity. -/
theorem physical_velocity_zero_of_completion
    (B : ι → Matrix n n ℂ) (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    {Z : Matrix n n ℂ} (hZ : Z.PosDef) (K V Y : Matrix n n ℂ)
    (hcompletion : Y - KSFisher.prepare (atom B c Z) Y = liftTransport Z (K + V)) :
    K + V - Z⁻¹ * liftTransport Z Y * Z⁻¹ + source B c (liftTransport Z Y) = 0 := by
  apply liftTransport_injective hZ
  simp only [liftTransport, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_zero, Matrix.zero_mul]
  change liftTransport Z K + liftTransport Z V -
    liftTransport Z (Z⁻¹ * liftTransport Z Y * Z⁻¹) +
    liftTransport Z (source B c (liftTransport Z Y)) = 0
  rw [liftTransport_inverse_term hZ, liftTransport_source B c hc]
  have hadd : liftTransport Z K + liftTransport Z V = liftTransport Z (K + V) := by
    simp only [liftTransport, Matrix.mul_add, Matrix.add_mul]
  rw [hadd, ← hcompletion]
  abel

theorem inverse_acceleration_pairing (S : Matrix n n ℂ) {Z : Matrix n n ℂ}
    (hZ : Z.PosDef) (Y : Matrix n n ℂ) :
    realTrace (S * (Z⁻¹ * liftTransport Z Y * Z⁻¹ * liftTransport Z Y * Z⁻¹)) =
      realTrace (balancedDensity S Z * (Y * Y)) := by
  have hi : Z⁻¹ * CFC.sqrt Z = transportInverseSqrt Z := by
    letI : Invertible Z := hZ.isUnit.invertible
    apply hZ.isUnit.mul_left_cancel
    rw [← Matrix.mul_assoc, Matrix.mul_inv_of_invertible, Matrix.one_mul,
      matrix_mul_transportInverseSqrt hZ]
  have hj : CFC.sqrt Z * Z⁻¹ = transportInverseSqrt Z := by
    letI : Invertible Z := hZ.isUnit.invertible
    apply hZ.isUnit.mul_right_cancel
    rw [Matrix.mul_assoc, Matrix.inv_mul_of_invertible, Matrix.mul_one,
      transportInverseSqrt_mul_self_matrix hZ]
  have heq : Z⁻¹ * liftTransport Z Y * Z⁻¹ * liftTransport Z Y * Z⁻¹ =
      transportInverseSqrt Z * (Y * Y) * transportInverseSqrt Z := by
    unfold liftTransport
    calc
      _ = (Z⁻¹ * CFC.sqrt Z) * Y * (CFC.sqrt Z * Z⁻¹ * CFC.sqrt Z) *
          Y * (CFC.sqrt Z * Z⁻¹) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [sqrt_mul_inverse_mul_sqrt hZ, hi, hj, Matrix.mul_one];
                  simp only [Matrix.mul_assoc]
  rw [heq]
  unfold balancedDensity
  simpa only [Matrix.mul_assoc] using
    realTrace_mul_comm (S * transportInverseSqrt Z * (Y * Y)) (transportInverseSqrt Z)

section LegalCompletion
variable [DecidableEq ι]

theorem synthesis_add (D : ι → Matrix n n ℂ) (x y : ι → ℝ) :
    KSFisher.synthesis D (x + y) = KSFisher.synthesis D x + KSFisher.synthesis D y := by
  simp only [KSFisher.synthesis, Pi.add_apply, add_smul, Finset.sum_add_distrib]

theorem synthesis_sub (D : ι → Matrix n n ℂ) (x y : ι → ℝ) :
    KSFisher.synthesis D (x - y) = KSFisher.synthesis D x - KSFisher.synthesis D y := by
  simp only [KSFisher.synthesis, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]

theorem prepare_add (D : ι → Matrix n n ℂ) (Y W : Matrix n n ℂ) :
    KSFisher.prepare D (Y + W) = KSFisher.prepare D Y + KSFisher.prepare D W := by
  simp only [KSFisher.prepare, Matrix.mul_add, realTrace_add, KSFisher.synthesis,
    add_smul, Finset.sum_add_distrib]

theorem prepare_smul (D : ι → Matrix n n ℂ) (a : ℝ) (Y : Matrix n n ℂ) :
    KSFisher.prepare D (a • Y) = a • KSFisher.prepare D Y := by
  simp only [KSFisher.prepare, Matrix.mul_smul, realTrace_smul, KSFisher.synthesis,
    MulAction.mul_smul, Finset.smul_sum]

theorem prepare_spin_synthesis (D : ι → Matrix n n ℂ) (J : Matrix n n ℂ)
    (y : ι → ℝ) :
    KSFisher.prepare D (J * KSFisher.synthesis D y) =
      KSFisher.synthesis D (KSFisher.spinGram J D *ᵥ y) := by
  unfold KSFisher.prepare
  congr 1
  funext i
  exact (KSFisher.spinGram_mulVec J D y i).symm

def spinCompletion (D : ι → Matrix n n ℂ) (J : Matrix n n ℂ)
    (z δ y : ι → ℝ) : Matrix n n ℂ :=
  J * KSFisher.synthesis D y + KSFisher.synthesis D (δ - Matrix.diagonal z *ᵥ y)

/-- The finite legality equation retains the exact mixed-source cancellation. -/
theorem legal_cancellation (D : ι → Matrix n n ℂ) (J : Matrix n n ℂ)
    (z δ y : ι → ℝ)
    (hlegal : (1 - KSFisher.gram D) *ᵥ δ =
      (KSFisher.spinGram J D - KSFisher.gram D * Matrix.diagonal z) *ᵥ y) :
    KSFisher.spinGram J D *ᵥ y +
      KSFisher.gram D *ᵥ (δ - Matrix.diagonal z *ᵥ y) = δ := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec] at hlegal
  rw [Matrix.mulVec_sub]
  funext i
  have hi := congrFun hlegal i
  simp only [Pi.sub_apply, Pi.add_apply] at hi ⊢
  linarith

theorem prepare_spinCompletion (D : ι → Matrix n n ℂ) (J : Matrix n n ℂ)
    (z δ y : ι → ℝ)
    (hlegal : (1 - KSFisher.gram D) *ᵥ δ =
      (KSFisher.spinGram J D - KSFisher.gram D * Matrix.diagonal z) *ᵥ y) :
    KSFisher.prepare D (spinCompletion D J z δ y) = KSFisher.synthesis D δ := by
  rw [spinCompletion, prepare_add, prepare_spin_synthesis, KSFisher.prepare_synthesis,
    ← synthesis_add, legal_cancellation D J z δ y hlegal]

/-- Exact balanced completion, with no inverse of the singular Gram defect. -/
theorem spinCompletion_defect (D : ι → Matrix n n ℂ) (J : Matrix n n ℂ)
    (z δ y : ι → ℝ) (a : ℝ)
    (hlegal : (1 - KSFisher.gram D) *ᵥ δ =
      (KSFisher.spinGram J D - KSFisher.gram D * Matrix.diagonal z) *ᵥ y) :
    a • spinCompletion D J z δ y - KSFisher.prepare D (a • spinCompletion D J z δ y) =
      a • (J * KSFisher.synthesis D y - KSFisher.synthesis D (Matrix.diagonal z *ᵥ y)) := by
  rw [prepare_smul, prepare_spinCompletion D J z δ y hlegal, ← smul_sub,
    spinCompletion, synthesis_sub]
  congr 1
  abel

theorem spinCompletion_probe (D : ι → Matrix n n ℂ) (J : Matrix n n ℂ)
    (z δ y : ι → ℝ)
    (hlegal : (1 - KSFisher.gram D) *ᵥ δ =
      (KSFisher.spinGram J D - KSFisher.gram D * Matrix.diagonal z) *ᵥ y)
    (i : ι) : realTrace (D i * spinCompletion D J z δ y) = δ i := by
  have hi := congrFun (legal_cancellation D J z δ y hlegal) i
  simpa only [Pi.add_apply, KSFisher.spinGram_mulVec, KSFisher.gram_mulVec,
    spinCompletion, Matrix.mul_add, realTrace_add] using hi

theorem spinCompletion_isHermitian (D : ι → Matrix n n ℂ)
    (hD : ∀ i, (D i).IsHermitian) {J : Matrix n n ℂ} (hJ : J.IsHermitian)
    (hc : ∀ i, J * D i = D i * J) (z δ y : ι → ℝ) :
    (spinCompletion D J z δ y).IsHermitian := by
  exact (KSFisher.spin_synthesis_isHermitian hJ D hD hc y).add
    (KSFisher.synthesis_isHermitian D hD _)

theorem spinCompletion_eq (D : ι → Matrix n n ℂ) (J : Matrix n n ℂ)
    (z δ y : ι → ℝ) : spinCompletion D J z δ y =
    J * KSFisher.synthesis D y - KSFisher.synthesis D (Matrix.diagonal z *ᵥ y) +
      KSFisher.synthesis D δ := by
  rw [spinCompletion, synthesis_sub]
  abel

end LegalCompletion

section PhysicalSpinCompletion
variable [DecidableEq ι]

def coefficientDirection (c : ι → ℝ) (a : ℝ) (y : ι → ℝ) : ι → ℝ :=
  fun i => a * Real.sqrt (c i) * y i

def physicalForce (B : ι → Matrix n n ℂ) (J : Matrix n n ℂ) (u : ℝ)
    (x h q : ι → ℝ) : Matrix n n ℂ :=
  (∑ i, h i • (J * B i)) + ∑ i, (-2 * u * x i * h i * q i) • B i

theorem liftTransport_physicalForce (B : ι → Matrix n n ℂ) (c : ι → ℝ)
    {Z J : Matrix n n ℂ} (hJZ : J * Z = Z * J)
    (u a : ℝ) (x q y : ι → ℝ) :
    liftTransport Z (physicalForce B J u x (coefficientDirection c a y) q) =
      a • (J * KSFisher.synthesis (atom B c Z) y -
        KSFisher.synthesis (atom B c Z) (Matrix.diagonal (fun i => 2 * u * x i * q i) *ᵥ y)) := by
  have hsq : CFC.sqrt Z * J = J * CFC.sqrt Z :=
    ((show Commute Z J from hJZ.symm).cfcₙ_nnreal NNReal.sqrt).eq
  have hfirst : liftTransport Z (∑ i, coefficientDirection c a y i • (J * B i)) =
      a • (J * KSFisher.synthesis (atom B c Z) y) := by
    simp only [liftTransport, coefficientDirection, KSFisher.synthesis, atom, balancedKraus,
      Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
      smul_smul, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hmat : CFC.sqrt Z * (J * B i) * CFC.sqrt Z =
        J * (CFC.sqrt Z * B i * CFC.sqrt Z) := by
      rw [← Matrix.mul_assoc (CFC.sqrt Z) J, hsq]
      simp only [Matrix.mul_assoc]
    rw [hmat]
    congr 1
    ring
  have hsecond : liftTransport Z (∑ i,
      (-2 * u * x i * coefficientDirection c a y i * q i) • B i) =
      -a • KSFisher.synthesis (atom B c Z)
        (Matrix.diagonal (fun i => 2 * u * x i * q i) *ᵥ y) := by
    simp only [liftTransport, coefficientDirection, KSFisher.synthesis, atom, balancedKraus,
      Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mulVec_diagonal, smul_smul, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    ring
  change liftTransport Z ((_ : Matrix n n ℂ) + _) = _
  have hadd : ∀ K V : Matrix n n ℂ,
      liftTransport Z (K + V) = liftTransport Z K + liftTransport Z V := by
    intros; simp only [liftTransport, Matrix.mul_add, Matrix.add_mul]
  rw [hadd, hfirst, hsecond, neg_smul, ← sub_eq_add_neg, ← smul_sub]

/-- Every finite legal pair produces an actual zero velocity of the physical
moving-transport majorant, for the exact natural owner derivative. -/
theorem physical_spin_velocity_zero
    (B : ι → Matrix n n ℂ) (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    {Z J : Matrix n n ℂ} (hZ : Z.PosDef) (hJZ : J * Z = Z * J)
    (u a : ℝ) (x q δ y : ι → ℝ)
    (hlegal : (1 - KSFisher.gram (atom B c Z)) *ᵥ δ =
      (KSFisher.spinGram J (atom B c Z) - KSFisher.gram (atom B c Z) *
        Matrix.diagonal (fun i => 2 * u * x i * q i)) *ᵥ y) :
    let W := a • spinCompletion (atom B c Z) J (fun i => 2 * u * x i * q i) δ y
    physicalForce B J u x (coefficientDirection c a y) q -
      Z⁻¹ * liftTransport Z W * Z⁻¹ + source B c (liftTransport Z W) = 0 := by
  dsimp only
  have hcompletion := spinCompletion_defect (atom B c Z) J
    (fun i => 2 * u * x i * q i) δ y a hlegal
  rw [← liftTransport_physicalForce B c hJZ u a x q y] at hcompletion
  simpa only [add_zero] using physical_velocity_zero_of_completion B c hc hZ
    (physicalForce B J u x (coefficientDirection c a y) q) 0
    (a • spinCompletion (atom B c Z) J (fun i => 2 * u * x i * q i) δ y)
    (by simpa only [add_zero] using hcompletion)

end PhysicalSpinCompletion

section ActualCurvature

def physicalAcceleration (B : ι → Matrix n n ℂ) (Z U : Matrix n n ℂ)
    (u : ℝ) (x h q : ι → ℝ) : Matrix n n ℂ :=
  (2 : ℝ) • (Z⁻¹ * U * Z⁻¹ * U * Z⁻¹) +
    ∑ i, (-2 * u * h i ^ 2 * q i - 4 * u * x i * h i * realTrace (B i * U)) • B i

theorem physicalAcceleration_pairing (B : ι → Matrix n n ℂ)
    (S Z U : Matrix n n ℂ) (u : ℝ) (x h q : ι → ℝ) :
    realTrace (S * physicalAcceleration B Z U u x h q) =
      2 * (realTrace (S * (Z⁻¹ * U * Z⁻¹ * U * Z⁻¹)) -
        ∑ i, (u * h i ^ 2 * q i + 2 * u * x i * h i * realTrace (B i * U)) *
          realTrace (S * B i)) := by
  simp only [physicalAcceleration, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_sum,
    realTrace_add, realTrace_smul, realTrace_sum]
  rw [mul_sub, Finset.mul_sum]
  have hs : (∑ i, (-2 * u * h i ^ 2 * q i -
      4 * u * x i * h i * realTrace (B i * U)) * realTrace (S * B i)) =
      -(∑ i, 2 * ((u * h i ^ 2 * q i + 2 * u * x i * h i * realTrace (B i * U)) *
        realTrace (S * B i))) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intros; ring
  rw [hs]
  ring

theorem scaled_transport_probe (B : ι → Matrix n n ℂ) (c : ι → ℝ)
    (Z W : Matrix n n ℂ) (a : ℝ) (i : ι) :
    Real.sqrt (c i) * realTrace (B i * liftTransport Z (a • W)) =
      a * realTrace (atom B c Z i * W) := by
  rw [trace_liftTransport]
  simp only [liftTransport, Matrix.mul_smul, realTrace_smul, atom, balancedKraus,
    Matrix.smul_mul]
  ring

/-- The exact second derivative of the moving majorant in balanced coordinates.
The mixed source term is retained, and no bound on the density Hessian is assumed. -/
theorem normalized_acceleration_pairing (B : ι → Matrix n n ℂ) (c : ι → ℝ)
    (hc : ∀ i, 0 ≤ c i) (S : Matrix n n ℂ) {Z : Matrix n n ℂ} (hZ : Z.PosDef)
    (W : Matrix n n ℂ) (u a : ℝ) (ha : u * a ^ 2 = 1) (x y : ι → ℝ) :
    realTrace (S * physicalAcceleration B Z (liftTransport Z (a • W)) u x
      (coefficientDirection c a y) (fun i => realTrace (Z * B i))) =
      2 * (a ^ 2 * realTrace (balancedDensity S Z * (W * W)) -
        ∑ i, (realTrace (atom B c Z i) * mass B c S Z i * y i ^ 2 +
          2 * x i * realTrace (S * B i) * y i * realTrace (atom B c Z i * W))) := by
  rw [physicalAcceleration_pairing, inverse_acceleration_pairing S hZ]
  have hinv : realTrace (balancedDensity S Z * ((a • W) * (a • W))) =
      a ^ 2 * realTrace (balancedDensity S Z * (W * W)) := by
    simp only [Matrix.smul_mul, Matrix.mul_smul, realTrace_smul]
    ring
  rw [hinv]
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  have hsquare := Real.mul_self_sqrt (hc i)
  have hprobe := scaled_transport_probe B c Z W a i
  have hdirect : u * coefficientDirection c a y i ^ 2 * realTrace (Z * B i) *
      realTrace (S * B i) = realTrace (atom B c Z i) * mass B c S Z i * y i ^ 2 := by
    rw [trace_atom B c hZ, mass_eq B c S hZ]
    unfold coefficientDirection
    calc
      _ = (u * a ^ 2) * ((Real.sqrt (c i) * Real.sqrt (c i)) *
          realTrace (Z * B i) * realTrace (S * B i) * y i ^ 2) := by ring
      _ = _ := by rw [ha]; ring
  have hcross : 2 * u * x i * coefficientDirection c a y i *
      realTrace (B i * liftTransport Z (a • W)) * realTrace (S * B i) =
      2 * x i * realTrace (S * B i) * y i * realTrace (atom B c Z i * W) := by
    unfold coefficientDirection
    calc
      _ = 2 * u * x i * a * y i * realTrace (S * B i) *
        (Real.sqrt (c i) * realTrace (B i * liftTransport Z (a • W))) := by ring
      _ = 2 * (u * a ^ 2) * x i * realTrace (S * B i) * y i *
        realTrace (atom B c Z i * W) := by rw [hprobe]; ring
      _ = _ := by rw [ha]; ring
  rw [add_mul, hdirect, hcross]

end ActualCurvature
end MatrixSpencer.KSBalancedSpin
