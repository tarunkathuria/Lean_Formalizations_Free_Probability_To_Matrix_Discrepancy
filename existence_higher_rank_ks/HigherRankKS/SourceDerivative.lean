import HigherRankKS.CarrierMetric
import HigherRankKS.SourceSmoothness
import HigherRankKS.SourceBudget
import MatrixSpencer.KSSpinSource

/-!
# The actual fixed-probe derivative of one source atom

The output probe stays fixed. Fixed carrier compression reduces the derivative
to a positive-definite carrier even when the original atom is singular.
-/

open Matrix MatrixSpencer Filter Topology Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff

noncomputable section
namespace HigherRankKS.SourceDerivative

variable {n : Type*} [Fintype n] [DecidableEq n]
local instance sourceDerivativeCStar {m : Type*} [Fintype m] [DecidableEq m] :
    CStarAlgebra (Matrix m m ℂ) := {}

/-- The scalar trace probe on ambient matrices as an actual continuous linear map. -/
def traceProbeCLM (W : Matrix n n ℂ) : Matrix n n ℂ →L[ℝ] ℝ :=
  (realTraceCLM (n := n)).comp (LinearMap.mulLeft ℝ W).toContinuousLinearMap

omit [DecidableEq n] in
@[simp] theorem traceProbeCLM_apply (W X : Matrix n n ℂ) :
    traceProbeCLM W X = realTrace (W * X) := rfl

/-- The old supported transport is extended by zero, and held fixed here. -/
def probe (β : ℝ) (A : Matrix n n ℂ) (Z : Matrix (n ⊕ n) (n ⊕ n) ℂ)
    (S : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ)) : ℝ :=
  realTrace (Z * sourceTerm β A (S : Matrix _ _ ℂ))

/-- The corresponding positive output probe on the fixed carrier of the atom. -/
def compressedProbe (A : Matrix n n ℂ) (Z : Matrix (n ⊕ n) (n ⊕ n) ℂ) :
    Matrix (AtomCarrierIndex A) (AtomCarrierIndex A) ℂ :=
  (CFC.sqrt A * atomEmbedding A)ᴴ * marginal Z * (CFC.sqrt A * atomEmbedding A)

theorem compressedProbe_posSemidef (A : Matrix n n ℂ)
    {Z : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hZ : Z.PosSemidef) :
    (compressedProbe A Z).PosSemidef :=
  (marginal_posSemidef hZ).conjTranspose_mul_mul_same _

theorem realTrace_mul_sourceTerm (β : ℝ) (A : Matrix n n ℂ)
    (Z S : Matrix (n ⊕ n) (n ⊕ n) ℂ) :
    realTrace (Z * sourceTerm β A S) = realTrace (marginal Z * sourceBlock β A S) := by
  rw [realTrace_mul_comm Z, realTrace_mul_comm (marginal Z)]
  exact congrArg Complex.re (KSSpinSource.doubled_trace_mul (sourceBlock β A S) Z)

theorem probe_eq_compressed (A : Matrix n n ℂ) (Z : Matrix (n ⊕ n) (n ⊕ n) ℂ)
    (k : ℕ) (hk : 1 ≤ k) (S : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ))
    (hS : (S : Matrix (n ⊕ n) (n ⊕ n) ℂ).PosSemidef) :
    probe ((1 : ℝ) / (2 : ℝ) ^ k) A Z S =
      realTrace (compressedProbe A Z * CarrierMetric.carrier ((1 : ℝ) / (2 : ℝ) ^ k)
        (compressedCarrierCLM A S)) := by
  rw [probe, realTrace_mul_sourceTerm, sourceBlock, carrierPower_reconstruct A hS k hk]
  have he : CFC.sqrt A * (atomEmbedding A *
      carrierPower ((1 : ℝ) / (2 : ℝ) ^ k) (compressedCarrier A (S : Matrix _ _ ℂ)) *
      (atomEmbedding A)ᴴ) * CFC.sqrt A =
      (CFC.sqrt A * atomEmbedding A) *
      carrierPower ((1 : ℝ) / (2 : ℝ) ^ k) (compressedCarrier A (S : Matrix _ _ ℂ)) *
      (CFC.sqrt A * atomEmbedding A)ᴴ := by
    simp only [Matrix.conjTranspose_mul, (CFC.sqrt_nonneg A).posSemidef.isHermitian.eq,
      Matrix.mul_assoc]
  rw [he, realTrace_mul_comm]
  rw [KSSafeRetirement.realTrace_embedded_mul, realTrace_mul_comm]
  simp only [compressedProbe, CarrierMetric.carrier, compressedCarrierCLM_coe]

theorem contDiffAt_probe (A : Matrix n n ℂ) (Z : Matrix (n ⊕ n) (n ⊕ n) ℂ)
    (k : ℕ) (hk : 1 ≤ k) (S : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ))
    (hS : (S : Matrix (n ⊕ n) (n ⊕ n) ℂ).PosDef) :
    ContDiffAt ℝ ∞ (probe ((1 : ℝ) / (2 : ℝ) ^ k) A Z) S :=
  (traceProbeCLM Z).contDiff.contDiffAt.comp S (contDiffAt_sourceTerm A k hk S hS)

private theorem dyadic_mem_Ioo (k : ℕ) (hk : 1 ≤ k) :
    (1 : ℝ) / (2 : ℝ) ^ k ∈ Ioo (0 : ℝ) 1 := by
  constructor
  · positivity
  · apply (div_lt_one (by positivity : 0 < (2 : ℝ) ^ k)).mpr
    exact one_lt_pow₀ (by norm_num) (Nat.ne_of_gt hk)

/-- The complete derivative chain is proved on a neighborhood of the faithful density. -/
theorem hasFDerivAt_probe (A : Matrix n n ℂ) (Z : Matrix (n ⊕ n) (n ⊕ n) ℂ)
    (k : ℕ) (hk : 1 ≤ k) (S : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ))
    (hS : (S : Matrix (n ⊕ n) (n ⊕ n) ℂ).PosDef) :
    HasFDerivAt (probe ((1 : ℝ) / (2 : ℝ) ^ k) A Z)
      ((traceProbeCLM (compressedProbe A Z)).comp
        ((fderiv ℝ (CarrierMetric.carrier ((1 : ℝ) / (2 : ℝ) ^ k))
          (compressedCarrierCLM A S)).comp (compressedCarrierCLM A))) S := by
  have hm : (compressedCarrierCLM A S : Matrix (AtomCarrierIndex A) (AtomCarrierIndex A) ℂ).PosDef := by
    rw [compressedCarrierCLM_coe]
    exact compressedCarrier_posDef A hS
  have hd := (traceProbeCLM (compressedProbe A Z)).hasFDerivAt.comp S
    (((CarrierMetric.smooth (dyadic_mem_Ioo k hk) (compressedCarrierCLM A S) hm).differentiableAt
      (by simp)).hasFDerivAt.comp S (compressedCarrierCLM A).hasFDerivAt)
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventually_posDef_of_posDef S hS] with X hX
  exact probe_eq_compressed A Z k hk X hX.posSemidef

theorem fderiv_probe_apply (A : Matrix n n ℂ) (Z : Matrix (n ⊕ n) (n ⊕ n) ℂ)
    (k : ℕ) (hk : 1 ≤ k) (S U : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ))
    (hS : (S : Matrix (n ⊕ n) (n ⊕ n) ℂ).PosDef) :
    fderiv ℝ (probe ((1 : ℝ) / (2 : ℝ) ^ k) A Z) S U =
      realTrace (compressedProbe A Z * CarrierMetric.first ((1 : ℝ) / (2 : ℝ) ^ k)
        (compressedCarrierCLM A S) (compressedCarrierCLM A U)) := by
  rw [(hasFDerivAt_probe A Z k hk S hS).fderiv]
  rfl

/-- Euler's identity for the actual nonlinear source scalarization. -/
theorem probe_euler (A : Matrix n n ℂ) (Z : Matrix (n ⊕ n) (n ⊕ n) ℂ)
    (k : ℕ) (hk : 1 ≤ k) (S : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ))
    (hS : (S : Matrix (n ⊕ n) (n ⊕ n) ℂ).PosDef) :
    fderiv ℝ (probe ((1 : ℝ) / (2 : ℝ) ^ k) A Z) S S =
      probe ((1 : ℝ) / (2 : ℝ) ^ k) A Z S := by
  have hm : (compressedCarrierCLM A S : Matrix (AtomCarrierIndex A) (AtomCarrierIndex A) ℂ).PosDef := by
    rw [compressedCarrierCLM_coe]
    exact compressedCarrier_posDef A hS
  rw [fderiv_probe_apply A Z k hk S S hS,
    CarrierMetric.first_radial (dyadic_mem_Ioo k hk) _ hm]
  exact (probe_eq_compressed A Z k hk S hS.posSemidef).symm

/-- The carrier trace equals the physical atom mass in every positive density direction. -/
theorem realTrace_compressedCarrier (A : Matrix n n ℂ) (hA : A.PosSemidef)
    {T : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hT : T.PosSemidef) :
    realTrace (compressedCarrier A T) = realTrace (spinAtom A * T) := by
  have h := realTrace_isometry_embedding (atomEmbedding A) (atomEmbedding_isometry A)
    (compressedCarrier A T)
  rw [carrier_reconstruct A hT, realTrace_carrier hA] at h
  have hs : realTrace (spinAtom A * T) = realTrace (A * marginal T) :=
    congrArg Complex.re (KSSpinSource.doubled_trace_mul A T)
  exact h.symm.trans hs.symm

/-- Every nonzero PSD atom has strictly positive mass at a faithful density. -/
theorem atom_mass_pos {A : Matrix n n ℂ} (hA : A.PosSemidef) (hA0 : A ≠ 0)
    {S : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hS : S.PosDef) :
    0 < realTrace (spinAtom A * S) := by
  have hn : Nonempty (AtomCarrierIndex A) := by
    by_contra hn
    haveI : IsEmpty (AtomCarrierIndex A) := not_nonempty_iff.mp hn
    have hz : atomEmbedding A * compressedAtom A * (atomEmbedding A)ᴴ = 0 := by
      ext i j
      simp [Matrix.mul_apply]
    exact hA0 ((atom_reconstruct hA).symm.trans hz)
  letI := hn
  rw [← realTrace_compressedCarrier A hA hS.posSemidef]
  exact (Complex.pos_iff.mp (compressedCarrier_posDef A hS).trace_pos).1

/-- The actual positive-direction derivative lower bound needed by the endpoint certificate. -/
theorem probe_derivative_lower (A : Matrix n n ℂ) (hA : A.PosSemidef)
    (Z : Matrix (n ⊕ n) (n ⊕ n) ℂ) (hZ : Z.PosSemidef)
    (k : ℕ) (hk : 1 ≤ k) (S T : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ))
    (hS : (S : Matrix (n ⊕ n) (n ⊕ n) ℂ).PosDef)
    (hT : (T : Matrix (n ⊕ n) (n ⊕ n) ℂ).PosSemidef)
    (hp : 0 < realTrace (spinAtom A * (S : Matrix _ _ ℂ))) :
    ((1 : ℝ) / (2 : ℝ) ^ k) *
      (probe ((1 : ℝ) / (2 : ℝ) ^ k) A Z S /
        realTrace (spinAtom A * (S : Matrix _ _ ℂ))) *
      realTrace (spinAtom A * (T : Matrix _ _ ℂ)) ≤
      fderiv ℝ (probe ((1 : ℝ) / (2 : ℝ) ^ k) A Z) S T := by
  have hm : (compressedCarrierCLM A S : Matrix (AtomCarrierIndex A) (AtomCarrierIndex A) ℂ).PosDef := by
    rw [compressedCarrierCLM_coe]
    exact compressedCarrier_posDef A hS
  have ht : (compressedCarrierCLM A T : Matrix (AtomCarrierIndex A) (AtomCarrierIndex A) ℂ).PosSemidef := by
    rw [compressedCarrierCLM_coe]
    exact compressedCarrier_posSemidef A hT
  have hn : Nonempty (AtomCarrierIndex A) := by
    by_contra hn
    haveI : IsEmpty (AtomCarrierIndex A) := not_nonempty_iff.mp hn
    have hz : realTrace (compressedCarrier A (S : Matrix _ _ ℂ)) = 0 := by simp [realTrace, Matrix.trace]
    rw [realTrace_compressedCarrier A hA hS.posSemidef] at hz
    linarith
  letI := hn
  have h := CarrierMetric.trace_first_lower (dyadic_mem_Ioo k hk)
    (compressedCarrierCLM A S) (compressedCarrierCLM A T) hm ht
    (compressedProbe A Z) (compressedProbe_posSemidef A hZ)
  rw [← probe_eq_compressed A Z k hk S hS.posSemidef,
    ← fderiv_probe_apply A Z k hk S T hS, compressedCarrierCLM_coe,
    compressedCarrierCLM_coe, realTrace_compressedCarrier A hA hS.posSemidef,
    realTrace_compressedCarrier A hA hT] at h
  exact h

end HigherRankKS.SourceDerivative
