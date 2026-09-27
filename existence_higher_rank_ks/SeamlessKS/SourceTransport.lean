import SeamlessKS.PhysicalDescent
import SeamlessKS.Source
import MatrixSpencer.KSSpinLocalState

/-!
# From actual vector atoms to the smooth-source legal transport direction

This module carries out source compression and all physical positivity
and symmetry arguments for arbitrary strictly positive scalar weights.
The formal slope parameter `χ` is independent of the actual position.
-/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace SeamlessKS.SourceTransport

open MatrixSpencer MatrixSpencer.KSSpinLocalState

variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
local instance {k : Type*} [Fintype k] [DecidableEq k] : CStarAlgebra (Matrix k k ℂ) := {}

/-- The optimizer transport on the actual fixed live source support. -/
def stateTransport (v : ι → n → ℂ) (c : ι → ℝ)
    (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) :=
  transportOptimizer (KSSupportSymmetry.compress (KSSpinCompression.embedding (atoms v)) S)
    (covarianceCompressedSource (KSSpinSource.family (atoms v))
      (KSSpinSource.coefficientCovariance c) S)

theorem stateTransport_posDef (v : ι → n → ℂ) {c : ι → ℝ}
    (hc : ∀ i, 0 < c i) {S : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hS : S.PosDef) :
    (stateTransport v c S).PosDef :=
  transportOptimizer_posDef
    (KSSupportSymmetry.compress_posDef _ (KSSpinCompression.embedding_isometry _) hS)
    (KSSpinCompression.compressed_source_posDef v hc hS)

theorem probe_pos (v : ι → n → ℂ) (hv : ∀ i, v i ≠ 0)
    {c : ι → ℝ} (hc : ∀ i, 0 < c i)
    {S : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hS : S.PosDef) (i : ι) :
    0 < realTrace (stateTransport v c S * KSSpinCompression.compressedAtom (atoms v) i) := by
  apply KSBalancedSpin.realTrace_mul_pos_of_posDef (stateTransport_posDef v hc hS)
    (KSSpinCompression.compressedAtom_posSemidef (atoms v)
      (fun j => KSRankOne.atom_posSemidef (v j)) i)
  exact KSSpinCompression.compressedAtom_ne_zero (atoms v)
    (fun j => KSRankOne.atom_isHermitian (v j)) i
    (fun hz => hv i ((KSRankOne.atom_eq_zero_iff (v i)).mp hz))

/-- All matrix-geometric premises of the negative legal direction follow
from the actual atoms and transport. Only the concrete scalar probe/slope
bounds, which are supplied by failed local tests, remain as hypotheses. -/
theorem actual_transport_descent [Nonempty ι]
    (v : ι → n → ℂ) (hv : ∀ i, v i ≠ 0)
    (c χ : ι → ℝ) (hc : ∀ i, 0 < c i)
    (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) (hS : S.PosDef)
    (hJS : KSSignSymmetry.conjugate KSSignSymmetry.signMatrix S = S)
    (hz : ∀ i, |128 * χ i * realTrace (stateTransport v c S *
      KSSpinCompression.compressedAtom (atoms v) i)| ≤ 1)
    (hsmall : ∀ i, c i * realTrace (stateTransport v c S *
      KSSpinCompression.compressedAtom (atoms v) i) ^ 2 ≤ (200 / 81 : ℝ) / 64) :
    let V := KSSpinCompression.embedding (atoms v)
    let B := KSSpinCompression.compressedAtom (atoms v)
    let J := KSSpinCompression.compressedSign (atoms v)
    let Z := stateTransport v c S
    ∃ h : ι → ℝ, ∃ U : Matrix (KSSpinCompression.supportIndex (atoms v))
        (KSSpinCompression.supportIndex (atoms v)) ℂ,
      h ≠ 0 ∧ U.IsHermitian ∧
      KSBalancedSpin.physicalForce B J 64 χ h (fun i => realTrace (Z * B i)) -
        Z⁻¹ * U * Z⁻¹ + KSBalancedSpin.source B c U = 0 ∧
      realTrace ((Vᴴ * S * V) * KSBalancedSpin.physicalAcceleration B Z U 64 χ h
        (fun i => realTrace (Z * B i))) < 0 := by
  let V := KSSpinCompression.embedding (atoms v)
  let B := KSSpinCompression.compressedAtom (atoms v)
  let S0 := KSSupportSymmetry.compress V S
  let M := covarianceCompressedSource (KSSpinSource.family (atoms v))
    (KSSpinSource.coefficientCovariance c) S
  let Z := stateTransport v c S
  have hS0 : S0.PosDef := KSSupportSymmetry.compress_posDef V
    (KSSpinCompression.embedding_isometry _) hS
  have hM : M.PosDef := KSSpinCompression.compressed_source_posDef v hc hS
  have hZ : Z.PosDef := stateTransport_posDef v hc hS
  have hBe : ∀ i, B i ≠ 0 := fun i => KSSpinCompression.compressedAtom_ne_zero (atoms v)
    (fun j => KSRankOne.atom_isHermitian (v j)) i
      (fun hz => hv i ((KSRankOne.atom_eq_zero_iff (v i)).mp hz))
  have hBp : ∀ i, (B i).PosSemidef := KSSpinCompression.compressedAtom_posSemidef (atoms v)
    (fun i => KSRankOne.atom_posSemidef (v i))
  have hsource : M = KSBalancedSpin.source B c S0 :=
    KSSpinCompression.compressed_source v c hS.isHermitian
  have hsolve : Z * KSBalancedSpin.source B c S0 * Z = S0 := by
    rw [← hsource]
    exact transportOptimizer_solve hS0 hM
  apply SeamlessKS.PhysicalDescent.exists_transport_descent B c hBp hBe hc hS0 hZ hsolve
    (KSSpinCompression.compressedSign_isHermitian (atoms v))
    (KSSpinCompression.compressedSign_sq (atoms v) (fun i => KSRankOne.atom_isHermitian (v i)))
    (KSSpinCompression.compressedSign_commute_transport v hc hS hJS).eq
    (fun i => (KSSpinCompression.compressedSign_commute_atom (atoms v)
      (fun j => KSRankOne.atom_isHermitian (v j)) i).eq) χ hz
  intro i
  rw [KSBalancedSpin.trace_atom B c hZ i, mul_pow, Real.sq_sqrt (hc i).le]
  exact hsmall i

/-- The actual smooth weights, fixed throughout the local walk. -/
def smoothWeights (ζ : ℝ) (x : ι → ℝ) : ι → ℝ :=
  fun i => Source.weight 64 ζ (x i)

/-- Formal quadratic slope parameter used only to reuse transport algebra. -/
def slopeParameter (ζ : ℝ) (x : ι → ℝ) : ι → ℝ :=
  fun i => -Source.slope 64 ζ (x i) / 128

/-- Failed outward secants for the new source imply an actual nonzero legal
transport direction. This theorem has no caller-supplied probe bound,
Fisher inequality, covariance, or negative acceleration premise. -/
theorem actual_transport_descent_of_failed_secants [Nonempty ι]
    (v : ι → n → ℂ) (hv : ∀ i, v i ≠ 0)
    (x : ι → ℝ) (hx : ∀ i, |x i| < 1)
    {ζ a : ℝ} (hζ : 0 < ζ) (ha : 0 < a) (hscale : ζ ≤ a / 10)
    (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) (hS : S.PosDef)
    (hJS : KSSignSymmetry.conjugate KSSignSymmetry.signMatrix S = S)
    (hfail : ∀ i, Source.secant 64 ζ |x i| a *
      realTrace (stateTransport v (smoothWeights ζ x) S *
        KSSpinCompression.compressedAtom (atoms v) i) ≤ 1) :
    let V := KSSpinCompression.embedding (atoms v)
    let B := KSSpinCompression.compressedAtom (atoms v)
    let J := KSSpinCompression.compressedSign (atoms v)
    let Z := stateTransport v (smoothWeights ζ x) S
    ∃ h : ι → ℝ, ∃ U : Matrix (KSSpinCompression.supportIndex (atoms v))
        (KSSpinCompression.supportIndex (atoms v)) ℂ,
      h ≠ 0 ∧ U.IsHermitian ∧
      KSBalancedSpin.physicalForce B J 64 (slopeParameter ζ x) h
        (fun i => realTrace (Z * B i)) - Z⁻¹ * U * Z⁻¹ +
          KSBalancedSpin.source B (smoothWeights ζ x) U = 0 ∧
      realTrace ((Vᴴ * S * V) * KSBalancedSpin.physicalAcceleration B Z U 64
        (slopeParameter ζ x) h (fun i => realTrace (Z * B i))) < 0 := by
  have hc : ∀ i, 0 < smoothWeights ζ x i := fun i =>
    Source.weight_pos (by norm_num) (hx i)
  have hq := fun i => probe_pos v hv hc hS i
  apply actual_transport_descent v hv (smoothWeights ζ x) (slopeParameter ζ x) hc S hS hJS
  · intro i
    have hs := Source.failed_slope_bound (by norm_num : (0 : ℝ) ≤ 64)
      hζ ha (hq i).le (hfail i)
    change |128 * (-Source.slope 64 ζ (x i) / 128) *
      realTrace (stateTransport v (smoothWeights ζ x) S *
        KSSpinCompression.compressedAtom (atoms v) i)| ≤ 1
    rw [show 128 * (-Source.slope 64 ζ (x i) / 128) =
      -Source.slope 64 ζ (x i) by ring, abs_mul, abs_neg, abs_of_pos (hq i)]
    exact hs
  · intro i
    have hs := Source.failed_weight_probe_sq_bound (by norm_num : (0 : ℝ) < 64)
      hζ.le ha hscale (hq i).le (hfail i)
    convert hs using 1
    norm_num

end SeamlessKS.SourceTransport
