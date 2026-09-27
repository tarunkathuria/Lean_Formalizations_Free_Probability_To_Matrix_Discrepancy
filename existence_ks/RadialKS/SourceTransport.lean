import SeamlessKS.SourceTransport
import RadialKS.PhysicalDescent
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace RadialKS.SourceTransport

open MatrixSpencer MatrixSpencer.KSSpinLocalState

variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
local instance {k : Type*} [Fintype k] [DecidableEq k] : CStarAlgebra (Matrix k k ℂ) := {}


open SeamlessKS.SourceTransport
theorem actual_transport_descent [Nonempty ι]
    (v : ι → n → ℂ) (hv : ∀ i, v i ≠ 0)
    (b c χ : ι → ℝ) (hc : ∀ i, 0 < c i)
    (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) (hS : S.PosDef)
    (hJS : KSSignSymmetry.conjugate KSSignSymmetry.signMatrix S = S)
    (hz : ∀ i, |128 * χ i * realTrace (SeamlessKS.SourceTransport.stateTransport v c S *
      KSSpinCompression.compressedAtom (atoms v) i)| ≤ 1)
    (hsmall : ∀ i, c i * realTrace (SeamlessKS.SourceTransport.stateTransport v c S *
      KSSpinCompression.compressedAtom (atoms v) i) ^ 2 ≤ (200 / 81 : ℝ) / 64) :
    let V := KSSpinCompression.embedding (atoms v)
    let B := KSSpinCompression.compressedAtom (atoms v)
    let J := KSSpinCompression.compressedSign (atoms v)
    let Z := SeamlessKS.SourceTransport.stateTransport v c S
    ∃ h : ι → ℝ, ∃ U : Matrix (KSSpinCompression.supportIndex (atoms v))
        (KSSpinCompression.supportIndex (atoms v)) ℂ,
      h ≠ 0 ∧ b ⬝ᵥ h = 0 ∧ U.IsHermitian ∧
      KSBalancedSpin.physicalForce B J 64 χ h (fun i => realTrace (Z * B i)) -
        Z⁻¹ * U * Z⁻¹ + KSBalancedSpin.source B c U = 0 ∧
      realTrace ((Vᴴ * S * V) * KSBalancedSpin.physicalAcceleration B Z U 64 χ h
        (fun i => realTrace (Z * B i))) < 0 := by
  let V := KSSpinCompression.embedding (atoms v)
  let B := KSSpinCompression.compressedAtom (atoms v)
  let S0 := KSSupportSymmetry.compress V S
  let M := covarianceCompressedSource (KSSpinSource.family (atoms v))
    (KSSpinSource.coefficientCovariance c) S
  let Z := SeamlessKS.SourceTransport.stateTransport v c S
  have hS0 : S0.PosDef := KSSupportSymmetry.compress_posDef V
    (KSSpinCompression.embedding_isometry _) hS
  have hM : M.PosDef := KSSpinCompression.compressed_source_posDef v hc hS
  have hZ : Z.PosDef := SeamlessKS.SourceTransport.stateTransport_posDef v hc hS
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
  apply RadialKS.PhysicalDescent.exists_transport_descent B c hBp hBe hc hS0 hZ hsolve
    (KSSpinCompression.compressedSign_isHermitian (atoms v))
    (KSSpinCompression.compressedSign_sq (atoms v) (fun i => KSRankOne.atom_isHermitian (v i)))
    (KSSpinCompression.compressedSign_commute_transport v hc hS hJS).eq
    (fun i => (KSSpinCompression.compressedSign_commute_atom (atoms v)
      (fun j => KSRankOne.atom_isHermitian (v j)) i).eq) b χ hz
  intro i
  rw [KSBalancedSpin.trace_atom B c hZ i, mul_pow, Real.sq_sqrt (hc i).le]
  exact hsmall i

theorem actual_transport_descent_of_failed_secants [Nonempty ι]
    (v : ι → n → ℂ) (hv : ∀ i, v i ≠ 0)
    (b x : ι → ℝ) (hx : ∀ i, |x i| < 1)
    {ζ a : ℝ} (hζ : 0 < ζ) (ha : 0 < a) (hscale : ζ ≤ a / 10)
    (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) (hS : S.PosDef)
    (hJS : KSSignSymmetry.conjugate KSSignSymmetry.signMatrix S = S)
    (hfail : ∀ i, SeamlessKS.Source.secant 64 ζ |x i| a *
      realTrace (SeamlessKS.SourceTransport.stateTransport v (smoothWeights ζ x) S *
        KSSpinCompression.compressedAtom (atoms v) i) ≤ 1) :
    let V := KSSpinCompression.embedding (atoms v)
    let B := KSSpinCompression.compressedAtom (atoms v)
    let J := KSSpinCompression.compressedSign (atoms v)
    let Z := SeamlessKS.SourceTransport.stateTransport v (smoothWeights ζ x) S
    ∃ h : ι → ℝ, ∃ U : Matrix (KSSpinCompression.supportIndex (atoms v))
        (KSSpinCompression.supportIndex (atoms v)) ℂ,
      h ≠ 0 ∧ b ⬝ᵥ h = 0 ∧ U.IsHermitian ∧
      KSBalancedSpin.physicalForce B J 64 (slopeParameter ζ x) h
        (fun i => realTrace (Z * B i)) - Z⁻¹ * U * Z⁻¹ +
          KSBalancedSpin.source B (smoothWeights ζ x) U = 0 ∧
      realTrace ((Vᴴ * S * V) * KSBalancedSpin.physicalAcceleration B Z U 64
        (slopeParameter ζ x) h (fun i => realTrace (Z * B i))) < 0 := by
  have hc : ∀ i, 0 < smoothWeights ζ x i := fun i =>
    SeamlessKS.Source.weight_pos (by norm_num) (hx i)
  have hq := fun i => SeamlessKS.SourceTransport.probe_pos v hv hc hS i
  apply actual_transport_descent v hv b (smoothWeights ζ x) (slopeParameter ζ x) hc S hS hJS
  · intro i
    have hs := SeamlessKS.Source.failed_slope_bound (by norm_num : (0 : ℝ) ≤ 64)
      hζ ha (hq i).le (hfail i)
    change |128 * (-SeamlessKS.Source.slope 64 ζ (x i) / 128) *
      realTrace (SeamlessKS.SourceTransport.stateTransport v (smoothWeights ζ x) S *
        KSSpinCompression.compressedAtom (atoms v) i)| ≤ 1
    rw [show 128 * (-SeamlessKS.Source.slope 64 ζ (x i) / 128) =
      -SeamlessKS.Source.slope 64 ζ (x i) by ring, abs_mul, abs_neg, abs_of_pos (hq i)]
    exact hs
  · intro i
    have hs := SeamlessKS.Source.failed_weight_probe_sq_bound (by norm_num : (0 : ℝ) < 64)
      hζ.le ha hscale (hq i).le (hfail i)
    convert hs using 1
    norm_num

end RadialKS.SourceTransport
