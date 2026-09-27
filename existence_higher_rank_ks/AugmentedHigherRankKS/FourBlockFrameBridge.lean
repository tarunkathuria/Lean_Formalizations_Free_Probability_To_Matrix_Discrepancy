import AugmentedHigherRankKS.FourBlockSourceMetric
import HigherRankKS.BalancedFrames
import HigherRankKS.NormalizedForce
import AugmentedHigherRankKS.FourBlockReducedVelocity

/-! Exact identities relating the nonlinear source defect to the balanced frame channel. -/

open Matrix MatrixSpencer HigherRankKS Set MatrixSpencer.KSFisher MatrixSpencer.KSSupportSymmetry
open scoped Topology ContDiff BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

noncomputable section
namespace AugmentedHigherRankKS.SupportedFrameBridge

variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
local instance supportedFrameBridgeCStar {l : Type*} [Fintype l] [DecidableEq l] :
    CStarAlgebra (Matrix l l ℂ) := {}

omit [DecidableEq ι] in
/-- The actual normalized frame channel prepares each atom in proportion to its input mass. -/
theorem frameChannel_eq_mass (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (β : ℝ) (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    (Z : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ) (hZ : Z.PosDef)
    (S U : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ)) :
    TwoFrames.frameChannel (BalancedFrames.measurementFrame (SupportedSpin.probe A) c Z)
      (BalancedFrames.preparationFrame (SupportedSpin.probe A) (SupportedSpin.term A β S)
        c (SupportedSpin.density A S) Z)
      (balancedDensity (SupportedSpin.density A U) Z) =
      ∑ i, c i • (SupportedSourceMetric.massRatio A S U i • SupportedSourceMetric.term A β Z i S) := by
  have h := NormalizedForce.channel_identity (balancedKraus (SupportedSpin.probe A) Z)
    (balancedKraus (SupportedSpin.term A β S) Z) c
    (BalancedFrames.carrierMass (SupportedSpin.probe A) (SupportedSpin.density A S)) hc
    (balancedDensity (SupportedSpin.density A U) Z)
  change TwoFrames.frameChannel (BalancedFrames.measurementFrame (SupportedSpin.probe A) c Z)
      (BalancedFrames.preparationFrame (SupportedSpin.probe A) (SupportedSpin.term A β S)
        c (SupportedSpin.density A S) Z) (balancedDensity (SupportedSpin.density A U) Z) = _ at h
  rw [h]
  apply Finset.sum_congr rfl
  intro i _
  have hp := KSBalancedSpin.trace_balanced_pair (SupportedSpin.density A U) (SupportedSpin.probe A i) hZ
  rw [SupportedSpin.probe_pairing A hA] at hp
  rw [balancedKraus, realTrace_mul_comm, hp]
  simp only [BalancedFrames.carrierMass, SupportedSpin.probe_pairing A hA,
    SupportedSourceMetric.massRatio, SupportedSourceMetric.term, balancedKraus, smul_smul]
  congr 1
  ring

omit [DecidableEq ι] in
/-- The actual source defect is its derivative minus the normalized frame channel. -/
theorem defect_eq_derivative_sub_channel (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) (β : ℝ) (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    (Z : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ) (hZ : Z.PosDef)
    (S U : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ)) :
    SupportedSourceMetric.defect A β c Z S U =
      (∑ i, c i • fderiv ℝ (SupportedSourceMetric.term A β Z i) S U) -
      TwoFrames.frameChannel (BalancedFrames.measurementFrame (SupportedSpin.probe A) c Z)
        (BalancedFrames.preparationFrame (SupportedSpin.probe A) (SupportedSpin.term A β S)
          c (SupportedSpin.density A S) Z)
        (balancedDensity (SupportedSpin.density A U) Z) := by
  rw [frameChannel_eq_mass A hA β c hc Z hZ S U]
  simp only [SupportedSourceMetric.defect, smul_sub, Finset.sum_sub_distrib]

omit [DecidableEq ι] in
/-- Fixed support compression and balancing commute with the actual source derivative. -/
theorem term_first_eq (A : ι → Matrix n n ℂ)
    (Z : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ)
    (i : ι) (k : ℕ) (hk : 1 ≤ k)
    (S U : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ))
    (hS : (S : Matrix (FourSpin n) (FourSpin n) ℂ).PosDef) :
    fderiv ℝ (SupportedSourceMetric.term A ((1 : ℝ) / 2 ^ k) Z i) S U =
      CFC.sqrt Z * ((sourceEmbedding A)ᴴ *
        fderiv ℝ (SourceDerivatives.term ((1 : ℝ) / 2 ^ k) (A i)) S U * sourceEmbedding A) * CFC.sqrt Z := by
  let R := (matrixExtensionCLM (CFC.sqrt Z)).comp (matrixExtensionCLM (sourceEmbedding A)ᴴ)
  have hf : DifferentiableAt ℝ (SourceDerivatives.term ((1 : ℝ) / 2 ^ k) (A i)) S :=
    (contDiffAt_sourceTerm (A i) k hk S hS).differentiableAt (by simp)
  have h := LinearDerivative.first (ContinuousLinearMap.id ℝ _) R
    (SourceDerivatives.term ((1 : ℝ) / 2 ^ k) (A i)) S U hf
  simpa only [R, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    matrixExtensionCLM_apply, Matrix.conjTranspose_conjTranspose,
    (CFC.sqrt_nonneg Z).posSemidef.isHermitian.eq,
    SupportedSourceMetric.term, SupportedSpin.term, compress, SourceDerivatives.term] using h

omit [DecidableEq ι] in
/-- The exact balanced mismatch is the normalized channel mismatch minus the nonlinear defect. -/
theorem mismatch_eq_frame_defect (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (k : ℕ) (hk : 1 ≤ k) (c : ℝ → ι → ℝ) (hcs : ContDiffAt ℝ 2 c 0)
    (hc : ∀ i, 0 < c 0 i)
    (S U : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ))
    (hS : (S : Matrix (FourSpin n) (FourSpin n) ℂ).PosDef)
    (Z : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ) (hZ : Z.PosDef) :
    let β := (1 : ℝ) / 2 ^ k
    let G := fun t : ℝ => jointReducedSourcePair A β (c t, S + t • U)
    let Y := balancedDensity (SupportedSpin.density A U) Z
    BalancedTransportResponse.mismatch Z
      ((deriv G 0).1 : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ)
      ((deriv G 0).2 : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ) =
      (Y - TwoFrames.frameChannel (BalancedFrames.measurementFrame (SupportedSpin.probe A) (c 0) Z)
        (BalancedFrames.preparationFrame (SupportedSpin.probe A) (SupportedSpin.term A β S)
          (c 0) (SupportedSpin.density A S) Z) Y -
        ∑ i, deriv (fun t => c t i) 0 • SupportedSourceMetric.term A β Z i S) -
      SupportedSourceMetric.defect A β (c 0) Z S U := by
  dsimp only
  have hm := ReducedSourceVelocity.mismatch_eq A k hk c hcs hc S U hS Z
  dsimp only at hm
  simp only [← term_first_eq A Z _ k hk S U hS] at hm
  rw [hm, defect_eq_derivative_sub_channel A hA _ (c 0) (fun i => (hc i).le) Z hZ S U]
  simp only [balancedDensity, transportInverseSqrt, SupportedSpin.density, compress,
    SupportedSourceMetric.term, SupportedSpin.term, SourceDerivatives.term]
  abel

omit [DecidableEq ι] in
/-- The scalar probe residual is exactly the trace of its balanced matrix defect. -/
theorem probe_residual_eq_trace (A : ι → Matrix n n ℂ)
    (Z : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ) (hZ : Z.PosSemidef)
    (i : ι) (k : ℕ) (hk : 1 ≤ k)
    (S U : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ))
    (hS : (S : Matrix (FourSpin n) (FourSpin n) ℂ).PosDef) :
    let β := (1 : ℝ) / 2 ^ k
    let p := realTrace (spinAtom (A i) * (S : Matrix (FourSpin n) (FourSpin n) ℂ))
    let τ := SourceDerivative.probe β (A i) (sourceEmbedding A * Z * (sourceEmbedding A)ᴴ)
    fderiv ℝ τ S U - (τ S / p) * realTrace (spinAtom (A i) * (U : Matrix (FourSpin n) (FourSpin n) ℂ)) =
      realTrace (fderiv ℝ (SupportedSourceMetric.term A β Z i) S U -
        SupportedSourceMetric.massRatio A S U i • SupportedSourceMetric.term A β Z i S) := by
  dsimp only
  rw [realTrace_sub, realTrace_smul, SupportedSourceMetric.trace_first_eq_probe A Z hZ i k hk S U hS,
    SupportedSourceMetric.trace_term_eq_probe A _ Z hZ i S]
  unfold SupportedSourceMetric.massRatio
  ring

omit [DecidableEq ι] in
/-- The normalized mismatch is Hermitian for every full Hermitian density direction. -/
theorem frame_mismatch_isHermitian (A : ι → Matrix n n ℂ) (β : ℝ) (c dc : ι → ℝ)
    (Z : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ)
    (S U : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ))
    (hS : (S : Matrix (FourSpin n) (FourSpin n) ℂ).PosSemidef) :
    let Y := balancedDensity (SupportedSpin.density A U) Z
    (Y - TwoFrames.frameChannel (BalancedFrames.measurementFrame (SupportedSpin.probe A) c Z)
      (BalancedFrames.preparationFrame (SupportedSpin.probe A) (SupportedSpin.term A β S)
        c (SupportedSpin.density A S) Z) Y -
      ∑ i, dc i • SupportedSourceMetric.term A β Z i S).IsHermitian := by
  dsimp only
  have hroot : (CFC.sqrt Z).IsHermitian := (CFC.sqrt_nonneg Z).posSemidef.isHermitian
  have hd : (SupportedSpin.density A U).IsHermitian :=
    Matrix.isHermitian_conjTranspose_mul_mul (sourceEmbedding A) U.property
  have hY : (balancedDensity (SupportedSpin.density A U) Z).IsHermitian := by
    simpa only [balancedDensity, transportInverseSqrt, hroot.inv.eq] using
      Matrix.isHermitian_mul_mul_conjTranspose (CFC.sqrt Z)⁻¹ hd
  have hO := fun i => (SupportedSpin.term_posSemidef A β hS i).isHermitian
  have hterm : ∀ i, (SupportedSourceMetric.term A β Z i S).IsHermitian := fun i => by
    simpa only [SupportedSourceMetric.term, hroot.eq] using
      Matrix.isHermitian_mul_mul_conjTranspose (CFC.sqrt Z) (hO i)
  have hF : ∀ i, (BalancedFrames.preparationFrame (SupportedSpin.probe A)
      (SupportedSpin.term A β S) c (SupportedSpin.density A S) Z i).IsHermitian := fun i =>
    IsSelfAdjoint.smul (show IsSelfAdjoint (Real.sqrt (c i) /
      BalancedFrames.carrierMass (SupportedSpin.probe A) (SupportedSpin.density A S) i) from rfl)
      (balancedKraus_isHermitian _ hO Z i)
  exact (hY.sub (synthesis_isHermitian _ hF _)).sub (synthesis_isHermitian _ hterm dc)

end AugmentedHigherRankKS.SupportedFrameBridge
