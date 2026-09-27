import HigherRankKS.SupportedSourceMetric

/-! Scalar probe consequence of the actual supported matrix source metric. -/
open Matrix MatrixSpencer Set
open scoped Topology ContDiff BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace HigherRankKS.SupportedScalarMetric
open SupportedSourceCalculus SupportedSourceMetric PowerGramMetric
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
local instance supportedScalarMetricCStar {l : Type*} [Fintype l] [DecidableEq l] :
    CStarAlgebra (Matrix l l ℂ) := {}
local instance supportedScalarMetricSpace :
    NormedSpace ℝ (selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ)) := inferInstance

/-- The residual is the actual scalar probe derivative with its atom mass direction removed. -/
def residual (A : ι → Matrix n n ℂ) (β : ℝ)
    (Z : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ)
    (S U : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ)) (i : ι) : ℝ :=
  fderiv ℝ (SourceDerivative.probe β (A i) (sourceEmbedding A * Z * (sourceEmbedding A)ᴴ)) S U -
    massRatio A S U i * SourceDerivative.probe β (A i) (sourceEmbedding A * Z * (sourceEmbedding A)ᴴ) S

/-- Equivalent physical form using the fixed-source ratio q_i = tau_i / p_i. -/
theorem residual_eq (A : ι → Matrix n n ℂ) (β : ℝ)
    (Z : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ)
    (S U : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ)) (i : ι) :
    residual A β Z S U i =
      fderiv ℝ (SourceDerivative.probe β (A i) (sourceEmbedding A * Z * (sourceEmbedding A)ᴴ)) S U -
        (SourceDerivative.probe β (A i) (sourceEmbedding A * Z * (sourceEmbedding A)ᴴ) S /
          realTrace (spinAtom (A i) * (S : Matrix (n ⊕ n) (n ⊕ n) ℂ))) *
            realTrace (spinAtom (A i) * (U : Matrix (n ⊕ n) (n ⊕ n) ℂ)) := by
  dsimp [residual, massRatio]
  ring

theorem residual_eq_carrier (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (Z : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ) (hZ : Z.PosSemidef)
    (k : ℕ) (hk : 1 ≤ k) (S U : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ))
    (hS : (S : Matrix (n ⊕ n) (n ⊕ n) ℂ).PosDef) (i : ι) :
    residual A ((1 : ℝ) / 2 ^ k) Z S U i = realTrace (krausMap (outputKraus (A i) (balanceMap A Z))
      (CarrierMetric.first ((1 : ℝ) / 2 ^ k) (compressedCarrierCLM (A i) S) (compressedCarrierCLM (A i) U) -
        (realTrace (compressedCarrierCLM (A i) U : Matrix (AtomCarrierIndex (A i)) (AtomCarrierIndex (A i)) ℂ) /
          realTrace (compressedCarrierCLM (A i) S : Matrix (AtomCarrierIndex (A i)) (AtomCarrierIndex (A i)) ℂ)) •
            CarrierMetric.carrier ((1 : ℝ) / 2 ^ k) (compressedCarrierCLM (A i) S))) := by
  rw [residual, ← trace_first_eq_probe A Z hZ i k hk S U hS,
    ← trace_term_eq_probe A _ Z hZ i S, term_eq_sourceOutput,
    sourceOutput_first (A i) (balanceMap A Z) k hk S U hS,
    massRatio_eq A hA S U hS i]
  simp only [map_sub, map_smul, realTrace_sub, realTrace_smul]
  rw [output_carrier_eq (A i) (balanceMap A Z) k hk S hS.posSemidef]
  rfl


theorem probe_sq_le (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (hne : ∀ i, A i ≠ 0) (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i) (b : ι → ℝ)
    (Z : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ) (hZ : Z.PosSemidef)
    (k : ℕ) (hk : 1 ≤ k) (S U : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ))
    (hS : (S : Matrix (n ⊕ n) (n ⊕ n) ℂ).PosDef) :
    (∑ i, c i * b i * residual A ((1 : ℝ) / 2 ^ k) Z S U i) ^ 2 ≤
      (1 - (1 : ℝ) / 2 ^ k) / ((1 : ℝ) / 2 ^ k) *
        (∑ i, c i * b i ^ 2 * SourceDerivative.probe ((1 : ℝ) / 2 ^ k) (A i)
          (sourceEmbedding A * Z * (sourceEmbedding A)ᴴ) S) *
        curvature A ((1 : ℝ) / 2 ^ k) c Z S U := by
  letI : ∀ i, Nonempty (AtomCarrierIndex (A i)) := fun i => atomCarrier_nonempty (hA i) (hne i)
  have h := SourceMetricAggregation.scalar_probe_sq_le (dyadic_mem_Ioo k hk) c hc b
    (fun i => outputKraus (A i) (balanceMap A Z))
    (fun i => compressedCarrierCLM (A i) S) (fun i => compressedCarrierCLM (A i) U)
    (fun i => by simpa only [compressedCarrierCLM_coe] using compressedCarrier_posDef (A i) hS)
  have hv (i : ι) : realTrace (krausMap (outputKraus (A i) (balanceMap A Z))
      (CarrierMetric.carrier ((1 : ℝ) / 2 ^ k) (compressedCarrierCLM (A i) S))) =
      SourceDerivative.probe ((1 : ℝ) / 2 ^ k) (A i) (sourceEmbedding A * Z * (sourceEmbedding A)ᴴ) S := by
    rw [output_carrier_eq (A i) (balanceMap A Z) k hk S hS.posSemidef]
    change realTrace (sourceOutput (A i) (balanceMap A Z) ((1 : ℝ) / 2 ^ k) S) = _
    rw [← term_eq_sourceOutput]
    exact trace_term_eq_probe A _ Z hZ i S
  simpa only [← residual_eq_carrier A hA Z hZ k hk S U hS, hv,
    ← curvature_eq_aggregate A c Z k hk S U hS] using h

theorem probe_nonneg (A : ι → Matrix n n ℂ) (β : ℝ)
    (Z : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ) (hZ : Z.PosSemidef)
    (S : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ))
    (hS : (S : Matrix (n ⊕ n) (n ⊕ n) ℂ).PosSemidef) (i : ι) :
    0 ≤ SourceDerivative.probe β (A i) (sourceEmbedding A * Z * (sourceEmbedding A)ᴴ) S := by
  change 0 ≤ realTrace ((sourceEmbedding A * Z * (sourceEmbedding A)ᴴ) * sourceTerm β (A i) S)
  rw [← SupportedSpin.term_pairing]
  exact realTrace_mul_nonneg hZ (SupportedSpin.term_posSemidef A β hS i)

/-- The weighted Cauchy--Schwarz form with arbitrary unnormalized coefficient probes. -/
theorem unweighted_probe_sq_le (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (hne : ∀ i, A i ≠ 0) (c : ι → ℝ) (hc : ∀ i, 0 < c i) (b : ι → ℝ)
    (Z : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ) (hZ : Z.PosSemidef)
    (k : ℕ) (hk : 1 ≤ k) (S U : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ))
    (hS : (S : Matrix (n ⊕ n) (n ⊕ n) ℂ).PosDef) :
    (∑ i, b i * residual A ((1 : ℝ) / 2 ^ k) Z S U i) ^ 2 ≤
      (1 - (1 : ℝ) / 2 ^ k) / ((1 : ℝ) / 2 ^ k) *
        (∑ i, b i ^ 2 * SourceDerivative.probe ((1 : ℝ) / 2 ^ k) (A i)
          (sourceEmbedding A * Z * (sourceEmbedding A)ᴴ) S / c i) *
        curvature A ((1 : ℝ) / 2 ^ k) c Z S U := by
  have h := probe_sq_le A hA hne c (fun i => (hc i).le) (fun i => b i / c i) Z hZ k hk S U hS
  have hl (i : ι) : c i * (b i / c i) * residual A ((1 : ℝ) / 2 ^ k) Z S U i =
      b i * residual A ((1 : ℝ) / 2 ^ k) Z S U i := by field_simp [(hc i).ne']
  have hr (i : ι) : c i * (b i / c i) ^ 2 *
      SourceDerivative.probe ((1 : ℝ) / 2 ^ k) (A i) (sourceEmbedding A * Z * (sourceEmbedding A)ᴴ) S =
      b i ^ 2 * SourceDerivative.probe ((1 : ℝ) / 2 ^ k) (A i)
        (sourceEmbedding A * Z * (sourceEmbedding A)ᴴ) S / c i := by
    field_simp
  simpa only [hl, hr] using h

/-- Half of the actual source curvature pays the scalar source residual. -/
theorem scalar_absorption (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (hne : ∀ i, A i ≠ 0) (c : ι → ℝ) (hc : ∀ i, 0 < c i) (b : ι → ℝ)
    (Z : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ) (hZ : Z.PosSemidef)
    (k : ℕ) (hk : 1 ≤ k) (S U : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ))
    (hS : (S : Matrix (n ⊕ n) (n ⊕ n) ℂ).PosDef) :
    2 * (∑ i, b i * residual A ((1 : ℝ) / 2 ^ k) Z S U i) ≤
      curvature A ((1 : ℝ) / 2 ^ k) c Z S U / 2 +
      (2 * (1 - (1 : ℝ) / 2 ^ k) / ((1 : ℝ) / 2 ^ k)) *
        (∑ i, b i ^ 2 * SourceDerivative.probe ((1 : ℝ) / 2 ^ k) (A i)
          (sourceEmbedding A * Z * (sourceEmbedding A)ᴴ) S / c i) := by
  let q := (1 - (1 : ℝ) / 2 ^ k) / ((1 : ℝ) / 2 ^ k) *
    (∑ i, b i ^ 2 * SourceDerivative.probe ((1 : ℝ) / 2 ^ k) (A i)
      (sourceEmbedding A * Z * (sourceEmbedding A)ᴴ) S / c i)
  have hq : 0 ≤ q := by
    apply mul_nonneg (div_nonneg (by linarith [(dyadic_mem_Ioo k hk).2]) (dyadic_mem_Ioo k hk).1.le)
    exact Finset.sum_nonneg (fun i _ => div_nonneg
      (mul_nonneg (sq_nonneg _) (probe_nonneg A _ Z hZ S hS.posSemidef i)) (hc i).le)
  have hcurv := curvature_nonneg A hA hne c (fun i => (hc i).le) Z k hk S U hS
  have hsq := unweighted_probe_sq_le A hA hne c hc b Z hZ k hk S U hS
  change (∑ i, b i * residual A ((1 : ℝ) / 2 ^ k) Z S U i) ^ 2 ≤
    q * curvature A ((1 : ℝ) / 2 ^ k) c Z S U at hsq
  have he : (2 * (1 - (1 : ℝ) / 2 ^ k) / ((1 : ℝ) / 2 ^ k)) *
      (∑ i, b i ^ 2 * SourceDerivative.probe ((1 : ℝ) / 2 ^ k) (A i)
        (sourceEmbedding A * Z * (sourceEmbedding A)ᴴ) S / c i) = 2 * q := by
    dsimp [q]; ring
  rw [he]
  nlinarith [sq_nonneg (curvature A ((1 : ℝ) / 2 ^ k) c Z S U / 2 - 2 * q)]

end HigherRankKS.SupportedScalarMetric
