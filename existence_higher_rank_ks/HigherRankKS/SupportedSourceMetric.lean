import HigherRankKS.SupportedSourceCalculus
import MatrixSpencer.BalancedTransport

/-! Actual supported and balanced nonlinear source metric. -/

open Matrix MatrixSpencer Set
open scoped Topology ContDiff BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace HigherRankKS.SupportedSourceMetric

open SupportedSourceCalculus PowerGramMetric SylvesterMetric
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
local instance supportedSourceMetricCStar {l : Type*} [Fintype l] [DecidableEq l] :
    CStarAlgebra (Matrix l l ℂ) := {}
local instance supportedSourceMetricSpace :
    NormedSpace ℝ (selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ)) := inferInstance

/-- Fixed balance and support map for the actual source. -/
def balanceMap (A : ι → Matrix n n ℂ)
    (Z : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ) :
    Matrix (SourceCarrierIndex A) (n ⊕ n) ℂ := CFC.sqrt Z * (sourceEmbedding A)ᴴ

/-- One actual source term after support compression and balancing. -/
def term (A : ι → Matrix n n ℂ) (β : ℝ)
    (Z : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ) (i : ι)
    (S : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ)) :
    Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ :=
  CFC.sqrt Z * SupportedSpin.term A β S i * CFC.sqrt Z

theorem term_eq_sourceOutput (A : ι → Matrix n n ℂ) (β : ℝ)
    (Z : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ) (i : ι) :
    term A β Z i = sourceOutput (A i) (balanceMap A Z) β := by
  funext S
  simp only [term, sourceOutput, balanceMap, SupportedSpin.term, KSSupportSymmetry.compress,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    (CFC.sqrt_nonneg Z).posSemidef.isHermitian.eq, Matrix.mul_assoc]

/-- Physical atom mass ratio in the density direction. -/
def massRatio (A : ι → Matrix n n ℂ)
    (S U : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ)) (i : ι) : ℝ :=
  realTrace (spinAtom (A i) * (U : Matrix (n ⊕ n) (n ⊕ n) ℂ)) /
    realTrace (spinAtom (A i) * (S : Matrix (n ⊕ n) (n ⊕ n) ℂ))

/-- Total balanced source. -/
def source (A : ι → Matrix n n ℂ) (β : ℝ) (c : ι → ℝ)
    (Z : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ)
    (S : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ)) :
    Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ := ∑ i, c i • term A β Z i S

/-- Actual density source response after removing each atom's mass direction. -/
def defect (A : ι → Matrix n n ℂ) (β : ℝ) (c : ι → ℝ)
    (Z : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ)
    (S U : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ)) :
    Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ :=
  ∑ i, c i • (fderiv ℝ (term A β Z i) S U - massRatio A S U i • term A β Z i S)

/-- Actual nonlinear density curvature, paired with the fixed old transport. -/
def curvature (A : ι → Matrix n n ℂ) (β : ℝ) (c : ι → ℝ)
    (Z : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ)
    (S U : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ)) : ℝ :=
  ∑ i, c i * (-realTrace (fderiv ℝ (fderiv ℝ (term A β Z i)) S U U))

theorem source_eq (A : ι → Matrix n n ℂ) (β : ℝ) (c : ι → ℝ)
    (Z : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ)
    (S : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ)) :
    source A β c Z S = CFC.sqrt Z * compressedSource A β c S * CFC.sqrt Z := by
  simp only [source, term, SupportedSpin.compressedSource_eq_sum, Matrix.mul_sum,
    Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]

theorem source_eq_aggregate (A : ι → Matrix n n ℂ) (c : ι → ℝ)
    (Z : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ)
    (k : ℕ) (hk : 1 ≤ k) (S : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ))
    (hS : (S : Matrix (n ⊕ n) (n ⊕ n) ℂ).PosDef) :
    source A ((1 : ℝ) / 2 ^ k) c Z S =
      SourceMetricAggregation.totalSource ((1 : ℝ) / 2 ^ k) c
        (fun i => outputKraus (A i) (balanceMap A Z)) (fun i => compressedCarrierCLM (A i) S) := by
  apply Finset.sum_congr rfl
  intro i _
  rw [term_eq_sourceOutput]
  exact congrArg (fun X => c i • X) (output_carrier_eq (A i) (balanceMap A Z) k hk S hS.posSemidef).symm

omit [Fintype ι] in
theorem massRatio_eq (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (S U : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ))
    (hS : (S : Matrix (n ⊕ n) (n ⊕ n) ℂ).PosDef) (i : ι) :
    massRatio A S U i =
      realTrace (compressedCarrierCLM (A i) U : Matrix (AtomCarrierIndex (A i)) (AtomCarrierIndex (A i)) ℂ) /
      realTrace (compressedCarrierCLM (A i) S : Matrix (AtomCarrierIndex (A i)) (AtomCarrierIndex (A i)) ℂ) := by
  rw [realTrace_compressedCarrier_direction (A i) (hA i) S U hS,
    realTrace_compressedCarrier_direction (A i) (hA i) S S hS]
  rfl

theorem defect_eq_aggregate (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef) (c : ι → ℝ)
    (Z : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ)
    (k : ℕ) (hk : 1 ≤ k) (S U : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ))
    (hS : (S : Matrix (n ⊕ n) (n ⊕ n) ℂ).PosDef) :
    defect A ((1 : ℝ) / 2 ^ k) c Z S U =
      SourceMetricAggregation.totalDefect ((1 : ℝ) / 2 ^ k) c
        (fun i => outputKraus (A i) (balanceMap A Z))
        (fun i => compressedCarrierCLM (A i) S) (fun i => compressedCarrierCLM (A i) U) := by
  apply Finset.sum_congr rfl
  intro i _
  rw [term_eq_sourceOutput, sourceOutput_first (A i) (balanceMap A Z) k hk S U hS,
    massRatio_eq A hA S U hS i]
  simp only [map_sub, map_smul]
  rw [output_carrier_eq (A i) (balanceMap A Z) k hk S hS.posSemidef]
  rfl

theorem curvature_eq_aggregate (A : ι → Matrix n n ℂ) (c : ι → ℝ)
    (Z : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ)
    (k : ℕ) (hk : 1 ≤ k) (S U : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ))
    (hS : (S : Matrix (n ⊕ n) (n ⊕ n) ℂ).PosDef) :
    curvature A ((1 : ℝ) / 2 ^ k) c Z S U =
      SourceMetricAggregation.totalCurvature ((1 : ℝ) / 2 ^ k) c
        (fun i => outputKraus (A i) (balanceMap A Z))
        (fun i => compressedCarrierCLM (A i) S) (fun i => compressedCarrierCLM (A i) U) := by
  apply Finset.sum_congr rfl
  intro i _
  rw [term_eq_sourceOutput, sourceOutput_second (A i) (balanceMap A Z) k hk S U hS]

theorem term_smooth (A : ι → Matrix n n ℂ)
    (Z : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ) (i : ι)
    (k : ℕ) (hk : 1 ≤ k) (S : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ))
    (hS : (S : Matrix (n ⊕ n) (n ⊕ n) ℂ).PosDef) :
    ContDiffAt ℝ ∞ (term A ((1 : ℝ) / 2 ^ k) Z i) S := by
  rw [term_eq_sourceOutput]
  exact sourceOutput_smooth (A i) (balanceMap A Z) k hk S hS

theorem trace_term_eq_probe (A : ι → Matrix n n ℂ) (β : ℝ)
    (Z : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ) (hZ : Z.PosSemidef)
    (i : ι) (S : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ)) :
    realTrace (term A β Z i S) =
      SourceDerivative.probe β (A i) (sourceEmbedding A * Z * (sourceEmbedding A)ᴴ) S := by
  rw [term, realTrace_mul_cycle, CFC.sqrt_mul_sqrt_self Z hZ.nonneg,
    SupportedSpin.term_pairing]
  rfl

theorem trace_first_eq_probe (A : ι → Matrix n n ℂ)
    (Z : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ) (hZ : Z.PosSemidef)
    (i : ι) (k : ℕ) (hk : 1 ≤ k) (S U : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ))
    (hS : (S : Matrix (n ⊕ n) (n ⊕ n) ℂ).PosDef) :
    realTrace (fderiv ℝ (term A ((1 : ℝ) / 2 ^ k) Z i) S U) =
      fderiv ℝ (SourceDerivative.probe ((1 : ℝ) / 2 ^ k) (A i)
        (sourceEmbedding A * Z * (sourceEmbedding A)ᴴ)) S U := by
  have he : SourceDerivative.probe ((1 : ℝ) / 2 ^ k) (A i)
      (sourceEmbedding A * Z * (sourceEmbedding A)ᴴ) =
      fun T => realTrace (term A ((1 : ℝ) / 2 ^ k) Z i T) := by
    funext T; exact (trace_term_eq_probe A _ Z hZ i T).symm
  rw [he]
  exact (LinearDerivative.first (ContinuousLinearMap.id ℝ _) realTraceCLM _ S U
    ((term_smooth A Z i k hk S hS).differentiableAt (by simp))).symm

theorem trace_second_eq_probe (A : ι → Matrix n n ℂ)
    (Z : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ) (hZ : Z.PosSemidef)
    (i : ι) (k : ℕ) (hk : 1 ≤ k) (S U : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ))
    (hS : (S : Matrix (n ⊕ n) (n ⊕ n) ℂ).PosDef) :
    realTrace (fderiv ℝ (fderiv ℝ (term A ((1 : ℝ) / 2 ^ k) Z i)) S U U) =
      fderiv ℝ (fderiv ℝ (SourceDerivative.probe ((1 : ℝ) / 2 ^ k) (A i)
        (sourceEmbedding A * Z * (sourceEmbedding A)ᴴ))) S U U := by
  have he : SourceDerivative.probe ((1 : ℝ) / 2 ^ k) (A i)
      (sourceEmbedding A * Z * (sourceEmbedding A)ᴴ) =
      fun T => realTrace (term A ((1 : ℝ) / 2 ^ k) Z i T) := by
    funext T; exact (trace_term_eq_probe A _ Z hZ i T).symm
  rw [he]
  exact (LinearDerivative.second (ContinuousLinearMap.id ℝ _) realTraceCLM _ S U
    ((term_smooth A Z i k hk S hS).of_le (WithTop.coe_le_coe.mpr le_top))).symm

theorem curvature_eq_probe (A : ι → Matrix n n ℂ) (c : ι → ℝ)
    (Z : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ) (hZ : Z.PosSemidef)
    (k : ℕ) (hk : 1 ≤ k) (S U : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ))
    (hS : (S : Matrix (n ⊕ n) (n ⊕ n) ℂ).PosDef) :
    curvature A ((1 : ℝ) / 2 ^ k) c Z S U =
      -(∑ i, c i * fderiv ℝ (fderiv ℝ (SourceDerivative.probe ((1 : ℝ) / 2 ^ k) (A i)
        (sourceEmbedding A * Z * (sourceEmbedding A)ᴴ))) S U U) := by
  simp only [curvature, trace_second_eq_probe A Z hZ _ k hk S U hS, mul_neg, Finset.sum_neg_distrib]

theorem defect_isHermitian (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (hne : ∀ i, A i ≠ 0) (c : ι → ℝ)
    (Z : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ)
    (k : ℕ) (hk : 1 ≤ k) (S U : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ))
    (hS : (S : Matrix (n ⊕ n) (n ⊕ n) ℂ).PosDef) :
    (defect A ((1 : ℝ) / 2 ^ k) c Z S U).IsHermitian := by
  letI : ∀ i, Nonempty (AtomCarrierIndex (A i)) := fun i => atomCarrier_nonempty (hA i) (hne i)
  rw [defect_eq_aggregate A hA c Z k hk S U hS]
  exact SourceMetricAggregation.totalDefect_isHermitian (dyadic_mem_Ioo k hk) _ _ _ _
    (fun i => by simpa only [compressedCarrierCLM_coe] using compressedCarrier_posDef (A i) hS)

theorem curvature_nonneg (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (hne : ∀ i, A i ≠ 0) (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    (Z : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ)
    (k : ℕ) (hk : 1 ≤ k) (S U : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ))
    (hS : (S : Matrix (n ⊕ n) (n ⊕ n) ℂ).PosDef) :
    0 ≤ curvature A ((1 : ℝ) / 2 ^ k) c Z S U := by
  letI : ∀ i, Nonempty (AtomCarrierIndex (A i)) := fun i => atomCarrier_nonempty (hA i) (hne i)
  rw [curvature_eq_aggregate A c Z k hk S U hS]
  exact SourceMetricAggregation.totalCurvature_nonneg (dyadic_mem_Ioo k hk) _ hc _ _ _
    (fun i => by simpa only [compressedCarrierCLM_coe] using compressedCarrier_posDef (A i) hS)

/-- The source metric estimate for the actual atom source with a fixed supported balance map. -/
theorem energy_le (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (hne : ∀ i, A i ≠ 0) (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    (Z : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ)
    (k : ℕ) (hk : 1 ≤ k) (S U : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ))
    (hS : (S : Matrix (n ⊕ n) (n ⊕ n) ℂ).PosDef)
    (hP : (source A ((1 : ℝ) / 2 ^ k) c Z S).PosDef) :
    energy (source A ((1 : ℝ) / 2 ^ k) c Z S) hP (defect A ((1 : ℝ) / 2 ^ k) c Z S U) ≤
      (1 - (1 : ℝ) / 2 ^ k) / (2 * ((1 : ℝ) / 2 ^ k)) * curvature A ((1 : ℝ) / 2 ^ k) c Z S U := by
  letI : ∀ i, Nonempty (AtomCarrierIndex (A i)) := fun i => atomCarrier_nonempty (hA i) (hne i)
  have hP' : (SourceMetricAggregation.totalSource ((1 : ℝ) / 2 ^ k) c
      (fun i => outputKraus (A i) (balanceMap A Z)) (fun i => compressedCarrierCLM (A i) S)).PosDef := by
    rw [← source_eq_aggregate A c Z k hk S hS]
    exact hP
  have h := SourceMetricAggregation.total_energy_le (dyadic_mem_Ioo k hk) c hc
    (fun i => outputKraus (A i) (balanceMap A Z))
    (fun i => compressedCarrierCLM (A i) S) (fun i => compressedCarrierCLM (A i) U)
    (fun i => by simpa only [compressedCarrierCLM_coe] using compressedCarrier_posDef (A i) hS) hP'
  simpa only [← source_eq_aggregate A c Z k hk S hS,
    ← defect_eq_aggregate A hA c Z k hk S U hS, ← curvature_eq_aggregate A c Z k hk S U hS] using h

/-- The balanced density at the actual supported optimizing transport. -/
def balanced (A : ι → Matrix n n ℂ) (β : ℝ) (c : ι → ℝ)
    (S : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ)) :
    Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ :=
  balancedDensity (SupportedSpin.density A S) (SupportedSpin.transport A β c S)

theorem balanced_posDef (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (c : ι → ℝ) (hc : ∀ i, 0 < c i) (k : ℕ) (hk : 1 ≤ k)
    (S : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ))
    (hS : (S : Matrix (n ⊕ n) (n ⊕ n) ℂ).PosDef) :
    (balanced A ((1 : ℝ) / 2 ^ k) c S).PosDef :=
  balancedDensity_posDef (SupportedSpin.density_posDef A hS) (SupportedSpin.transport_posDef A hA hc hS k hk)

theorem source_eq_balanced (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (c : ι → ℝ) (hc : ∀ i, 0 < c i) (k : ℕ) (hk : 1 ≤ k)
    (S : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ))
    (hS : (S : Matrix (n ⊕ n) (n ⊕ n) ℂ).PosDef) :
    source A ((1 : ℝ) / 2 ^ k) c (SupportedSpin.transport A ((1 : ℝ) / 2 ^ k) c S) S =
      balanced A ((1 : ℝ) / 2 ^ k) c S := by
  rw [source_eq, balanced, balancedDensity_eq_source_congruence
    (SupportedSpin.transport_posDef A hA hc hS k hk) (SupportedSpin.transport_equation A hA hc hS k hk)]

/-- Actual supported source metric, with every source, transport, and derivative instantiated. -/
theorem actual_energy_le (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (hne : ∀ i, A i ≠ 0) (c : ι → ℝ) (hc : ∀ i, 0 < c i)
    (k : ℕ) (hk : 1 ≤ k) (S U : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ))
    (hS : (S : Matrix (n ⊕ n) (n ⊕ n) ℂ).PosDef) :
    energy (balanced A ((1 : ℝ) / 2 ^ k) c S) (balanced_posDef A hA c hc k hk S hS)
      (defect A ((1 : ℝ) / 2 ^ k) c (SupportedSpin.transport A ((1 : ℝ) / 2 ^ k) c S) S U) ≤
      (1 - (1 : ℝ) / 2 ^ k) / (2 * ((1 : ℝ) / 2 ^ k)) *
        curvature A ((1 : ℝ) / 2 ^ k) c (SupportedSpin.transport A ((1 : ℝ) / 2 ^ k) c S) S U := by
  have hp : (source A ((1 : ℝ) / 2 ^ k) c (SupportedSpin.transport A ((1 : ℝ) / 2 ^ k) c S) S).PosDef := by
    rw [source_eq_balanced A hA c hc k hk S hS]
    exact balanced_posDef A hA c hc k hk S hS
  have h := energy_le A hA hne c (fun i => (hc i).le) _ k hk S U hS hp
  simpa only [source_eq_balanced A hA c hc k hk S hS] using h

/-- Exact beta absorption for the actual supported nonlinear source. -/
theorem actual_absorption (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (hne : ∀ i, A i ≠ 0) (c : ι → ℝ) (hc : ∀ i, 0 < c i)
    (k : ℕ) (hk : 1 ≤ k) (S U : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ))
    (hS : (S : Matrix (n ⊕ n) (n ⊕ n) ℂ).PosDef)
    {X : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ} (hX : X.IsHermitian) :
    ((1 : ℝ) / 2 ^ k) * energy (balanced A ((1 : ℝ) / 2 ^ k) c S)
      (balanced_posDef A hA c hc k hk S hS) X ≤
      energy (balanced A ((1 : ℝ) / 2 ^ k) c S) (balanced_posDef A hA c hc k hk S hS)
        (X - defect A ((1 : ℝ) / 2 ^ k) c (SupportedSpin.transport A ((1 : ℝ) / 2 ^ k) c S) S U) +
      curvature A ((1 : ℝ) / 2 ^ k) c (SupportedSpin.transport A ((1 : ℝ) / 2 ^ k) c S) S U / 2 := by
  exact source_metric_absorption _ _ hX (defect_isHermitian A hA hne c _ k hk S U hS)
    (dyadic_mem_Ioo k hk).1 (dyadic_mem_Ioo k hk).2 (actual_energy_le A hA hne c hc k hk S U hS)

end HigherRankKS.SupportedSourceMetric
