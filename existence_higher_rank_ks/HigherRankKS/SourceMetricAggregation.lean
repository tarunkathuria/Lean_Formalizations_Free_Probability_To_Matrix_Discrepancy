import HigherRankKS.CarrierGramMetric
import HigherRankKS.SylvesterAggregation

/-!
# Aggregating actual nonlinear sources before taking the inverse metric

Each original atom may have its own carrier and Kraus index type. Individual
outputs may be singular. Only their weighted sum must be positive definite.
-/

open Matrix MatrixSpencer Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

noncomputable section
namespace HigherRankKS.SourceMetricAggregation

open PowerGramMetric SylvesterMetric

variable {ι m : Type*} [Fintype ι] [Fintype m] [DecidableEq m]
variable {n κ : ι → Type*} [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)]
  [∀ i, Fintype (κ i)]

/-- Total concrete source output; carrier dimensions may depend on the
original atom label. -/
def totalSource (β : ℝ) (c : ι → ℝ) (K : ∀ i, κ i → Matrix m (n i) ℂ)
    (M : ∀ i, selfAdjoint (Matrix (n i) (n i) ℂ)) : Matrix m m ℂ :=
  ∑ i, c i • krausMap (K i) (CarrierMetric.carrier β (M i))

/-- The full matrix defect remaining after subtracting the scalar trace
direction separately for each original atom. -/
def totalDefect (β : ℝ) (c : ι → ℝ) (K : ∀ i, κ i → Matrix m (n i) ℂ)
    (M U : ∀ i, selfAdjoint (Matrix (n i) (n i) ℂ)) : Matrix m m ℂ :=
  ∑ i, c i • krausMap (K i) (CarrierMetric.first β (M i) (U i) -
    (realTrace (U i : Matrix (n i) (n i) ℂ) /
      realTrace (M i : Matrix (n i) (n i) ℂ)) • CarrierMetric.carrier β (M i))

/-- Actual source curvature, paired with the output trace. -/
def totalCurvature (β : ℝ) (c : ι → ℝ) (K : ∀ i, κ i → Matrix m (n i) ℂ)
    (M U : ∀ i, selfAdjoint (Matrix (n i) (n i) ℂ)) : ℝ :=
  ∑ i, c i * (-realTrace (krausMap (K i) (CarrierMetric.second β (M i) (U i) (U i))))

variable [∀ i, Nonempty (n i)]

omit [Fintype m] [DecidableEq m] in
theorem totalDefect_isHermitian {β : ℝ} (hβ : β ∈ Ioo 0 1)
    (c : ι → ℝ) (K : ∀ i, κ i → Matrix m (n i) ℂ)
    (M U : ∀ i, selfAdjoint (Matrix (n i) (n i) ℂ))
    (hM : ∀ i, (M i : Matrix (n i) (n i) ℂ).PosDef) :
    (totalDefect β c K M U).IsHermitian := by
  have hα : 1 - β ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hβ.2], by linarith [hβ.1]⟩
  have hi (i : ι) : (krausMap (K i) (CarrierMetric.first β (M i) (U i) -
      (realTrace (U i : Matrix (n i) (n i) ℂ) /
        realTrace (M i : Matrix (n i) (n i) ℂ)) • CarrierMetric.carrier β (M i))).IsHermitian := by
    apply krausMap_isHermitian
    rw [(CarrierMetric.centered hβ (M i) (U i) (hM i)).1]
    exact (IsSelfAdjoint.all _).smul
      (first_isHermitian hα (M i) _ (hM i)).isSelfAdjoint
  change (totalDefect β c K M U)ᴴ = totalDefect β c K M U
  simp only [totalDefect, Matrix.conjTranspose_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact (IsSelfAdjoint.all (c i)).smul (hi i).isSelfAdjoint

/-- This is the actual aggregate source estimate in variational form.
No invertibility premise is made on any individual atom output. -/
theorem total_variational_le {β : ℝ} (hβ : β ∈ Ioo 0 1)
    (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i) (K : ∀ i, κ i → Matrix m (n i) ℂ)
    (M U : ∀ i, selfAdjoint (Matrix (n i) (n i) ℂ))
    (hM : ∀ i, (M i : Matrix (n i) (n i) ℂ).PosDef)
    {Y : Matrix m m ℂ} (hY : Y.IsHermitian) :
    variational (((1 - β) * β) • totalSource β c K M)
      ((2 * β) • totalDefect β c K M U) Y ≤ 2 * totalCurvature β c K M U := by
  let W := fun i => krausMap (K i) (CarrierMetric.carrier β (M i))
  let R := fun i => krausMap (K i) (CarrierMetric.first β (M i) (U i) -
    (realTrace (U i : Matrix (n i) (n i) ℂ) /
      realTrace (M i : Matrix (n i) (n i) ℂ)) • CarrierMetric.carrier β (M i))
  let C := fun i => -realTrace (krausMap (K i) (CarrierMetric.second β (M i) (U i) (U i)))
  change variational (((1 - β) * β) • ∑ i, c i • W i)
    ((2 * β) • ∑ i, c i • R i) Y ≤ 2 * ∑ i, c i * C i
  have hs : variational (((1 - β) * β) • ∑ i, c i • W i)
      ((2 * β) • ∑ i, c i • R i) Y =
      ∑ i, c i * variational (((1 - β) * β) • W i) ((2 * β) • R i) Y := by
    simp only [Finset.smul_sum, smul_comm ((1 - β) * β), smul_comm (2 * β)]
    exact variational_weighted_sum _ _ c Y
  rw [hs, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have h := mul_le_mul_of_nonneg_left
    (CarrierMetric.carrier_variational_le hβ (K i) (M i) (U i) (hM i) hY) (hc i)
  change c i * variational (((1 - β) * β) • W i) ((2 * β) • R i) Y ≤ 2 * (c i * C i)
  nlinarith

/-- Nonnegative curvature of the concrete aggregate, without any output
invertibility condition. -/
theorem totalCurvature_nonneg {β : ℝ} (hβ : β ∈ Ioo 0 1)
    (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i) (K : ∀ i, κ i → Matrix m (n i) ℂ)
    (M U : ∀ i, selfAdjoint (Matrix (n i) (n i) ℂ))
    (hM : ∀ i, (M i : Matrix (n i) (n i) ℂ).PosDef) :
    0 ≤ totalCurvature β c K M U := by
  have h := total_variational_le hβ c hc K M U hM
    (show (0 : Matrix m m ℂ).IsHermitian from by simp [Matrix.IsHermitian])
  simp only [variational, realTrace_zero, mul_zero, sylvester_apply, Matrix.zero_mul,
    add_zero, sub_zero] at h
  linarith

/-- The aggregate metric estimate for actual nonlinear carriers. Only the
total output must be positive definite, so singular individual outputs
are handled directly by their summed Gram representation. -/
theorem total_energy_le {β : ℝ} (hβ : β ∈ Ioo 0 1)
    (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i) (K : ∀ i, κ i → Matrix m (n i) ℂ)
    (M U : ∀ i, selfAdjoint (Matrix (n i) (n i) ℂ))
    (hM : ∀ i, (M i : Matrix (n i) (n i) ℂ).PosDef)
    (hP : (totalSource β c K M).PosDef) :
    energy (totalSource β c K M) hP (totalDefect β c K M U) ≤
      (1 - β) / (2 * β) * totalCurvature β c K M U :=
  energy_le_of_source_variational _ _ hP (totalDefect_isHermitian hβ c K M U hM)
    hβ.1 hβ.2 (fun _ hY => total_variational_le hβ c hc K M U hM hY)

/-- The scalar aggregate estimate follows from testing the actual matrix
variational estimate on scalar multiples of the identity. It also covers
singular total outputs. -/
theorem total_trace_sq_le {β : ℝ} (hβ : β ∈ Ioo 0 1)
    (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i) (K : ∀ i, κ i → Matrix m (n i) ℂ)
    (M U : ∀ i, selfAdjoint (Matrix (n i) (n i) ℂ))
    (hM : ∀ i, (M i : Matrix (n i) (n i) ℂ).PosDef) :
    (realTrace (totalDefect β c K M U)) ^ 2 ≤
      (1 - β) / β * realTrace (totalSource β c K M) * totalCurvature β c K M U :=
  trace_sq_le_of_source_variational _ _ hβ.1
    (fun _ hY => total_variational_le hβ c hc K M U hM hY)

/-- Scalar aggregation with arbitrary signed label probes. The quadratic
budget keeps the original labels and needs no invertibility assumptions. -/
theorem scalar_probe_sq_le {β : ℝ} (hβ : β ∈ Ioo 0 1)
    (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i) (b : ι → ℝ)
    (K : ∀ i, κ i → Matrix m (n i) ℂ)
    (M U : ∀ i, selfAdjoint (Matrix (n i) (n i) ℂ))
    (hM : ∀ i, (M i : Matrix (n i) (n i) ℂ).PosDef) :
    (∑ i, c i * b i * realTrace (krausMap (K i)
      (CarrierMetric.first β (M i) (U i) -
        (realTrace (U i : Matrix (n i) (n i) ℂ) /
          realTrace (M i : Matrix (n i) (n i) ℂ)) • CarrierMetric.carrier β (M i)))) ^ 2 ≤
      (1 - β) / β *
        (∑ i, c i * b i ^ 2 * realTrace (krausMap (K i) (CarrierMetric.carrier β (M i)))) *
        totalCurvature β c K M U :=
  trace_probe_sq_le_of_variational _ _ _ c b hc hβ.1
    (fun i _ hY => CarrierMetric.carrier_variational_le hβ (K i) (M i) (U i) (hM i) hY)

/-- Source curvature absorbs the internal source response with the exact
coefficient beta in the actual supported inverse-Sylvester metric. -/
theorem total_source_absorption {β : ℝ} (hβ : β ∈ Ioo 0 1)
    (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i) (K : ∀ i, κ i → Matrix m (n i) ℂ)
    (M U : ∀ i, selfAdjoint (Matrix (n i) (n i) ℂ))
    (hM : ∀ i, (M i : Matrix (n i) (n i) ℂ).PosDef)
    (hP : (totalSource β c K M).PosDef)
    {X : Matrix m m ℂ} (hX : X.IsHermitian) :
    β * energy (totalSource β c K M) hP X ≤
      energy (totalSource β c K M) hP (X - totalDefect β c K M U) +
        totalCurvature β c K M U / 2 :=
  source_metric_absorption _ hP hX (totalDefect_isHermitian hβ c K M U hM)
    hβ.1 hβ.2 (total_energy_le hβ c hc K M U hM hP)

end HigherRankKS.SourceMetricAggregation
