import HigherRankKS.MatrixPowerDifferential
import HigherRankKS.IntegratedSylvesterMetric

/-!
# Resolvent Gram representation of the actual power Hessian

The columns have finite carrier and output dimensions and an arbitrary
positive spectral measure. Their Gram integrals are identified with the
actual Fréchet Hessian proved in `MatrixPowerDifferential`; polarization
supplies mixed directions. The integrated completed square then bounds
each rectangular Kraus output without a derivative estimate assumption.
-/

open Matrix MatrixSpencer Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

noncomputable section
set_option maxHeartbeats 100000
namespace HigherRankKS.PowerGramMetric

open MatrixPowerDifferential IntegratedSylvesterMetric SylvesterMetric

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

def sandwich (K : Matrix m n ℂ) : Matrix n n ℂ →L[ℝ] Matrix m m ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => K * X * Kᴴ
      map_add' := by intro X Y; simp only [Matrix.mul_add, Matrix.add_mul]
      map_smul' := by intro r X; simp only [Matrix.mul_smul, Matrix.smul_mul]; rfl }

omit [DecidableEq n] [Fintype m] [DecidableEq m] in
@[simp] theorem sandwich_apply (K : Matrix m n ℂ) (X : Matrix n n ℂ) :
    sandwich K X = K * X * Kᴴ := rfl

def column (α : ℝ) (K : Matrix m n ℂ) (M U : selfAdjoint (Matrix n n ℂ))
    (t : ℝ) : Matrix m n ℂ :=
  Real.sqrt (2 * t ^ α) • resolventColumn K (resolvent M t) U

omit [Fintype m] [DecidableEq m] in
theorem column_gram {α t : ℝ} (K : Matrix m n ℂ)
    (M U : selfAdjoint (Matrix n n ℂ)) (hM : (M : Matrix n n ℂ).PosDef) (ht : 0 < t) :
    column α K M U t * (column α K M U t)ᴴ =
      sandwich K ((2 * t ^ α) • (resolvent M t * (U : Matrix n n ℂ) *
        resolvent M t * (U : Matrix n n ℂ) * resolvent M t)) := by
  rw [column, Matrix.conjTranspose_smul, star_trivial,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    ← sq, Real.sq_sqrt (by positivity),
    resolventColumn_product K (resolvent_posDef hM ht.le).posSemidef U.property]
  simp only [sandwich_apply, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]

omit [Fintype m] [DecidableEq m] in
theorem column_add (α : ℝ) (K : Matrix m n ℂ)
    (M U V : selfAdjoint (Matrix n n ℂ)) (t : ℝ) :
    column α K M (U + V) t = column α K M U t + column α K M V t := by
  simp only [column, resolventColumn, AddSubgroup.coe_add, Matrix.mul_add, Matrix.add_mul,
    smul_add]

theorem integrable_gram {α : ℝ} (hα : α ∈ Ioo 0 1) (μ : Measure ℝ)
    (hμ : PowerIntegralRepresentation.ScalarRepresentation α μ)
    (K : Matrix m n ℂ) (M U : selfAdjoint (Matrix n n ℂ))
    (hM : (M : Matrix n n ℂ).PosDef) :
    IntegrableOn (fun t => column α K M U t * (column α K M U t)ᴴ) (Ioi 0) μ := by
  have hi := (PowerIntegralDerivatives.iteratedDeriv_two_power_integral hα μ hμ hM U.property).1.neg
  apply ((sandwich K).integrable_comp hi).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [column_gram K M U hM ht]
  apply congrArg (sandwich K)
  simp only [Pi.neg_apply, neg_smul, neg_mul, neg_neg]

theorem integral_gram {α : ℝ} (hα : α ∈ Ioo 0 1) (μ : Measure ℝ)
    (hμ : PowerIntegralRepresentation.ScalarRepresentation α μ)
    (K : Matrix m n ℂ) (M U : selfAdjoint (Matrix n n ℂ))
    (hM : (M : Matrix n n ℂ).PosDef) :
    (∫ t in Ioi 0, column α K M U t * (column α K M U t)ᴴ ∂μ) =
      -(sandwich K (second α M U U)) := by
  have hi := (PowerIntegralDerivatives.iteratedDeriv_two_power_integral hα μ hμ hM U.property).1
  rw [second_diagonal_integral hα μ hμ M U hM,
    ← (sandwich K).integral_comp_comm hi, ← integral_neg]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [column_gram K M U hM ht]
  rw [← map_neg]
  apply congrArg (sandwich K)
  simp only [neg_smul, neg_mul, neg_neg]

omit [Fintype m] [DecidableEq m] in
theorem column_cross_eq (α : ℝ) (K : Matrix m n ℂ)
    (M U V : selfAdjoint (Matrix n n ℂ)) (t : ℝ) :
    column α K M U t * (column α K M V t)ᴴ +
      column α K M V t * (column α K M U t)ᴴ =
      column α K M (U + V) t * (column α K M (U + V) t)ᴴ -
        column α K M U t * (column α K M U t)ᴴ -
        column α K M V t * (column α K M V t)ᴴ := by
  rw [column_add]
  simp only [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add]
  abel

theorem integrable_cross {α : ℝ} (hα : α ∈ Ioo 0 1) (μ : Measure ℝ)
    (hμ : PowerIntegralRepresentation.ScalarRepresentation α μ)
    (K : Matrix m n ℂ) (M U V : selfAdjoint (Matrix n n ℂ))
    (hM : (M : Matrix n n ℂ).PosDef) :
    IntegrableOn (fun t => column α K M U t * (column α K M V t)ᴴ +
      column α K M V t * (column α K M U t)ᴴ) (Ioi 0) μ := by
  simp_rw [column_cross_eq]
  exact ((integrable_gram hα μ hμ K M (U + V) hM).sub
    (integrable_gram hα μ hμ K M U hM)).sub (integrable_gram hα μ hμ K M V hM)

theorem integral_cross {α : ℝ} (hα : α ∈ Ioo 0 1) (μ : Measure ℝ)
    (hμ : PowerIntegralRepresentation.ScalarRepresentation α μ)
    (K : Matrix m n ℂ) (M U V : selfAdjoint (Matrix n n ℂ))
    (hM : (M : Matrix n n ℂ).PosDef) :
    (∫ t in Ioi 0, column α K M U t * (column α K M V t)ᴴ +
      column α K M V t * (column α K M U t)ᴴ ∂μ) =
      (-2 : ℝ) • sandwich K (second α M U V) := by
  simp_rw [column_cross_eq]
  have hs : IntegrableOn (fun t =>
      column α K M (U + V) t * (column α K M (U + V) t)ᴴ -
        column α K M U t * (column α K M U t)ᴴ) (Ioi 0) μ :=
    (integrable_gram hα μ hμ K M (U + V) hM).sub (integrable_gram hα μ hμ K M U hM)
  rw [integral_sub hs (integrable_gram hα μ hμ K M V hM),
    integral_sub (integrable_gram hα μ hμ K M (U + V) hM)
      (integrable_gram hα μ hμ K M U hM),
    integral_gram hα μ hμ K M (U + V) hM, integral_gram hα μ hμ K M U hM,
    integral_gram hα μ hμ K M V hM]
  simp only [second, map_add, ContinuousLinearMap.add_apply]
  rw [show fderiv ℝ (fderiv ℝ (power α)) M V U =
    fderiv ℝ (fderiv ℝ (power α)) M U V from second_symm hα M V U hM]
  rw [show (-2 : ℝ) = -(1 + 1) by norm_num, neg_smul, add_smul, one_smul]
  abel

theorem first_isHermitian {α : ℝ} (hα : α ∈ Ioo 0 1)
    (M U : selfAdjoint (Matrix n n ℂ)) (hM : (M : Matrix n n ℂ).PosDef) :
    (first α M U).IsHermitian := by
  obtain ⟨μ, hμ⟩ := PowerIntegralRepresentation.exists_scalarRepresentation hα
  rw [first_integral hα μ hμ M U hM]
  apply integral_isHermitian _ _
    (PowerIntegralDerivatives.deriv_power_integral hα μ hμ hM U.property).1
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have hR := (resolvent_posDef hM ht.le).isHermitian
  have hH : (resolvent M t * (U : Matrix n n ℂ) * resolvent M t).IsHermitian := by
    simpa only [hR.eq] using
      Matrix.isHermitian_mul_mul_conjTranspose (resolvent M t)
        (show (U : Matrix n n ℂ).IsHermitian from U.property)
  exact (IsSelfAdjoint.all (t ^ α)).smul hH.isSelfAdjoint

/-- The integrated resolvent columns imply the variational metric bound
for a single rectangular Kraus operator, without output invertibility. -/
theorem single_variational_le {α : ℝ} (hα : α ∈ Ioo 0 1)
    (K : Matrix m n ℂ) (M U : selfAdjoint (Matrix n n ℂ))
    (hM : (M : Matrix n n ℂ).PosDef) {Y : Matrix m m ℂ} (hY : Y.IsHermitian) :
    variational ((α * (1 - α)) • sandwich K (power α M))
      ((2 * (1 - α)) • sandwich K (first α M U)) Y ≤
        2 * realTrace (-(sandwich K (second α M U U))) := by
  obtain ⟨μ, hμ⟩ := PowerIntegralRepresentation.exists_scalarRepresentation hα
  have hBi : Integrable (fun t : ℝ => realTrace
      (column α K M U t * (column α K M U t)ᴴ)) (μ.restrict (Ioi 0)) :=
    (realTraceCLM (n := m)).integrable_comp (integrable_gram hα μ hμ K M U hM)
  have h := integrated_crossGram_variational_le (n := m) (m := n) (T := ℝ)
    (μ.restrict (Ioi 0)) (column α K M M) (column α K M U)
    (integrable_gram hα μ hμ K M M hM)
    (integrable_cross hα μ hμ K M M U hM) hBi hY
  have hA : (∫ t in Ioi 0, column α K M M t * (column α K M M t)ᴴ ∂μ) =
      (α * (1 - α)) • sandwich K (power α M) := by
    rw [integral_gram hα μ hμ K M M hM, second_radial hα M M hM,
      first_radial hα M hM, map_smul, map_smul, smul_smul]
    rw [← neg_smul]
    apply congrArg (fun c : ℝ => c • sandwich K (power α M))
    ring
  have hR : (∫ t in Ioi 0, column α K M M t * (column α K M U t)ᴴ +
      column α K M U t * (column α K M M t)ᴴ ∂μ) =
      (2 * (1 - α)) • sandwich K (first α M U) := by
    rw [integral_cross hα μ hμ K M M U hM, second_symm hα M M U hM,
      second_radial hα M U hM, map_smul, smul_smul]
    apply congrArg (fun c : ℝ => c • sandwich K (first α M U))
    ring
  have hB := (realTraceCLM (n := m)).integral_comp_comm (integrable_gram hα μ hμ K M U hM)
  simp only [realTraceCLM_apply] at hB
  rw [integral_gram hα μ hμ K M U hM] at hB
  rwa [hA, hR, hB] at h

end HigherRankKS.PowerGramMetric
