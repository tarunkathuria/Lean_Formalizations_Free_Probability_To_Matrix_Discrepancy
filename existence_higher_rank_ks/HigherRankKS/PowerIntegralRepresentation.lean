import HigherRankKS.MatrixPowerConcavity
import MatrixSpencer.KSCompactResolvent

open Matrix MatrixSpencer Set Filter MeasureTheory
open scoped NNReal Topology MatrixOrder ComplexOrder Matrix.Norms.L2Operator unitInterval

noncomputable section
namespace HigherRankKS.PowerIntegralRepresentation

variable {n : Type*} [Fintype n] [DecidableEq n]
local instance : CStarAlgebra (Matrix n n ℂ) := {}

/-- Scalar information satisfied by the positive measure in the fractional
power integral representation.  Its existence is proved below. -/
def ScalarRepresentation (α : ℝ) (μ : Measure ℝ) : Prop :=
  ∀ x : ℝ, 0 ≤ x → IntegrableOn (fun t => Real.rpowIntegrand₀₁ α t x) (Ioi 0) μ ∧
    x ^ α = ∫ t in Ioi 0, Real.rpowIntegrand₀₁ α t x ∂μ

theorem exists_scalarRepresentation {α : ℝ} (hα : α ∈ Ioo 0 1) :
    ∃ μ : Measure ℝ, ScalarRepresentation α μ :=
  Real.exists_measure_rpow_eq_integral hα

/-- The same scalar measure gives the actual CFC matrix power, together
with matrix-valued Bochner integrability. -/
theorem matrix_representation {α : ℝ} (hα : α ∈ Ioo 0 1) (μ : Measure ℝ)
    (hμ : ScalarRepresentation α μ) (M : Matrix n n ℂ) (hM : M.PosSemidef) :
    IntegrableOn (fun t => cfcₙ (Real.rpowIntegrand₀₁ α t) M) (Ioi 0) μ ∧
      CFC.rpow M α = ∫ t in Ioi 0, cfcₙ (Real.rpowIntegrand₀₁ α t) M ∂μ := by
  nontriviality (Matrix n n ℂ)
  let maxr : ℝ := sSup (quasispectrum ℝ M)
  have hmax : 0 ≤ maxr :=
    le_csSup_of_le (b := 0) (IsCompact.bddAbove (quasispectrum.isCompact M))
      (by simp) (by simp)
  let bound : ℝ → ℝ := fun t => ‖Real.rpowIntegrand₀₁ α t maxr‖
  have hf : ContinuousOn (Function.uncurry (Real.rpowIntegrand₀₁ α))
      (Ioi (0 : ℝ) ×ˢ quasispectrum ℝ M) :=
    Real.continuousOn_rpowIntegrand₀₁_uncurry hα _
      (fun z hz => quasispectrum_nonneg_of_nonneg M hM.nonneg z hz)
  have hbound : ∀ᵐ t ∂μ.restrict (Ioi 0), ∀ z ∈ quasispectrum ℝ M,
      ‖Real.rpowIntegrand₀₁ α t z‖ ≤ bound t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    intro z hz
    have hz0 := quasispectrum_nonneg_of_nonneg M hM.nonneg z hz
    dsimp [bound]
    rw [abs_of_nonneg (Real.rpowIntegrand₀₁_nonneg hα.1 ht.le hz0),
      abs_of_nonneg (Real.rpowIntegrand₀₁_nonneg hα.1 ht.le hmax)]
    exact Real.rpowIntegrand₀₁_monotoneOn hα ht.le hz0 hmax
      (le_csSup (IsCompact.bddAbove (quasispectrum.isCompact M)) hz)
  have hfinite : HasFiniteIntegral bound (μ.restrict (Ioi 0)) := by
    rw [hasFiniteIntegral_norm_iff]
    exact (hμ maxr hmax).1.2
  have hzero : ∀ᵐ t ∂μ.restrict (Ioi 0), Real.rpowIntegrand₀₁ α t 0 = 0 := by simp
  refine ⟨integrableOn_cfcₙ measurableSet_Ioi _ bound M hf hzero hbound hfinite, ?_⟩
  let q : ℝ≥0 := ⟨α, hα.1.le⟩
  have hq : 0 < q := hα.1
  change M ^ (q : ℝ) = _
  rw [← CFC.nnrpow_eq_rpow hq, CFC.nnrpow_eq_cfcₙ_real M q hM.nonneg]
  calc
    cfcₙ (fun x : ℝ => x ^ (q : ℝ)) M =
        cfcₙ (fun x : ℝ => ∫ t in Ioi 0, Real.rpowIntegrand₀₁ α t x ∂μ) M := by
      apply cfcₙ_congr
      intro x hx
      exact (hμ x (quasispectrum_nonneg_of_nonneg M hM.nonneg x hx)).2
    _ = _ := cfcₙ_setIntegral measurableSet_Ioi _ bound M hf hzero hbound hfinite
      hM.isHermitian

/-- A concrete inverse identity that does not invoke scalar multiplication
rules for the totalized matrix inverse. -/
theorem inv_real_smul {M : Matrix n n ℂ} (hM : IsUnit M) {c : ℝ} (hc : c ≠ 0) :
    (c • M)⁻¹ = c⁻¹ • M⁻¹ := by
  letI : Invertible M := hM.invertible
  apply Matrix.inv_eq_right_inv
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Matrix.mul_inv_of_invertible, inv_mul_cancel₀ hc, one_smul]

/-- The CFC integrand is the actual unweighted resolvent kernel. -/
theorem cfc_integrand_eq_resolvent {α t : ℝ} (hα : α ∈ Ioo 0 1) (ht : 0 < t)
    (M : Matrix n n ℂ) (hM : M.PosSemidef) :
    cfcₙ (Real.rpowIntegrand₀₁ α t) M =
      t ^ (α - 1) • (M * (M + t • (1 : Matrix n n ℂ))⁻¹) := by
  have hQ : (M + t • (1 : Matrix n n ℂ)).PosDef :=
    Matrix.PosDef.posSemidef_add hM ((Matrix.PosDef.one).smul ht)
  letI : Invertible (M + t • (1 : Matrix n n ℂ)) := hQ.isUnit.invertible
  rw [CFC.cfcₙ_rpowIntegrand₀₁_eq_cfcₙ_rpowIntegrand₀₁_one hα ht M hM.nonneg]
  have hscaled : (t⁻¹ • M).PosSemidef := (smul_nonneg (inv_pos.mpr ht).le hM.nonneg).posSemidef
  have he : Real.rpowIntegrand₀₁ α 1 = fun x : ℝ => 1 - (1 + x)⁻¹ := by
    funext x
    simp [Real.rpowIntegrand₀₁]
  rw [he, cfc_resolvent_one hscaled]
  have hden : (1 : Matrix n n ℂ) + t⁻¹ • M = t⁻¹ • (M + t • 1) := by
    rw [smul_add, smul_smul, inv_mul_cancel₀ ht.ne', one_smul]
    exact add_comm _ _
  rw [hden, inv_real_smul hQ.isUnit (inv_ne_zero ht.ne'), inv_inv]
  have hid := Matrix.mul_inv_of_invertible (M + t • (1 : Matrix n n ℂ))
  simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul] at hid
  congr 1
  exact (eq_sub_iff_add_eq.mpr hid).symm

/-- Exact unweighted resolvent representation, with the same positive
measure that normalizes every scalar power. -/
theorem resolvent_representation {α : ℝ} (hα : α ∈ Ioo 0 1) (μ : Measure ℝ)
    (hμ : ScalarRepresentation α μ) (M : Matrix n n ℂ) (hM : M.PosSemidef) :
    IntegrableOn (fun t => t ^ (α - 1) •
      (M * (M + t • (1 : Matrix n n ℂ))⁻¹)) (Ioi 0) μ ∧
    CFC.rpow M α = ∫ t in Ioi 0, t ^ (α - 1) •
      (M * (M + t • (1 : Matrix n n ℂ))⁻¹) ∂μ := by
  have heq : (fun t => cfcₙ (Real.rpowIntegrand₀₁ α t) M) =ᶠ[ae (μ.restrict (Ioi 0))]
      (fun t => t ^ (α - 1) • (M * (M + t • (1 : Matrix n n ℂ))⁻¹)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact cfc_integrand_eq_resolvent hα ht M hM
  obtain ⟨hi, he⟩ := matrix_representation hα μ hμ M hM
  exact ⟨hi.congr heq, he.trans (integral_congr_ae heq)⟩

end HigherRankKS.PowerIntegralRepresentation
