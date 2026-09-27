import MatrixSpencer.FixedFaceOwnerTaylor

/-! Finite averaging of the actual fixed-face owner Taylor expansion. -/
open Set Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace MatrixSpencer
noncomputable section
set_option maxHeartbeats 800000

/-- Finite averaging only uses positive-weight branch bounds. -/
theorem finite_weighted_second_order_drift {σ : Type*} [Fintype σ]
    (w e l q : σ → ℝ) (h ε b : ℝ) (hw : ∀ s, 0 ≤ w s) (hsum : ∑ s, w s = 1)
    (hlin : ∑ s, w s * l s = 0) (hquad : ∑ s, w s * q s = b)
    (hbound : ∀ s, 0 < w s → e s ≤ h * l s + h ^ 2 * q s + ε * h ^ 2) :
    ∑ s, w s * e s ≤ h ^ 2 * b + ε * h ^ 2 := by
  calc
    _ ≤ ∑ s, w s * (h * l s + h ^ 2 * q s + ε * h ^ 2) := by
      apply Finset.sum_le_sum
      intro s _
      rcases eq_or_lt_of_le (hw s) with hs | hs
      · simp only [← hs, zero_mul, le_refl]
      · exact mul_le_mul_of_nonneg_left (hbound s hs) (hw s)
    _ = h * (∑ s, w s * l s) + h ^ 2 * (∑ s, w s * q s) + (∑ s, w s) * (ε * h ^ 2) := by
      simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro s _
      ring
    _ = _ := by rw [hlin, hquad, hsum]; ring

variable {ι κ n : Type*} [Fintype ι] [Fintype κ] [Fintype n]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq n]
local instance finiteOwnerDriftCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance finiteOwnerDriftPhysicalSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance
local instance finiteOwnerDriftCoeffSpace : NormedSpace ℝ (selfAdjoint (Matrix κ κ ℝ)) := inferInstance

/-- The physical displacement uses the original labels, independent of face coordinates. -/
def ownerPhysicalIncrement (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (u : EuclideanSpace ℝ ι) : selfAdjoint (Matrix n n ℂ) :=
  ∑ i, u i • hermitianMatrixFamily A hA i

def ownerPhysicalIncrementLinear (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) :
    EuclideanSpace ℝ ι →ₗ[ℝ] selfAdjoint (Matrix n n ℂ) where
  toFun := ownerPhysicalIncrement A hA
  map_add' u v := by simp [ownerPhysicalIncrement, add_smul, Finset.sum_add_distrib]
  map_smul' r u := by simp [ownerPhysicalIncrement, Finset.smul_sum, smul_smul]

omit [DecidableEq ι] in
/-- A deterministic bound suffices for selecting a uniform Taylor chart. -/
theorem ownerPhysicalIncrement_norm_le (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (u : EuclideanSpace ℝ ι) :
    ‖ownerPhysicalIncrement A hA u‖ ≤ ‖u‖ * ∑ i, ‖A i‖ := by
  calc
    _ ≤ ∑ i, ‖u i • hermitianMatrixFamily A hA i‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖u‖ * ‖A i‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (PiLp.norm_apply_le u i) (norm_nonneg (A i))
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- The covariance cap gives a common physical-direction bound for the finite sampler. -/
theorem covarianceSample_owner_norm_le (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) {Q : Matrix ι ι ℝ} (hQ : Q.PosSemidef)
    (hcap : Q ≤ 1) (s : ι × Bool) :
    ‖ownerPhysicalIncrement A hA (covarianceSampleIncrement hQ s)‖ ≤
      Real.sqrt (Fintype.card ι) * ∑ i, ‖A i‖ := by
  have htr : realTrace Q ≤ (Fintype.card ι : ℝ) := by
    have h := realTrace_mul_mono Matrix.PosSemidef.one hcap
    simpa only [Matrix.one_mul, realTrace, Matrix.trace_one, RCLike.natCast_re] using h
  have hn : ‖covarianceSampleIncrement hQ s‖ = Real.sqrt (realTrace Q) := by
    rw [← covarianceSample_norm_sq hQ s, Real.sqrt_sq (norm_nonneg _)]
  exact (ownerPhysicalIncrement_norm_le A hA _).trans
    (mul_le_mul_of_nonneg_right (hn.le.trans (Real.sqrt_le_sqrt htr))
      (Finset.sum_nonneg (fun i _ => norm_nonneg (A i))))

/-- Mean-zero coefficients cancel the actual first derivative in the full physical center. -/
theorem covarianceSample_owner_linear_mean (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) {Q : Matrix ι ι ℝ} (hQ : Q.PosSemidef)
    (S : selfAdjoint (Matrix n n ℂ)) :
    (∑ s, covarianceSampleWeight hQ s * tracePairing S
      (ownerPhysicalIncrement A hA (covarianceSampleIncrement hQ s))) = 0 := by
  have hm := covarianceSample_linear_mean Q hQ
    ((tracePairing (S : Matrix n n ℂ)).toLinearMap.comp (ownerPhysicalIncrementLinear A hA))
  simpa only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, ownerPhysicalIncrementLinear] using hm

/-- One mesh controls the expected actual potential increment for every bounded
state and spectral sampler in a fixed coefficient face. The PSD covariance
payment is discarded after proving its sign. -/
theorem uniform_covarianceSample_owner_drift_fixedFace [Nonempty n]
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) (U : Matrix ι κ ℝ)
    {θ : ℝ} (hθ : 0 < θ) (R V B : ℝ) {a : ℝ} (ha : 0 < a) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ (H : selfAdjoint (Matrix n n ℂ)) (K L : selfAdjoint (Matrix κ κ ℝ)),
      ‖H‖ ≤ R → a • (1 : Matrix κ κ ℝ) ≤ (K : Matrix κ κ ℝ) →
      (K : Matrix κ κ ℝ) ≤ 1 → ‖L‖ ≤ B → (L : Matrix κ κ ℝ).PosSemidef →
      ∀ (Q : Matrix ι ι ℝ) (hQ : Q.PosSemidef), Q = covarianceLift U L →
      0 < realTrace Q →
      (∀ s, 0 < covarianceSampleWeight hQ s →
        ‖ownerPhysicalIncrement A hA (covarianceSampleIncrement hQ s)‖ ≤ V) →
      ∀ h ∈ Icc (0 : ℝ) δ,
        (∑ s, covarianceSampleWeight hQ s *
          (ownerPotential (H + h • ownerPhysicalIncrement A hA (covarianceSampleIncrement hQ s)) A
              (covarianceLift U K - h ^ 2 • Q) θ - ownerPotential H A (covarianceLift U K) θ)) ≤
          h ^ 2 * realTrace (Q * ownerCoefficientResponse A hA (covarianceLift U K) θ H) + ε * h ^ 2 := by
  obtain ⟨δ, hδ, hb⟩ := uniform_owner_matched_taylor_fixedFace A hA U hθ R V B ha hε
  refine ⟨δ, hδ, ?_⟩
  intro H K L hH hfloor hcap hLnorm hL Q hQ hQl htrace hV h hh
  let S := hermitianDensityOptimizer H (covarianceKraus (mixFamily A U) K) θ
  let v := fun s => ownerPhysicalIncrement A hA (covarianceSampleIncrement hQ s)
  have hK : (K : Matrix κ κ ℝ).PosDef :=
    CovarianceCompactChart.posDef_of_scalar_floor ha hfloor
  have hpayment : 0 ≤ covarianceDerivativeFunctional (mixFamily A U) K S L :=
    covarianceDerivativeFunctional_nonneg (mixFamily A U) (mixFamily_isHermitian A U hA) hθ H K L hK hL
  apply finite_weighted_second_order_drift (covarianceSampleWeight hQ) _
    (fun s => tracePairing S (v s))
    (fun s => (1 / 2 : ℝ) * ownerCenterHessian A (covarianceLift U K) θ H (v s) (v s))
    h ε _ (covarianceSampleWeight_nonneg hQ htrace) (covarianceSampleWeight_sum hQ htrace)
    (covarianceSample_owner_linear_mean A hA hQ S)
    (covarianceSample_owner_hessian A hA (covarianceLift U K) θ H hQ htrace)
  intro s hs
  have hp : ((H, K), v s, L) ∈
      CovarianceCompactChart.parameterChart R a V B (1 : Matrix κ κ ℝ) := by
    exact ⟨⟨by simpa using hH, hfloor, hcap⟩,
      (by simpa only [Metric.mem_closedBall, dist_zero_right] using hV s hs),
      (by simpa only [Metric.mem_closedBall, dist_zero_right] using hLnorm)⟩
  have he := (abs_le.mp (hb ((H, K), v s, L) hp h hh)).2
  rw [← hQl] at he
  change ownerPotential (H + h • v s) A (covarianceLift U K - h ^ 2 • Q) θ -
      ownerPotential H A (covarianceLift U K) θ - h * tracePairing S (v s) -
      h ^ 2 * ((1 / 2 : ℝ) * ownerCenterHessian A (covarianceLift U K) θ H (v s) (v s) -
        covarianceDerivativeFunctional (mixFamily A U) K S L) ≤ ε * h ^ 2 at he
  have hpaid := mul_nonneg (sq_nonneg h) hpayment
  dsimp only [v]
  linarith

end
end MatrixSpencer
