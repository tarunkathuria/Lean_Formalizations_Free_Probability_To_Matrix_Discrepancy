import MatrixSpencer.MatchedOwnerTaylor
import MatrixSpencer.DyadicJointOwnerResponse
import MatrixSpencer.DyadicCoefficientResponse

/-! Uniform matched-step Taylor expansion of the actual dyadic owner potential. -/
open Set Filter Matrix
open scoped Topology ContDiff MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace MatrixSpencer
noncomputable section
set_option maxHeartbeats 800000
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n]
local instance dyadicMatchedOwnerCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance dyadicMatchedOwnerPhysicalGroup : NormedAddCommGroup (selfAdjoint (Matrix n n ℂ)) := inferInstance
local instance dyadicMatchedOwnerCoeffGroup : NormedAddCommGroup (selfAdjoint (Matrix ι ι ℝ)) := inferInstance
local instance dyadicMatchedOwnerPhysicalSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance
local instance dyadicMatchedOwnerCoeffSpace : NormedSpace ℝ (selfAdjoint (Matrix ι ι ℝ)) := inferInstance
local instance dyadicMatchedOwnerPhysicalFinite : FiniteDimensional ℝ (selfAdjoint (Matrix n n ℂ)) :=
  inferInstanceAs (FiniteDimensional ℝ (selfAdjoint.submodule ℝ (Matrix n n ℂ)))
local instance dyadicMatchedOwnerCoeffFinite : FiniteDimensional ℝ (selfAdjoint (Matrix ι ι ℝ)) :=
  inferInstanceAs (FiniteDimensional ℝ (selfAdjoint.submodule ℝ (Matrix ι ι ℝ)))

/-- The actual linear coefficient of the optimized potential. -/
def dyadicOwnerMatchedLinear [Nonempty n] (A : ι → Matrix n n ℂ) (m : ℕ) (θ : ℝ) (p : OwnerTaylorData ι n) : ℝ :=
  tracePairing (hermitianDyadicDensityOptimizer p.1.1 (covarianceKraus A p.1.2) m θ) p.2.1

/-- The actual second-order drift: half the center Hessian less covariance payment. -/
def dyadicOwnerMatchedDrift [Nonempty n] (A : ι → Matrix n n ℂ) (m : ℕ) (θ : ℝ) (p : OwnerTaylorData ι n) : ℝ :=
  (1 / 2 : ℝ) * dyadicOwnerCenterHessian A p.1.2 m θ p.1.1 p.2.1 p.2.1 -
    covarianceDerivativeFunctional A p.1.2
      (hermitianDyadicDensityOptimizer p.1.1 (covarianceKraus A p.1.2) m θ) p.2.2

theorem jointDyadicOwner_fderiv_center [Nonempty n] (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (hθ : 0 < θ)
    (H V : selfAdjoint (Matrix n n ℂ)) (C : selfAdjoint (Matrix ι ι ℝ))
    (hC : (C : Matrix ι ι ℝ).PosDef) :
    fderiv ℝ (jointHermitianDyadicOwnerPotential A m θ) (H, C) (V, 0) =
      tracePairing (hermitianDyadicDensityOptimizer H (covarianceKraus A C) m θ) V := by
  have hf : ContDiffAt ℝ 2 (jointHermitianDyadicOwnerPotential A m θ) (H, C) :=
    (contDiffAt_jointHermitianDyadicOwnerPotential A hA m hm θ hθ H C hC).of_le
      (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  rw [← fderiv_fiber_fst_apply _ H V C hf]
  change fderiv ℝ (dyadicOwnerPotentialAsCenter A C m θ) H V = _
  rw [dyadicOwnerPotentialAsCenter_eq A hA hC.posSemidef m θ,
    (hasFDerivAt_hermitianDyadicDensityPotential H (covarianceKraus A C) m hm θ hθ).fderiv]
  rfl

theorem jointDyadicOwner_fderiv_covariance [Nonempty n] (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (hθ : 0 < θ)
    (H : selfAdjoint (Matrix n n ℂ)) (C Q : selfAdjoint (Matrix ι ι ℝ))
    (hC : (C : Matrix ι ι ℝ).PosDef) :
    fderiv ℝ (jointHermitianDyadicOwnerPotential A m θ) (H, C) (0, -Q) =
      -covarianceDerivativeFunctional A C (hermitianDyadicDensityOptimizer H (covarianceKraus A C) m θ) Q := by
  have hf : ContDiffAt ℝ 2 (jointHermitianDyadicOwnerPotential A m θ) (H, C) :=
    (contDiffAt_jointHermitianDyadicOwnerPotential A hA m hm θ hθ H C hC).of_le
      (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  rw [← fderiv_fiber_snd_apply _ H C (-Q) hf]
  change fderiv ℝ (hermitianDyadicOwnerPotential H A m θ) C (-Q) = _
  rw [(hasFDerivAt_hermitianDyadicOwnerPotential_covariance H A hA m hm θ hθ C hC).fderiv, map_neg]

theorem jointDyadicOwner_fderiv_fderiv_center [Nonempty n] (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (hθ : 0 < θ)
    (H V : selfAdjoint (Matrix n n ℂ)) (C : selfAdjoint (Matrix ι ι ℝ))
    (hC : (C : Matrix ι ι ℝ).PosDef) :
    fderiv ℝ (fderiv ℝ (jointHermitianDyadicOwnerPotential A m θ)) (H, C) (V, 0) (V, 0) =
      dyadicOwnerCenterHessian A C m θ H V V := by
  have hf : ContDiffAt ℝ 2 (jointHermitianDyadicOwnerPotential A m θ) (H, C) :=
    (contDiffAt_jointHermitianDyadicOwnerPotential A hA m hm θ hθ H C hC).of_le
      (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  exact fderiv_fderiv_fiber_fst_quadratic _ H V C hf

/-- One mesh works for every state and perturbation in any compact positive-covariance chart. -/
theorem compact_uniform_dyadicOwner_matched_taylor [Nonempty n]
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (hθ : 0 < θ)
    (K : Set (OwnerTaylorData ι n)) (hK : IsCompact K)
    (hC : ∀ p ∈ K, (p.1.2 : Matrix ι ι ℝ).PosDef) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ p ∈ K, ∀ h ∈ Icc (0 : ℝ) δ,
      |jointHermitianDyadicOwnerPotential A m θ (ownerMatchedPoint p h) -
        jointHermitianDyadicOwnerPotential A m θ p.1 - h * dyadicOwnerMatchedLinear A m θ p -
        h ^ 2 * dyadicOwnerMatchedDrift A m θ p| ≤ ε * h ^ 2 := by
  have himg := hK.image (continuous_ownerTaylorEmbedding (ι := ι) (n := n))
  have hf : ∀ q ∈ ownerTaylorEmbedding '' K,
      ContDiffAt ℝ 2 (jointHermitianDyadicOwnerPotential A m θ) q.1 := by
    rintro q ⟨p, hp, rfl⟩
    exact (contDiffAt_jointHermitianDyadicOwnerPotential A hA m hm θ hθ p.1.1 p.1.2 (hC p hp)).of_le
      (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  obtain ⟨δ, hδ, hb⟩ := compact_uniform_matched_taylor_two (jointHermitianDyadicOwnerPotential A m θ)
    (ownerTaylorEmbedding '' K) himg hf hε
  refine ⟨δ, hδ, ?_⟩
  intro p hp h hh
  have hbound := hb (ownerTaylorEmbedding p) ⟨p, hp, rfl⟩ h hh
  rw [ownerTaylorEmbedding_curve] at hbound
  change |jointHermitianDyadicOwnerPotential A m θ (ownerMatchedPoint p h) -
      jointHermitianDyadicOwnerPotential A m θ p.1 -
      h * fderiv ℝ (jointHermitianDyadicOwnerPotential A m θ) p.1 (p.2.1, 0) -
      h ^ 2 * ((1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ (jointHermitianDyadicOwnerPotential A m θ))
        p.1 (p.2.1, 0) (p.2.1, 0) + fderiv ℝ (jointHermitianDyadicOwnerPotential A m θ) p.1 (0, -p.2.2))| ≤ _ at hbound
  rw [jointDyadicOwner_fderiv_center A hA m hm θ hθ p.1.1 p.2.1 p.1.2 (hC p hp),
    jointDyadicOwner_fderiv_fderiv_center A hA m hm θ hθ p.1.1 p.2.1 p.1.2 (hC p hp),
    jointDyadicOwner_fderiv_covariance A hA m hm θ hθ p.1.1 p.1.2 p.2.2 (hC p hp)] at hbound
  exact hbound

/-- Uniform mesh on the actual bounded-center, positive-floor coefficient chart,
for all bounded physical and covariance directions. Set the floor to half an
owner's positive lower eigenvalue for the usual epoch chart. -/
theorem uniform_dyadicOwner_matched_taylor_on_chart [Nonempty n]
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (hθ : 0 < θ)
    (R V Q : ℝ) {a : ℝ} (ha : 0 < a) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ p ∈ CovarianceCompactChart.parameterChart (n := n) R a V Q (1 : Matrix ι ι ℝ),
      ∀ h ∈ Icc (0 : ℝ) δ,
        |jointHermitianDyadicOwnerPotential A m θ (ownerMatchedPoint p h) -
          jointHermitianDyadicOwnerPotential A m θ p.1 - h * dyadicOwnerMatchedLinear A m θ p -
          h ^ 2 * dyadicOwnerMatchedDrift A m θ p| ≤ ε * h ^ 2 :=
  compact_uniform_dyadicOwner_matched_taylor A hA m hm θ hθ _
    (CovarianceCompactChart.isCompact_parameterChart R V Q ha.le 1)
    (fun _ hp => CovarianceCompactChart.parameterChart_posDef ha hp) hε

end
end MatrixSpencer
