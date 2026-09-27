import MatrixSpencer.CompactTaylor
import MatrixSpencer.JointOwnerResponse
import MatrixSpencer.CovarianceGram
import MatrixSpencer.CoefficientResponse
import MatrixSpencer.CovarianceCompactChart

/-! Compact uniform matched-step Taylor expansion of the actual owner potential. -/

open Set Filter Matrix
open scoped Topology ContDiff MatrixOrder ComplexOrder Matrix.Norms.L2Operator

namespace MatrixSpencer
noncomputable section
set_option maxHeartbeats 800000

section FiberCalculus
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem fderiv_fiber_fst_apply (f : X × Y → ℝ) (x v : X) (y : Y)
    (hf : ContDiffAt ℝ 2 f (x, y)) :
    fderiv ℝ (fun z => f (z, y)) x v = fderiv ℝ f (x, y) (v, 0) := by
  have hd := (hf.differentiableAt (by norm_num)).hasFDerivAt.comp x
    ((hasFDerivAt_id x).prodMk (hasFDerivAt_const (𝕜 := ℝ) y x))
  exact DFunLike.congr_fun hd.fderiv v

theorem fderiv_fiber_snd_apply (f : X × Y → ℝ) (x : X) (y v : Y)
    (hf : ContDiffAt ℝ 2 f (x, y)) :
    fderiv ℝ (fun z => f (x, z)) y v = fderiv ℝ f (x, y) (0, v) := by
  have hd := (hf.differentiableAt (by norm_num)).hasFDerivAt.comp y
    ((hasFDerivAt_const (𝕜 := ℝ) x y).prodMk (hasFDerivAt_id y))
  exact DFunLike.congr_fun hd.fderiv v

/-- The actual joint Hessian on a center fiber is the actual fiber Hessian. -/
theorem fderiv_fderiv_fiber_fst_quadratic (f : X × Y → ℝ) (x v : X) (y : Y)
    (hf : ContDiffAt ℝ 2 f (x, y)) :
    fderiv ℝ (fderiv ℝ f) (x, y) (v, 0) (v, 0) =
      fderiv ℝ (fderiv ℝ (fun z => f (z, y))) x v v := by
  have hpart : ContDiffAt ℝ 2 (fun z => f (z, y)) x :=
    hf.comp x (contDiffAt_id.prodMk contDiffAt_const)
  have hfull := iteratedDeriv_comp_matchedCurve_two_zero f ((x, y), (v, 0), 0) hf
  have hfiber := iteratedDeriv_comp_matchedCurve_two_zero (fun z => f (z, y)) (x, v, 0) hpart
  have hefun : (fun h => f (matchedCurve ((x, y), (v, 0), (0 : X × Y)) h)) =
      (fun h => f (matchedCurve (x, v, (0 : X)) h, y)) := by
    funext h
    simp [matchedCurve]
  rw [hefun] at hfull
  simpa only [map_zero, mul_zero, add_zero] using hfull.symm.trans hfiber
end FiberCalculus

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n]
local instance matchedOwnerCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance matchedOwnerPhysicalGroup : NormedAddCommGroup (selfAdjoint (Matrix n n ℂ)) := inferInstance
local instance matchedOwnerCoeffGroup : NormedAddCommGroup (selfAdjoint (Matrix ι ι ℝ)) := inferInstance
local instance matchedOwnerPhysicalSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance
local instance matchedOwnerCoeffSpace : NormedSpace ℝ (selfAdjoint (Matrix ι ι ℝ)) := inferInstance
local instance matchedOwnerPhysicalFinite : FiniteDimensional ℝ (selfAdjoint (Matrix n n ℂ)) :=
  inferInstanceAs (FiniteDimensional ℝ (selfAdjoint.submodule ℝ (Matrix n n ℂ)))
local instance matchedOwnerCoeffFinite : FiniteDimensional ℝ (selfAdjoint (Matrix ι ι ℝ)) :=
  inferInstanceAs (FiniteDimensional ℝ (selfAdjoint.submodule ℝ (Matrix ι ι ℝ)))

/-- State `(H,C)` with bounded or finitely many perturbations `(V,Q)`. -/
abbrev OwnerTaylorData (ι n : Type*) [Fintype ι] [Fintype n] :=
  (selfAdjoint (Matrix n n ℂ) × selfAdjoint (Matrix ι ι ℝ)) ×
    selfAdjoint (Matrix n n ℂ) × selfAdjoint (Matrix ι ι ℝ)

/-- The matched owner step: linear center displacement and quadratic covariance shaving. -/
def ownerMatchedPoint (p : OwnerTaylorData ι n) (h : ℝ) :=
  (p.1.1 + h • p.2.1, p.1.2 - h ^ 2 • p.2.2)

/-- The actual linear coefficient of the optimized potential. -/
def ownerMatchedLinear [Nonempty n] (A : ι → Matrix n n ℂ) (θ : ℝ) (p : OwnerTaylorData ι n) : ℝ :=
  tracePairing (hermitianDensityOptimizer p.1.1 (covarianceKraus A p.1.2) θ) p.2.1

/-- The actual second-order drift: half the center Hessian less covariance payment. -/
def ownerMatchedDrift [Nonempty n] (A : ι → Matrix n n ℂ) (θ : ℝ) (p : OwnerTaylorData ι n) : ℝ :=
  (1 / 2 : ℝ) * ownerCenterHessian A p.1.2 θ p.1.1 p.2.1 p.2.1 -
    covarianceDerivativeFunctional A p.1.2
      (hermitianDensityOptimizer p.1.1 (covarianceKraus A p.1.2) θ) p.2.2

/-- Embedding matched owner data into the generic quadratic-curve parameter space. -/
def ownerTaylorEmbedding (p : OwnerTaylorData ι n) :=
  (p.1, (p.2.1, (0 : selfAdjoint (Matrix ι ι ℝ))), ((0 : selfAdjoint (Matrix n n ℂ)), -p.2.2))

omit [DecidableEq ι] [DecidableEq n] in
theorem continuous_ownerTaylorEmbedding : Continuous (ownerTaylorEmbedding (ι := ι) (n := n)) := by
  unfold ownerTaylorEmbedding
  fun_prop

theorem ownerTaylorEmbedding_curve (p : OwnerTaylorData ι n) (h : ℝ) :
    matchedCurve (ownerTaylorEmbedding p) h = ownerMatchedPoint p h := by
  apply Prod.ext <;> simp [matchedCurve, ownerTaylorEmbedding, ownerMatchedPoint, sub_eq_add_neg]

theorem jointOwner_fderiv_center [Nonempty n] (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) {θ : ℝ} (hθ : 0 < θ)
    (H V : selfAdjoint (Matrix n n ℂ)) (C : selfAdjoint (Matrix ι ι ℝ))
    (hC : (C : Matrix ι ι ℝ).PosDef) :
    fderiv ℝ (jointHermitianOwnerPotential A θ) (H, C) (V, 0) =
      tracePairing (hermitianDensityOptimizer H (covarianceKraus A C) θ) V := by
  have hf : ContDiffAt ℝ 2 (jointHermitianOwnerPotential A θ) (H, C) :=
    (contDiffAt_jointHermitianOwnerPotential A hA hθ H C hC).of_le
      (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  rw [← fderiv_fiber_fst_apply _ H V C hf]
  change fderiv ℝ (ownerPotentialAsCenter A C θ) H V = _
  rw [ownerPotentialAsCenter_eq A hA hC.posSemidef θ,
    (hasFDerivAt_hermitianDensityPotential_source_unrestricted H (covarianceKraus A C) hθ).fderiv]
  rfl

theorem jointOwner_fderiv_covariance [Nonempty n] (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) {θ : ℝ} (hθ : 0 < θ)
    (H : selfAdjoint (Matrix n n ℂ)) (C Q : selfAdjoint (Matrix ι ι ℝ))
    (hC : (C : Matrix ι ι ℝ).PosDef) :
    fderiv ℝ (jointHermitianOwnerPotential A θ) (H, C) (0, -Q) =
      -covarianceDerivativeFunctional A C (hermitianDensityOptimizer H (covarianceKraus A C) θ) Q := by
  have hf : ContDiffAt ℝ 2 (jointHermitianOwnerPotential A θ) (H, C) :=
    (contDiffAt_jointHermitianOwnerPotential A hA hθ H C hC).of_le
      (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  rw [← fderiv_fiber_snd_apply _ H C (-Q) hf]
  change fderiv ℝ (hermitianOwnerPotential H A θ) C (-Q) = _
  rw [(hasFDerivAt_hermitianOwnerPotential_covariance H A hA hθ C hC).fderiv, map_neg]

theorem jointOwner_fderiv_fderiv_center [Nonempty n] (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) {θ : ℝ} (hθ : 0 < θ)
    (H V : selfAdjoint (Matrix n n ℂ)) (C : selfAdjoint (Matrix ι ι ℝ))
    (hC : (C : Matrix ι ι ℝ).PosDef) :
    fderiv ℝ (fderiv ℝ (jointHermitianOwnerPotential A θ)) (H, C) (V, 0) (V, 0) =
      ownerCenterHessian A C θ H V V := by
  have hf : ContDiffAt ℝ 2 (jointHermitianOwnerPotential A θ) (H, C) :=
    (contDiffAt_jointHermitianOwnerPotential A hA hθ H C hC).of_le
      (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  exact fderiv_fderiv_fiber_fst_quadratic _ H V C hf

/-- One mesh works for every state and perturbation in any compact positive-covariance chart. -/
theorem compact_uniform_owner_matched_taylor [Nonempty n]
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) {θ : ℝ} (hθ : 0 < θ)
    (K : Set (OwnerTaylorData ι n)) (hK : IsCompact K)
    (hC : ∀ p ∈ K, (p.1.2 : Matrix ι ι ℝ).PosDef) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ p ∈ K, ∀ h ∈ Icc (0 : ℝ) δ,
      |jointHermitianOwnerPotential A θ (ownerMatchedPoint p h) -
        jointHermitianOwnerPotential A θ p.1 - h * ownerMatchedLinear A θ p -
        h ^ 2 * ownerMatchedDrift A θ p| ≤ ε * h ^ 2 := by
  have himg := hK.image (continuous_ownerTaylorEmbedding (ι := ι) (n := n))
  have hf : ∀ q ∈ ownerTaylorEmbedding '' K,
      ContDiffAt ℝ 2 (jointHermitianOwnerPotential A θ) q.1 := by
    rintro q ⟨p, hp, rfl⟩
    exact (contDiffAt_jointHermitianOwnerPotential A hA hθ p.1.1 p.1.2 (hC p hp)).of_le
      (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  obtain ⟨δ, hδ, hb⟩ := compact_uniform_matched_taylor_two (jointHermitianOwnerPotential A θ)
    (ownerTaylorEmbedding '' K) himg hf hε
  refine ⟨δ, hδ, ?_⟩
  intro p hp h hh
  have hbound := hb (ownerTaylorEmbedding p) ⟨p, hp, rfl⟩ h hh
  rw [ownerTaylorEmbedding_curve] at hbound
  change |jointHermitianOwnerPotential A θ (ownerMatchedPoint p h) -
      jointHermitianOwnerPotential A θ p.1 -
      h * fderiv ℝ (jointHermitianOwnerPotential A θ) p.1 (p.2.1, 0) -
      h ^ 2 * ((1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ (jointHermitianOwnerPotential A θ))
        p.1 (p.2.1, 0) (p.2.1, 0) + fderiv ℝ (jointHermitianOwnerPotential A θ) p.1 (0, -p.2.2))| ≤ _ at hbound
  rw [jointOwner_fderiv_center A hA hθ p.1.1 p.2.1 p.1.2 (hC p hp),
    jointOwner_fderiv_fderiv_center A hA hθ p.1.1 p.2.1 p.1.2 (hC p hp),
    jointOwner_fderiv_covariance A hA hθ p.1.1 p.1.2 p.2.2 (hC p hp)] at hbound
  exact hbound

/-- Uniform mesh on the actual bounded-center, positive-floor coefficient chart,
for all bounded physical and covariance directions. Set the floor to half an
owner's positive lower eigenvalue for the usual epoch chart. -/
theorem uniform_owner_matched_taylor_on_chart [Nonempty n]
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) {θ : ℝ} (hθ : 0 < θ)
    (R V Q : ℝ) {a : ℝ} (ha : 0 < a) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ p ∈ CovarianceCompactChart.parameterChart (n := n) R a V Q (1 : Matrix ι ι ℝ),
      ∀ h ∈ Icc (0 : ℝ) δ,
        |jointHermitianOwnerPotential A θ (ownerMatchedPoint p h) -
          jointHermitianOwnerPotential A θ p.1 - h * ownerMatchedLinear A θ p -
          h ^ 2 * ownerMatchedDrift A θ p| ≤ ε * h ^ 2 :=
  compact_uniform_owner_matched_taylor A hA hθ _
    (CovarianceCompactChart.isCompact_parameterChart R V Q ha.le 1)
    (fun _ hp => CovarianceCompactChart.parameterChart_posDef ha hp) hε

end
end MatrixSpencer
