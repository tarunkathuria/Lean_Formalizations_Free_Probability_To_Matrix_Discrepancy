import MatrixSpencer.KSEighthSmoothness
import MatrixSpencer.KSSupportedHessian

/-!
# Actual negative Hessian direction from the eighth-cube transport comparison

This reproduces the original two-block physical comparison and its supported
transport majorant, then uses smooth contact to obtain derivatives of the
actual retained-owner potential. It does not choose a compact minimizer or
invoke the full-cube algorithm. The failed eighth retirement inequalities
are the branch hypotheses; the numerical controller discharges them later.
-/

open Matrix Filter Topology
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
noncomputable section
namespace MatrixSpencer.KSEighthHessian
open KSEighthBlocks KSEighthActualState KSEighthFullSupport KSEighthLocalState

variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n] [Nonempty n]
local instance {k : Type*} [Fintype k] [DecidableEq k] : CStarAlgebra (Matrix k k ℂ) := {}

theorem exists_negative_second_curve [Nonempty ι]
    (Q : Matrix n n ℂ) (hQ : Q.IsHermitian) (v : ι → n → ℂ) (hv : ∀ i, v i ≠ 0)
    (x : ι → ℝ) (hx : ∀ i, |x i| ≤ (1 / 8 : ℝ)) {θ : ℝ} (hθ : 0 < θ)
    (hn₁ : ∀ i, KSEighthBalanced.owner x i * KSEighthBalanced.probe (KSEighthSupport.compressedVector v)
      (transport Q v x θ true) i < 1 / 8 - x i)
    (hn₂ : ∀ i, KSEighthBalanced.owner x i * KSEighthBalanced.probe (KSEighthSupport.compressedVector v)
      (transport Q v x θ false) i < 1 / 8 + x i) :
    ∃ h : ι → ℝ, h ≠ 0 ∧ deriv (curvePotential Q v θ x h) 0 = 0 ∧
      iteratedDeriv 2 (curvePotential Q v θ x h) 0 < 0 := by
  let vc := KSEighthSupport.compressedVector v
  let Ac := fun i => KSRankOne.atom (vc i)
  let S := fullDensity Q v x θ
  let V := fullEmbedding v
  let B := KSIndependentSource.family Ac
  let Z := fullTransport Q v x θ
  have hc := KSEighthBalanced.owner_pos x hx
  have hZ₁ := transport_posDef Q v hv x hx hθ true
  have hZ₂ := transport_posDef Q v hv x hx hθ false
  obtain ⟨h, U₁, U₂, hh, hU₁, hU₂, hzero₁, hzero₂, hneg⟩ :=
    KSEighthPhysicalDescent.exists_common_physical_descent vc
      (KSEighthSupport.compressedVector_ne_zero v hv) x hx
      (supportDensity Q v x θ true) (supportDensity Q v x θ false)
      (transport Q v x θ true) (transport Q v x θ false)
      (supportDensity_posDef Q v x hθ true) (supportDensity_posDef Q v x hθ false) hZ₁ hZ₂
      (transport_solve Q v hv x hx hθ true) (transport_solve Q v hv x hx hθ false) hn₁ hn₂
  refine ⟨h, hh, ?_⟩
  let U := KSEighthBlocks.blockDiag U₁ U₂
  let q := fun j : ι × Bool => realTrace (Z * B j)
  let r := fun j : ι × Bool => realTrace (B j * U)
  let xx := fun j : ι × Bool => x j.1
  let hh' := fun j : ι × Bool => h j.1
  let cc := fun j : ι × Bool => KSEighthBalanced.owner x j.1
  let L := fun t => covarianceKraus (family v) (KSIndependentSource.coefficientCovariance (curveOwners x h t))
  let Hh : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ) := ⟨signedLift Q, signedLift_isHermitian hQ⟩
  let Kh : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ) :=
    ⟨∑ i, h i • signedLift (KSRankOne.atom (v i)), by
      change (∑ i, h i • signedLift (KSRankOne.atom (v i)))ᴴ = ∑ i, h i • signedLift (KSRankOne.atom (v i))
      simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, star_trivial,
        fun i => (signedLift_isHermitian (KSRankOne.atom_isHermitian (v i))).eq]⟩
  let Ah : ι × Bool → selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ) := fun j => ⟨family v j, family_isHermitian v j⟩
  have hU : U.IsHermitian := blockDiag_isHermitian hU₁ hU₂
  have hZ : Z.PosDef := fullTransport_posDef Q v hv x hx hθ
  have hArecon : ∀ j, (Ah j : Matrix (n ⊕ n) (n ⊕ n) ℂ) = V * B j * Vᴴ :=
    fun j => (independent_atom_reconstruct v hv j).symm
  have hKrecon : (Kh : Matrix (n ⊕ n) (n ⊕ n) ℂ) =
      V * (∑ j, hh' j • (KSSignSymmetry.signMatrix * B j)) * Vᴴ := by
    simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
    trans ∑ j : ι × Bool, hh' j • (KSSignSymmetry.signMatrix * family v j)
    · exact (KSIndependentTransportCurve.sign_times_independent_sum _ h).symm
    · exact Finset.sum_congr rfl (fun j _ => congrArg (fun M => hh' j • M)
        (KSIndependentTransportCurve.independent_signed_reconstruct v hv j).symm)
  have hq₁ (i : ι) : q (i, true) = KSEighthBalanced.probe vc (transport Q v x θ true) i := by
    exact realTrace_mul_independent Ac Z (i, true)
  have hq₂ (i : ι) : q (i, false) = KSEighthBalanced.probe vc (transport Q v x θ false) i := by
    exact realTrace_mul_independent Ac Z (i, false)
  have hlegal : KSBalancedSpin.physicalForce B KSSignSymmetry.signMatrix 64 xx hh' q -
      Z⁻¹ * U * Z⁻¹ + KSBalancedSpin.source B cc U = 0 := by
    have he := physical_velocity_blocks Ac (1 : Matrix (supportIndex v) (supportIndex v) ℂ) (-1)
      hZ₁ hZ₂ U₁ U₂ 64 cc xx hh' q
    change KSBalancedSpin.physicalForce B KSSignSymmetry.signMatrix 64 xx hh' q -
      Z⁻¹ * U * Z⁻¹ + KSBalancedSpin.source B cc U = _ at he
    rw [he]
    simp only [xx, hh', cc, hq₁, hq₂]
    trans KSEighthBlocks.blockDiag (0 : Matrix (supportIndex v) (supportIndex v) ℂ) 0
    · exact congrArg₂ KSEighthBlocks.blockDiag hzero₁ hzero₂
    · ext a b
      cases a <;> cases b <;> rfl
  have hacc : realTrace ((Vᴴ * (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) * V) *
      KSBalancedSpin.physicalAcceleration B Z U 64 xx hh' q) < 0 := by
    have he := physical_acceleration_pairing_blocks Ac
      (Vᴴ * (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) * V) hZ₁ hZ₂ U₁ U₂ 64 xx hh' q
    change realTrace ((Vᴴ * (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) * V) *
      KSBalancedSpin.physicalAcceleration B Z U 64 xx hh' q) = _ at he
    rw [he]
    have hs := actual_density_compressed Q v x hx hθ
    change Vᴴ * (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) * V = _ at hs
    rw [hs]
    simpa only [blockDiag_toBlocks11, blockDiag_toBlocks22, xx, hh', hq₁, hq₂] using hneg
  have he (T : Matrix (n ⊕ n) (n ⊕ n) ℂ) :
      krausChannel (L 0) T = covarianceSource (family v) (covariance x) T := by
    dsimp only [L]
    rw [curveOwners_zero]
    exact (covarianceSource_eq_kraus _ (family_isHermitian v) (covariance_posSemidef x hx) T).symm
  have heq : curvePotential Q v θ x h =ᶠ[𝓝 (0 : ℝ)]
      (fun t => densityPotential (curveCenter Q v h t) (L t) θ) := by
    filter_upwards [eventually_curveOwners_pos hx h] with t hct
    exact ownerPotential_eq_densityPotential _ _ (family_isHermitian v)
      (KSIndependentSource.coefficientCovariance_posSemidef (fun i => (hct i).le)) θ
  have hsmooth : ContDiffAt ℝ 2 (curvePotential Q v θ x h) 0 :=
    (KSEighthSmoothness.contDiffAt_curvePotential Q hQ v hθ x h
      (fun i => (hx i).trans_lt (by norm_num))).of_le
      (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have hactual := KSSupportedHessian.deriv_zero_and_second_le_of_supported_curve
    (curveCenter Q v h) L V (fullEmbedding_isometry v) Hh Kh Ah hZ hU 64 xx hh' q r hθ S
    (fullDensity_posDef Q v x hθ) (fullDensity_trace Q v x θ)
    (by intro T hT; dsimp only [curveCenter, L]; rw [zero_smul, add_zero, curveOwners_zero]
        exact fullDensity_isMaxOn Q v x θ T hT)
    (by rw [he]; exact actual_source_posDef Q v hv x hx hθ)
    (by rw [he]; exact actual_transport_solve Q v hv x hx hθ)
    (by intro T hT; rw [he]; exact source_reconstruct v hv _ hT.isHermitian)
    (by filter_upwards [eventually_curveOwners_pos hx h] with t hct
        intro T hT
        rw [← covarianceSource_eq_kraus (family v) (family_isHermitian v)
          (KSIndependentSource.coefficientCovariance_posSemidef (fun i => (hct i).le))]
        exact source_reconstruct v hv _ hT.1.isHermitian)
    (by filter_upwards [eventually_curveOwners_pos hx h] with t hct
        exact KSSupportedCenterCurve.centerCurve_eq_supportedGradient V Hh Kh Ah B (L t)
          hZ.isHermitian hU 64 xx hh' t
          (KSIndependentTransportCurve.curve_sourceAdjoint v x h t (fun i => (hct i).le) hZ.isHermitian hU))
    (KSSupportedCenterCurve.centerVelocity_zero V Kh Ah B KSSignSymmetry.signMatrix hZ.isHermitian hU
      64 cc xx hh' q (fun j => rfl) hArecon hKrecon hlegal)
    (hsmooth.congr_of_eventuallyEq heq.symm)
  constructor
  · exact heq.deriv_eq.trans hactual.1
  · rw [heq.iteratedDeriv_eq 2]
    apply hactual.2.trans_lt
    rw [KSSupportedCenterCurve.centerAcceleration_pairing V (S : Matrix (n ⊕ n) (n ⊕ n) ℂ)
      Ah B hZ.isHermitian hU 64 xx hh' q hArecon]
    exact hacc

end MatrixSpencer.KSEighthHessian
