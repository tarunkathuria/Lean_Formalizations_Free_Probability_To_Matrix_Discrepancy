import SeamlessKS.SourceTransport
import SeamlessKS.SourceCalculus
import MatrixSpencer.KSDebitSmoothness

/-! Actual smooth-source potential and its coefficient curves. -/
open Matrix Filter Topology
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
noncomputable section
namespace SeamlessKS.SmoothPotential
open MatrixSpencer MatrixSpencer.KSSpinLocalState MatrixSpencer.KSDebitLocalState
open SeamlessKS.SourceTransport

variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
local instance {k : Type*} [Fintype k] [DecidableEq k] : CStarAlgebra (Matrix k k ℂ) := {}

def curveWeights (ζ : ℝ) (x h : ι → ℝ) (t : ℝ) : ι → ℝ :=
  fun i => Source.weight 64 ζ (x i+t*h i)

def curveSlopes (ζ : ℝ) (x h : ι → ℝ) (i : ι) (t : ℝ) : ℝ :=
  Source.slope 64 ζ (x i+t*h i)*h i

def curveCurvatures (ζ : ℝ) (x h : ι → ℝ) (i : ι) : ℝ :=
  Source.curvature 64 ζ (x i)*h i^2

@[simp] theorem curveWeights_zero (ζ : ℝ) (x h : ι → ℝ) :
    curveWeights ζ x h 0 = smoothWeights ζ x := by
  funext i; simp [curveWeights, smoothWeights]

theorem hasDerivAt_curveWeights {ζ : ℝ} (hζ : 0 < ζ) (x h : ι → ℝ) (i : ι) (t : ℝ) :
    HasDerivAt (fun s => curveWeights ζ x h s i) (curveSlopes ζ x h i t) t := by
  have hl : HasDerivAt (fun s : ℝ => x i+s*h i) (h i) t := by
    simpa using ((hasDerivAt_id t).mul_const (h i)).const_add (x i)
  exact (Source.hasDerivAt_weight hζ 64 (x i+t*h i)).comp t hl

theorem hasDerivAt_curveSlopes {ζ : ℝ} (hζ : 0 < ζ) (x h : ι → ℝ) (i : ι) :
    HasDerivAt (curveSlopes ζ x h i) (curveCurvatures ζ x h i) 0 := by
  have hl : HasDerivAt (fun s : ℝ => x i+s*h i) (h i) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).mul_const (h i)).const_add (x i)
  have hh := ((Source.hasDerivAt_slope hζ 64 (x i+0*h i)).comp 0 hl).mul_const (h i)
  convert hh using 1 <;> simp [curveSlopes, curveCurvatures, pow_two, mul_assoc]

theorem contDiff_curveWeights {ζ : ℝ} (hζ : 0 < ζ) (x h : ι → ℝ) :
    ContDiff ℝ ∞ (curveWeights ζ x h) := by
  apply contDiff_pi.mpr
  intro i
  exact (Source.weight_contDiff hζ 64 ∞).comp (contDiff_const.add (contDiff_id.mul contDiff_const))

theorem eventually_curveWeights_pos {ζ : ℝ} (hζ : 0 < ζ)
    {x : ι → ℝ} (hx : ∀ i, |x i| < 1) (h : ι → ℝ) :
    ∀ᶠ t in 𝓝 (0:ℝ), ∀ i, 0 < curveWeights ζ x h t i := by
  rw [Filter.eventually_all]
  intro i
  have hc : Continuous (fun t => curveWeights ζ x h t i) :=
    (continuous_apply i).comp (contDiff_curveWeights hζ x h).continuous
  have hi : 0 < curveWeights ζ x h 0 i := by
    rw [curveWeights_zero]; exact Source.weight_pos (by norm_num) (hx i)
  exact hc.continuousAt.eventually (isOpen_Ioi.mem_nhds hi)

def curvePotential (M : Matrix (n ⊕ n) (n ⊕ n) ℂ) (v : ι → n → ℂ)
    (θ ζ : ℝ) (x h : ι → ℝ) (t : ℝ) : ℝ :=
  ownerPotential (curveCenter M v h t) (KSSpinSource.family (atoms v))
    (KSSpinSource.coefficientCovariance (curveWeights ζ x h t)) θ

theorem contDiffAt_curvePotential [Nonempty n]
    (M : Matrix (n ⊕ n) (n ⊕ n) ℂ) (hM : M.IsHermitian)
    (v : ι → n → ℂ) {θ ζ : ℝ} (hθ : 0 < θ) (hζ : 0 < ζ)
    (x h : ι → ℝ) (hx : ∀ i, |x i| < 1) :
    ContDiffAt ℝ ∞ (curvePotential M v θ ζ x h) 0 := by
  let Hh : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ) := ⟨M,hM⟩
  let Kh : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ) :=
    ⟨∑ i, h i • signedLift (atoms v i), by
      change (∑ i, h i • signedLift (atoms v i))ᴴ = ∑ i, h i • signedLift (atoms v i)
      simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, star_trivial]
      exact Finset.sum_congr rfl (fun i _ => congrArg (fun M => h i • M)
        (signedLift_isHermitian (KSRankOne.atom_isHermitian (v i))).eq)⟩
  let P := fun t : ℝ => (Hh+t • Kh,
    KSDebitSmoothness.coefficientCovarianceCLM (curveWeights ζ x h t))
  have hP : ContDiff ℝ ∞ P := by
    apply ContDiff.prodMk
    · exact contDiff_const.add (contDiff_id.smul contDiff_const)
    · exact KSDebitSmoothness.coefficientCovarianceCLM.contDiff.comp (contDiff_curveWeights hζ x h)
  have hC : ((P 0).2 : Matrix (ι × Fin 4) (ι × Fin 4) ℝ).PosDef := by
    change (KSSpinSource.coefficientCovariance (curveWeights ζ x h 0)).PosDef
    rw [curveWeights_zero]
    exact KSSpinCompression.coefficientCovariance_posDef
      (fun i => Source.weight_pos (by norm_num) (hx i))
  have hj := contDiffAt_jointHermitianOwnerPotential
    (KSSpinSource.family (atoms v))
    (KSSpinSource.family_isHermitian (atoms v) (fun i => KSRankOne.atom_isHermitian (v i)))
    hθ (P 0).1 (P 0).2 hC
  convert hj.comp 0 hP.contDiffAt using 1

theorem curve_sourceAdjoint (v : ι → n → ℂ) (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    {Z U : Matrix (KSSpinCompression.supportIndex (atoms v))
      (KSSpinCompression.supportIndex (atoms v)) ℂ}
    (hZ : Z.IsHermitian) (hU : U.IsHermitian) (t : ℝ) :
    KSSafeRetirement.sourceAdjoint
      (covarianceKraus (KSSpinSource.family (atoms v)) (KSSpinSource.coefficientCovariance c))
      (KSSpinCompression.embedding (atoms v)*KSMovingOwnerHessian.transportLine Z U t*
        (KSSpinCompression.embedding (atoms v))ᴴ) =
      ∑ i, (c i*realTrace (KSSpinCompression.compressedAtom (atoms v) i*
        KSMovingOwnerHessian.transportLine Z U t)) • KSSpinSource.doubled (atoms v i) := by
  rw [KSOwnerRetirement.sourceAdjoint_covarianceKraus (KSSpinSource.family (atoms v))
    (KSSpinSource.family_isHermitian (atoms v) (fun i => KSRankOne.atom_isHermitian (v i)))
    (KSSpinSource.coefficientCovariance_posSemidef hc)]
  trans ∑ i, (c i*realTrace (KSSpinSource.doubled (atoms v i)*
    (KSSpinCompression.embedding (atoms v)*KSMovingOwnerHessian.transportLine Z U t*
      (KSSpinCompression.embedding (atoms v))ᴴ))) • KSSpinSource.doubled (atoms v i)
  · exact KSSpinSource.source_eq_tracePrepare_real v c
      (Matrix.isHermitian_mul_mul_conjTranspose (KSSpinCompression.embedding (atoms v))
        (KSSupportedCenterCurve.transportLine_isHermitian hZ hU t))
  · simp only [KSSpinCompression.transport_probe]

end SeamlessKS.SmoothPotential
