import SeamlessKS.ActualHessian
import RadialKS.SourceTransport
open Matrix Filter Topology
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
noncomputable section
namespace RadialKS.ActualHessian

open MatrixSpencer MatrixSpencer.KSSpinLocalState MatrixSpencer.KSDebitLocalState
open SeamlessKS.SourceTransport SeamlessKS.SmoothPotential

variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
local instance {k : Type*} [Fintype k] [DecidableEq k] : CStarAlgebra (Matrix k k ℂ) := {}

/-- Failed local outward tests force a nonzero critical coefficient curve with
negative actual secondderivative. -/
theorem exists_negative_second_curve [Nonempty ι] [Nonempty n]
    (M : Matrix (n ⊕ n) (n ⊕ n) ℂ) (hMherm : M.IsHermitian)
    (hJM : Commute KSSignSymmetry.signMatrix M) (v : ι → n → ℂ) (hv : ∀ i, v i ≠ 0)
    (b x : ι → ℝ) (hx : ∀ i, |x i| < 1) {θ ζ a : ℝ} (hθ : 0 < θ)
    (hζ : 0 < ζ) (ha : 0 < a) (hscale : ζ ≤ a/10)
    (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) (hS : S.PosDef) (ht : realTrace S = 1)
    (hmax : ∀ T ∈ densitySet,
      ownerObjective M (KSSpinSource.family (atoms v))
        (KSSpinSource.coefficientCovariance (smoothWeights ζ x)) θ T ≤
      ownerObjective M (KSSpinSource.family (atoms v))
        (KSSpinSource.coefficientCovariance (smoothWeights ζ x)) θ S)
    (hfail : ∀ i, SeamlessKS.Source.secant 64 ζ |x i| a * realTrace (SeamlessKS.SourceTransport.stateTransport v (smoothWeights ζ x) S *
      KSSpinCompression.compressedAtom (atoms v) i) ≤ 1) :
    ∃ h : ι → ℝ, h ≠ 0 ∧ b ⬝ᵥ h = 0 ∧ deriv (SeamlessKS.SmoothPotential.curvePotential M v θ ζ x h) 0 = 0 ∧
      iteratedDeriv 2 (SeamlessKS.SmoothPotential.curvePotential M v θ ζ x h) 0 < 0 := by
  let V := KSSpinCompression.embedding (atoms v)
  let B := KSSpinCompression.compressedAtom (atoms v)
  let J := KSSpinCompression.compressedSign (atoms v)
  let Z := SeamlessKS.SourceTransport.stateTransport v (smoothWeights ζ x) S
  have hc : ∀ i, 0 < smoothWeights ζ x i := fun i => SeamlessKS.Source.weight_pos (by norm_num) (hx i)
  have hA := KSSpinSource.family_isHermitian (atoms v) (fun i => KSRankOne.atom_isHermitian (v i))
  have hC := KSSpinSource.coefficientCovariance_posSemidef (fun i => (hc i).le)
  have hJS := KSDebitCenter.optimizer_conjugate_eq_of_commute M hJM v
    (fun i => (hc i).le) hθ ⟨hS.posSemidef, ht⟩ hmax
  obtain ⟨h, U, hh, horth, hU, hlegal, hnegative⟩ := RadialKS.SourceTransport.actual_transport_descent_of_failed_secants v hv b x hx hζ ha hscale S hS hJS hfail
  refine ⟨h, hh, horth, ?_⟩
  let L := fun t => covarianceKraus (KSSpinSource.family (atoms v))
    (KSSpinSource.coefficientCovariance (curveWeights ζ x h t))
  let Hh : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ) := ⟨M, hMherm⟩
  let Kh : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ) :=
    ⟨∑ i, h i • signedLift (atoms v i), by
      change (∑ i, h i • signedLift (atoms v i))ᴴ = ∑ i, h i • signedLift (atoms v i)
      simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, star_trivial]
      exact Finset.sum_congr rfl (fun i _ => congrArg (fun M => h i • M)
        (signedLift_isHermitian (KSRankOne.atom_isHermitian (v i))).eq)⟩
  let Ah : ι → selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ) :=
    fun i => ⟨KSSpinSource.doubled (atoms v i), KSSpinSource.doubled_isHermitian (KSRankOne.atom_isHermitian _)⟩
  let Sh : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ) := ⟨S, hS.isHermitian⟩
  let q := fun i => realTrace (Z * B i)
  let r := fun i => realTrace (B i * U)
  have hV : Vᴴ * V = 1 := KSSpinCompression.embedding_isometry _
  have hS0 := KSSupportSymmetry.compress_posDef V hV hS
  have hM := KSSpinCompression.compressed_source_posDef v hc hS
  have hZ : Z.PosDef := transportOptimizer_posDef hS0 hM
  have hsolve := transportOptimizer_solve hS0 hM
  have he (T : Matrix (n ⊕ n) (n ⊕ n) ℂ) :
      krausChannel (L 0) T = covarianceSource (KSSpinSource.family (atoms v))
        (KSSpinSource.coefficientCovariance (smoothWeights ζ x)) T := by
    dsimp only [L]
    rw [curveWeights_zero, ← covarianceSource_eq_kraus _ hA hC]
  have hArecon : ∀ i, (Ah i : Matrix (n ⊕ n) (n ⊕ n) ℂ) = V * B i * Vᴴ :=
    fun i => (KSSpinCompression.compressedAtom_reconstruct (atoms v)
      (fun j => KSRankOne.atom_isHermitian (v j)) i).symm
  have hKrecon : (Kh : Matrix (n ⊕ n) (n ⊕ n) ℂ) = V * (∑ i, h i • (J * B i)) * Vᴴ := by
    simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
    exact Finset.sum_congr rfl (fun i _ => congrArg (fun M => h i • M) (signed_atom_reconstruct v i).symm)
  have heq : SeamlessKS.SmoothPotential.curvePotential M v θ ζ x h =ᶠ[𝓝 (0 : ℝ)]
      (fun t => densityPotential (KSDebitLocalState.curveCenter M v h t) (L t) θ) := by
    filter_upwards [eventually_curveWeights_pos hζ hx h] with t hct
    exact ownerPotential_eq_densityPotential _ _ hA
      (KSSpinSource.coefficientCovariance_posSemidef (fun i => (hct i).le)) θ
  have hsmooth : ContDiffAt ℝ 2 (SeamlessKS.SmoothPotential.curvePotential M v θ ζ x h) 0 :=
    (SeamlessKS.SmoothPotential.contDiffAt_curvePotential M hMherm v hθ hζ x h hx).of_le
      (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have hactual := SeamlessKS.SupportedHessian.deriv_zero_and_second_le_of_supported_curve
    (KSDebitLocalState.curveCenter M v h) L V hV Hh Kh Ah hZ hU
    (fun i t => curveWeights ζ x h t i) (curveSlopes ζ x h) (curveCurvatures ζ x h) q r
    (hasDerivAt_curveWeights hζ x h) (hasDerivAt_curveSlopes hζ x h)
    (fun i => ((SeamlessKS.Source.weight_contDiff hζ 64 2).comp
      (contDiff_const.add (contDiff_id.mul contDiff_const))).contDiffAt) hθ Sh hS ht
    (by intro T hT
        dsimp only [KSDebitLocalState.curveCenter, L]
        rw [zero_smul, add_zero, curveWeights_zero,
          ← ownerObjective_eq_densityObjective _ _ hA hC,
          ← ownerObjective_eq_densityObjective _ _ hA hC]
        exact hmax T hT)
    (by rw [he]; exact hM)
    (by rw [he]; exact hsolve)
    (by intro T hT; rw [he]; exact KSSpinCompression.source_reconstruct v (smoothWeights ζ x) T)
    (by filter_upwards [eventually_curveWeights_pos hζ hx h] with t hct
        intro T hT
        exact kraus_source_reconstruct v (curveWeights ζ x h t) (fun i => (hct i).le) T)
    (by filter_upwards [eventually_curveWeights_pos hζ hx h] with t hct
        exact SeamlessKS.TransportAlgebra.curve_eq_supportedGradient V Hh Kh Ah B (L t)
          hZ.isHermitian hU (fun i t => curveWeights ζ x h t i) t
          (SeamlessKS.SmoothPotential.curve_sourceAdjoint v (curveWeights ζ x h t) (fun i => (hct i).le) hZ.isHermitian hU t))
    (SeamlessKS.TransportAlgebra.velocity_zero V Kh Ah B J hZ.isHermitian hU 64
      (fun i t => curveWeights ζ x h t i) (curveSlopes ζ x h) (slopeParameter ζ x) h q
      (by intro i; simp [curveSlopes, slopeParameter]; ring) hArecon hKrecon
      (by simpa only [curveWeights_zero] using hlegal))
    (hsmooth.congr_of_eventuallyEq heq.symm)
  constructor
  · exact heq.deriv_eq.trans hactual.1
  · rw [heq.iteratedDeriv_eq 2]
    apply hactual.2.trans_lt
    apply (SeamlessKS.TransportAlgebra.acceleration_pairing_le V S Ah B hZ.isHermitian hU 64
      (fun i => curveSlopes ζ x h i 0) (curveCurvatures ζ x h) (slopeParameter ζ x) h q
      (by intro i; simp [curveSlopes, slopeParameter]; ring)
      (by intro i; have hh := mul_le_mul_of_nonneg_right
            (SeamlessKS.Source.curvature_upper (ζ := ζ) (by norm_num : (0:ℝ) ≤ 64) (x i)) (sq_nonneg (h i))
          simpa only [curveCurvatures, mul_assoc] using hh)
      (by intro i
          exact mul_nonneg (SeamlessKS.SourceTransport.probe_pos v hv hc hS i).le
            (realTrace_mul_nonneg hS.posSemidef
              (KSSpinSource.doubled_posSemidef (KSRankOne.atom_posSemidef (v i)))))
      hArecon).trans_lt hnegative

/-- The concrete full-cube algorithm's PSD debit satisfies the generalized
center hypotheses without any extra symmetry assumption. -/
theorem exists_negative_second_debit_curve [Nonempty ι] [Nonempty n]
    (H B : Matrix n n ℂ) (hH : H.IsHermitian) (hB : B.PosSemidef)
    (v : ι → n → ℂ) (hv : ∀ i, v i ≠ 0)
    (b x : ι → ℝ) (hx : ∀ i, |x i| < 1) {θ ζ a : ℝ} (hθ : 0 < θ)
    (hζ : 0 < ζ) (ha : 0 < a) (hscale : ζ ≤ a/10)
    (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) (hS : S.PosDef) (ht : realTrace S = 1)
    (hmax : ∀ T ∈ densitySet,
      ownerObjective (KSDebitCenter.center H B) (KSSpinSource.family (atoms v))
        (KSSpinSource.coefficientCovariance (smoothWeights ζ x)) θ T ≤
      ownerObjective (KSDebitCenter.center H B) (KSSpinSource.family (atoms v))
        (KSSpinSource.coefficientCovariance (smoothWeights ζ x)) θ S)
    (hfail : ∀ i, SeamlessKS.Source.secant 64 ζ |x i| a * realTrace (SeamlessKS.SourceTransport.stateTransport v (smoothWeights ζ x) S *
      KSSpinCompression.compressedAtom (atoms v) i) ≤ 1) :
    ∃ h : ι → ℝ, h ≠ 0 ∧ b ⬝ᵥ h = 0 ∧
      deriv (SeamlessKS.SmoothPotential.curvePotential (KSDebitCenter.center H B) v θ ζ x h) 0 = 0 ∧
      iteratedDeriv 2 (SeamlessKS.SmoothPotential.curvePotential (KSDebitCenter.center H B) v θ ζ x h) 0 < 0 :=
  exists_negative_second_curve (KSDebitCenter.center H B)
    (KSDebitCenter.center_isHermitian_of_posSemidef hH hB)
    (KSDebitCenter.signMatrix_commute_center H B) v hv b x hx hθ hζ ha hscale S hS ht hmax hfail

/-- The actual optimizer selected by the proved compact-attainment theorem.
This is an analytic definition, not a numerical evaluation procedure. -/
def actualOptimizer [Nonempty n]
    (M : Matrix (n ⊕ n) (n ⊕ n) ℂ) (v : ι → n → ℂ) (θ ζ : ℝ) (x : ι → ℝ) :=
  densityOptimizer M (covarianceKraus (KSSpinSource.family (atoms v))
    (KSSpinSource.coefficientCovariance (smoothWeights ζ x))) θ

/-- At the actual chosen optimizer, all positivity, trace, and maximizing
conditions are proved internally. Only the concrete failed local outward tests
remain as the hypothesis describing this branch of the walk. -/
theorem exists_negative_second_debit_curve_actual [Nonempty ι] [Nonempty n]
    (H B : Matrix n n ℂ) (hH : H.IsHermitian) (hB : B.PosSemidef)
    (v : ι → n → ℂ) (hv : ∀ i, v i ≠ 0)
    (b x : ι → ℝ) (hx : ∀ i, |x i| < 1) {θ ζ a : ℝ} (hθ : 0 < θ)
    (hζ : 0 < ζ) (ha : 0 < a) (hscale : ζ ≤ a/10)
    (hfail : ∀ i, SeamlessKS.Source.secant 64 ζ |x i| a * realTrace
      (SeamlessKS.SourceTransport.stateTransport v (smoothWeights ζ x) (actualOptimizer (KSDebitCenter.center H B) v θ ζ x) *
        KSSpinCompression.compressedAtom (atoms v) i) ≤ 1) :
    ∃ h : ι → ℝ, h ≠ 0 ∧ b ⬝ᵥ h = 0 ∧
      deriv (SeamlessKS.SmoothPotential.curvePotential (KSDebitCenter.center H B) v θ ζ x h) 0 = 0 ∧
      iteratedDeriv 2 (SeamlessKS.SmoothPotential.curvePotential
        (KSDebitCenter.center H B) v θ ζ x h) 0 < 0 := by
  let M := KSDebitCenter.center H B
  let A := KSSpinSource.family (atoms v)
  let C := KSSpinSource.coefficientCovariance (smoothWeights ζ x)
  let S := actualOptimizer M v θ ζ x
  have hA := KSSpinSource.family_isHermitian (atoms v)
    (fun i => KSRankOne.atom_isHermitian (v i))
  have hC : C.PosSemidef := KSSpinSource.coefficientCovariance_posSemidef
    (fun i => (SeamlessKS.Source.weight_pos (ζ := ζ) (by norm_num : (0:ℝ)<64) (hx i)).le)
  have hS : S.PosDef := densityOptimizer_posDef M (covarianceKraus A C) hθ
  have ht : realTrace S = 1 := (densityOptimizer_mem M (covarianceKraus A C) θ).2
  apply exists_negative_second_debit_curve H B hH hB v hv b x hx hθ hζ ha hscale S hS ht _ hfail
  intro T hT
  change ownerObjective M A C θ T ≤ ownerObjective M A C θ S
  rw [ownerObjective_eq_densityObjective M A hA hC,
    ownerObjective_eq_densityObjective M A hA hC]
  exact densityOptimizer_isMaxOn M (covarianceKraus A C) θ T hT

end RadialKS.ActualHessian
