import MatrixSpencer.KSEighthPhysicalDescent

/-! Exact independent sign-channel source identities for moving transports. -/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSIndependentTransportCurve
open KSEighthBlocks KSEighthActualState KSEighthFullSupport

variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n] [Nonempty n]

theorem source_eq_tracePrepare (v : ι → n → ℂ) (c : ι → ℝ)
    {X : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hX : X.IsHermitian) :
    covarianceSource (family v) (KSIndependentSource.coefficientCovariance c) X =
      ∑ j : ι × Bool, (c j.1 * realTrace (family v j * X)) • family v j := by
  unfold family
  rw [KSIndependentSource.source_eq_sum, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [KSEndpointRetirement.left_sandwich (v i) hX, KSEndpointRetirement.right_sandwich (v i) hX]
  simp only [Fintype.sum_bool, family, KSIndependentSource.family, if_true, Bool.false_eq_true,
    if_false, smul_add, smul_smul]
  abel

theorem sign_times_independent_sum (A : ι → Matrix n n ℂ) (h : ι → ℝ) :
    ∑ j : ι × Bool, h j.1 • (KSSignSymmetry.signMatrix * KSIndependentSource.family A j) =
      ∑ i, h i • signedLift (A i) := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Fintype.sum_bool, KSIndependentSource.family, if_true, Bool.false_eq_true, if_false]
  rw [← smul_add]
  congr 1
  simp [KSSignSymmetry.signMatrix, signedLift, leftDensity, rightDensity, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_add]

theorem independent_signed_reconstruct (v : ι → n → ℂ) (hv : ∀ i, v i ≠ 0)
    (j : ι × Bool) :
    fullEmbedding v * (KSSignSymmetry.signMatrix * KSIndependentSource.family
      (fun i => KSRankOne.atom (KSEighthSupport.compressedVector v i)) j) * (fullEmbedding v)ᴴ =
      KSSignSymmetry.signMatrix * family v j := by
  have hc : fullEmbedding v * KSSignSymmetry.signMatrix =
      KSSignSymmetry.signMatrix * fullEmbedding v := by
    simp [fullEmbedding, doubledRect, KSSignSymmetry.signMatrix, signedLift, Matrix.fromBlocks_multiply]
  rw [← Matrix.mul_assoc, hc, Matrix.mul_assoc, Matrix.mul_assoc]
  simpa only [Matrix.mul_assoc] using
    congrArg (fun M => KSSignSymmetry.signMatrix * M) (independent_atom_reconstruct v hv j)

theorem curve_sourceAdjoint (v : ι → n → ℂ) (x h : ι → ℝ) (t : ℝ)
    (hc : ∀ i, 0 ≤ 64 * (1 - (x i + t * h i) ^ 2))
    {Z U : Matrix (supportIndex v ⊕ supportIndex v) (supportIndex v ⊕ supportIndex v) ℂ}
    (hZ : Z.IsHermitian) (hU : U.IsHermitian) :
    KSSafeRetirement.sourceAdjoint (covarianceKraus (family v)
      (KSIndependentSource.coefficientCovariance (fun i => 64 * (1 - (x i + t * h i) ^ 2))))
      (fullEmbedding v * KSMovingOwnerHessian.transportLine Z U t * (fullEmbedding v)ᴴ) =
      ∑ j : ι × Bool, (64 * (1 - (x j.1 + t * h j.1) ^ 2) *
        realTrace (KSIndependentSource.family (fun i => KSRankOne.atom (KSEighthSupport.compressedVector v i)) j *
          KSMovingOwnerHessian.transportLine Z U t)) • family v j := by
  rw [KSOwnerRetirement.sourceAdjoint_covarianceKraus (family v) (family_isHermitian v)
    (KSIndependentSource.coefficientCovariance_posSemidef hc)]
  rw [source_eq_tracePrepare v _ (Matrix.isHermitian_mul_mul_conjTranspose _
    (KSSupportedCenterCurve.transportLine_isHermitian hZ hU t))]
  simp only [independent_probe]

end MatrixSpencer.KSIndependentTransportCurve
