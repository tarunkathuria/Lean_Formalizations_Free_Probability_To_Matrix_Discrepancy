import MatrixSpencer.KSSupportedCenterCurve
import MatrixSpencer.KSSpinCompression
import MatrixSpencer.KSStateRetirement

/-! Actual local spin state on a nonempty family of live original atoms. -/

open Matrix Filter Topology
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
noncomputable section
namespace MatrixSpencer.KSSpinLocalState

variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
local instance {k : Type*} [Fintype k] [DecidableEq k] : CStarAlgebra (Matrix k k ℂ) := {}

def atoms (v : ι → n → ℂ) : ι → Matrix n n ℂ := fun i => KSRankOne.atom (v i)
def owners (x : ι → ℝ) : ι → ℝ := fun i => 64 * (1 - x i ^ 2)
def ownerCurve (x h : ι → ℝ) (t : ℝ) : ι → ℝ := fun i => 64 * (1 - (x i + t * h i) ^ 2)

def stateTransport (v : ι → n → ℂ) (x : ι → ℝ)
    (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) :=
  transportOptimizer (KSSupportSymmetry.compress (KSSpinCompression.embedding (atoms v)) S)
    (covarianceCompressedSource (KSSpinSource.family (atoms v))
      (KSSpinSource.coefficientCovariance (owners x)) S)

def curveCenter (Q : Matrix n n ℂ) (v : ι → n → ℂ) (h : ι → ℝ) (t : ℝ) :=
  signedLift Q + t • (∑ i, h i • signedLift (atoms v i))

def curvePotential (Q : Matrix n n ℂ) (v : ι → n → ℂ) (θ : ℝ)
    (x h : ι → ℝ) (t : ℝ) : ℝ :=
  ownerPotential (curveCenter Q v h t) (KSSpinSource.family (atoms v))
    (KSSpinSource.coefficientCovariance (ownerCurve x h t)) θ

theorem owners_pos {x : ι → ℝ} (hx : ∀ i, |x i| < 1) (i : ι) : 0 < owners x i := by
  have hi := hx i
  have hs : x i ^ 2 < 1 := by nlinarith [sq_abs (x i), abs_nonneg (x i)]
  dsimp [owners]
  linarith

@[simp] theorem ownerCurve_zero (x h : ι → ℝ) : ownerCurve x h 0 = owners x := by
  funext i; simp only [ownerCurve, owners, zero_mul, add_zero]

theorem eventually_ownerCurve_pos {x : ι → ℝ} (hx : ∀ i, |x i| < 1) (h : ι → ℝ) :
    ∀ᶠ t in 𝓝 (0 : ℝ), ∀ i, 0 < ownerCurve x h t i := by
  rw [Filter.eventually_all]
  intro i
  have hc : Continuous (fun t : ℝ => ownerCurve x h t i) := by unfold ownerCurve; fun_prop
  have hi : 0 < ownerCurve x h 0 i := by rw [ownerCurve_zero]; exact owners_pos hx i
  exact hc.continuousAt.eventually (isOpen_Ioi.mem_nhds hi)

theorem signed_atom_reconstruct (v : ι → n → ℂ) (i : ι) :
    KSSpinCompression.embedding (atoms v) *
      (KSSpinCompression.compressedSign (atoms v) * KSSpinCompression.compressedAtom (atoms v) i) *
      (KSSpinCompression.embedding (atoms v))ᴴ = signedLift (atoms v i) := by
  let V := KSSpinCompression.embedding (atoms v)
  have hV := KSSpinCompression.embedding_isometry (atoms v)
  have hA : ∀ i, (atoms v i).IsHermitian := fun i => KSRankOne.atom_isHermitian (v i)
  have hi := KSSupportSymmetry.intertwine V hV KSSignSymmetry.signMatrix
    (KSSpinCompression.projection_commute_sign (atoms v) hA)
  change V * KSSpinCompression.compressedSign (atoms v) = KSSignSymmetry.signMatrix * V at hi
  change V * (KSSpinCompression.compressedSign (atoms v) * _) * Vᴴ = _
  rw [← Matrix.mul_assoc V, hi]
  rw [Matrix.mul_assoc KSSignSymmetry.signMatrix V,
    Matrix.mul_assoc KSSignSymmetry.signMatrix, KSSpinCompression.compressedAtom_reconstruct (atoms v) hA]
  simp [KSSignSymmetry.signMatrix, signedLift, KSSpinSource.doubled, Matrix.fromBlocks_multiply]

theorem curve_sourceAdjoint (v : ι → n → ℂ) (x h : ι → ℝ) (t : ℝ)
    (hc : ∀ i, 0 ≤ ownerCurve x h t i)
    {Z U : Matrix (KSSpinCompression.supportIndex (atoms v))
      (KSSpinCompression.supportIndex (atoms v)) ℂ}
    (hZ : Z.IsHermitian) (hU : U.IsHermitian) :
    KSSafeRetirement.sourceAdjoint
      (covarianceKraus (KSSpinSource.family (atoms v))
        (KSSpinSource.coefficientCovariance (ownerCurve x h t)))
      (KSSpinCompression.embedding (atoms v) * KSMovingOwnerHessian.transportLine Z U t *
        (KSSpinCompression.embedding (atoms v))ᴴ) =
      ∑ i, (64 * (1 - (x i + t * h i) ^ 2) *
        realTrace (KSSpinCompression.compressedAtom (atoms v) i * KSMovingOwnerHessian.transportLine Z U t)) •
          KSSpinSource.doubled (atoms v i) := by
  rw [KSOwnerRetirement.sourceAdjoint_covarianceKraus (KSSpinSource.family (atoms v))
    (KSSpinSource.family_isHermitian (atoms v) (fun i => KSRankOne.atom_isHermitian (v i)))
    (KSSpinSource.coefficientCovariance_posSemidef hc)]
  trans ∑ i, (ownerCurve x h t i * realTrace (KSSpinSource.doubled (atoms v i) *
    (KSSpinCompression.embedding (atoms v) * KSMovingOwnerHessian.transportLine Z U t *
      (KSSpinCompression.embedding (atoms v))ᴴ))) • KSSpinSource.doubled (atoms v i)
  · exact KSSpinSource.source_eq_tracePrepare_real v (ownerCurve x h t)
      (Matrix.isHermitian_mul_mul_conjTranspose (KSSpinCompression.embedding (atoms v))
        (KSSupportedCenterCurve.transportLine_isHermitian hZ hU t))
  · simp only [KSSpinCompression.transport_probe, ownerCurve]

theorem kraus_source_reconstruct (v : ι → n → ℂ) (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    (X : Matrix (n ⊕ n) (n ⊕ n) ℂ) :
    let V := KSSpinCompression.embedding (atoms v)
    let L := covarianceKraus (KSSpinSource.family (atoms v)) (KSSpinSource.coefficientCovariance c)
    V * (Vᴴ * krausChannel L X * V) * Vᴴ = krausChannel L X := by
  dsimp only
  rw [← covarianceSource_eq_kraus (KSSpinSource.family (atoms v))
    (KSSpinSource.family_isHermitian (atoms v) (fun i => KSRankOne.atom_isHermitian (v i)))
    (KSSpinSource.coefficientCovariance_posSemidef hc)]
  exact KSSpinCompression.source_reconstruct v c X

theorem actual_transport_descent [Nonempty ι] (v : ι → n → ℂ) (hv : ∀ i, v i ≠ 0)
    (x : ι → ℝ) (hx : ∀ i, |x i| < 1)
    (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) (hS : S.PosDef)
    (hJS : KSSignSymmetry.conjugate KSSignSymmetry.signMatrix S = S)
    (hfail : ∀ i, owners x i * realTrace (stateTransport v x S *
      KSSpinCompression.compressedAtom (atoms v) i) < 1 - |x i|) :
    let V := KSSpinCompression.embedding (atoms v)
    let B := KSSpinCompression.compressedAtom (atoms v)
    let J := KSSpinCompression.compressedSign (atoms v)
    let Z := stateTransport v x S
    ∃ h : ι → ℝ, ∃ U : Matrix (KSSpinCompression.supportIndex (atoms v))
        (KSSpinCompression.supportIndex (atoms v)) ℂ,
      h ≠ 0 ∧ U.IsHermitian ∧
      KSBalancedSpin.physicalForce B J 64 x h (fun i => realTrace (Z * B i)) -
        Z⁻¹ * U * Z⁻¹ + KSBalancedSpin.source B (owners x) U = 0 ∧
      realTrace ((Vᴴ * S * V) * KSBalancedSpin.physicalAcceleration B Z U 64 x h
        (fun i => realTrace (Z * B i))) < 0 := by
  let V := KSSpinCompression.embedding (atoms v)
  let B := KSSpinCompression.compressedAtom (atoms v)
  let S0 := KSSupportSymmetry.compress V S
  let M := covarianceCompressedSource (KSSpinSource.family (atoms v))
    (KSSpinSource.coefficientCovariance (owners x)) S
  let Z := stateTransport v x S
  have hc := owners_pos hx
  have hS0 : S0.PosDef := KSSupportSymmetry.compress_posDef V (KSSpinCompression.embedding_isometry _) hS
  have hM : M.PosDef := KSSpinCompression.compressed_source_posDef v hc hS
  have hZ : Z.PosDef := transportOptimizer_posDef hS0 hM
  have hBe : ∀ i, B i ≠ 0 := fun i => KSSpinCompression.compressedAtom_ne_zero (atoms v)
    (fun j => KSRankOne.atom_isHermitian (v j)) i
      (fun hz => hv i ((KSRankOne.atom_eq_zero_iff (v i)).mp hz))
  have hBp : ∀ i, (B i).PosSemidef := KSSpinCompression.compressedAtom_posSemidef (atoms v)
    (fun i => KSRankOne.atom_posSemidef (v i))
  have hsource : M = KSBalancedSpin.source B (owners x) S0 :=
    KSSpinCompression.compressed_source v (owners x) hS.isHermitian
  have hsolve : Z * KSBalancedSpin.source B (owners x) S0 * Z = S0 := by
    rw [← hsource]
    exact transportOptimizer_solve hS0 hM
  have hq : ∀ i, 0 < realTrace (Z * B i) := fun i =>
    KSBalancedSpin.realTrace_mul_pos_of_posDef hZ (hBp i) (hBe i)
  have hbds := fun i => KSPotentialModels.spin_noSafe_scalar_bounds (hx i) (hq i) (hfail i)
  apply KSSpinActualDescent.exists_transport_descent B (owners x) hBp hBe hc hS0 hZ hsolve
    (KSSpinCompression.compressedSign_isHermitian (atoms v))
    (KSSpinCompression.compressedSign_sq (atoms v) (fun i => KSRankOne.atom_isHermitian (v i)))
    (KSSpinCompression.compressedSign_commute_transport v hc hS hJS).eq
    (fun i => (KSSpinCompression.compressedSign_commute_atom (atoms v)
      (fun j => KSRankOne.atom_isHermitian (v j)) i).eq) x (fun i => (hbds i).2)
  intro i
  rw [KSBalancedSpin.trace_atom B (owners x) hZ i, mul_pow, Real.sq_sqrt (hc i).le]
  exact (hbds i).1

theorem exists_not_isLocalMin_curve [Nonempty ι] [Nonempty n]
    (Q : Matrix n n ℂ) (hQ : Q.IsHermitian) (v : ι → n → ℂ) (hv : ∀ i, v i ≠ 0)
    (x : ι → ℝ) (hx : ∀ i, |x i| < 1) {θ : ℝ} (hθ : 0 < θ)
    (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) (hS : S.PosDef) (ht : realTrace S = 1)
    (hmax : ∀ T ∈ densitySet,
      ownerObjective (signedLift Q) (KSSpinSource.family (atoms v))
        (KSSpinSource.coefficientCovariance (owners x)) θ T ≤
      ownerObjective (signedLift Q) (KSSpinSource.family (atoms v))
        (KSSpinSource.coefficientCovariance (owners x)) θ S)
    (hfail : ∀ i, owners x i * realTrace (stateTransport v x S *
      KSSpinCompression.compressedAtom (atoms v) i) < 1 - |x i|) :
    ∃ h : ι → ℝ, h ≠ 0 ∧ ¬ IsLocalMin (curvePotential Q v θ x h) 0 := by
  let V := KSSpinCompression.embedding (atoms v)
  let B := KSSpinCompression.compressedAtom (atoms v)
  let J := KSSpinCompression.compressedSign (atoms v)
  let Z := stateTransport v x S
  have hc := owners_pos hx
  have hA := KSSpinSource.family_isHermitian (atoms v) (fun i => KSRankOne.atom_isHermitian (v i))
  have hC := KSSpinSource.coefficientCovariance_posSemidef (fun i => (hc i).le)
  have hdiag := KSSpinSymmetry.optimizer_blockDiagonal Q v (fun i => (hc i).le) hθ ⟨hS.posSemidef, ht⟩ hmax
  have hJS : KSSignSymmetry.conjugate KSSignSymmetry.signMatrix S = S := by
    conv_lhs => rw [hdiag]
    simp only [KSSignSymmetry.sign_conjugate_blocks, Matrix.toBlocks_fromBlocks₁₁,
      Matrix.toBlocks_fromBlocks₁₂, Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂,
      neg_zero]
    exact hdiag.symm
  obtain ⟨h, U, hh, hU, hlegal, hnegative⟩ := actual_transport_descent v hv x hx S hS hJS hfail
  refine ⟨h, hh, ?_⟩
  let L := fun t => covarianceKraus (KSSpinSource.family (atoms v))
    (KSSpinSource.coefficientCovariance (ownerCurve x h t))
  let Hh : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ) := ⟨signedLift Q, signedLift_isHermitian hQ⟩
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
        (KSSpinSource.coefficientCovariance (owners x)) T := by
    dsimp only [L]
    rw [ownerCurve_zero, ← covarianceSource_eq_kraus _ hA hC]
  have hArecon : ∀ i, (Ah i : Matrix (n ⊕ n) (n ⊕ n) ℂ) = V * B i * Vᴴ :=
    fun i => (KSSpinCompression.compressedAtom_reconstruct (atoms v)
      (fun j => KSRankOne.atom_isHermitian (v j)) i).symm
  have hKrecon : (Kh : Matrix (n ⊕ n) (n ⊕ n) ℂ) = V * (∑ i, h i • (J * B i)) * Vᴴ := by
    simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
    exact Finset.sum_congr rfl (fun i _ => congrArg (fun M => h i • M) (signed_atom_reconstruct v i).symm)
  have hnot := KSSupportedCenterCurve.not_isLocalMin_of_supported_curve
    (curveCenter Q v h) L V hV Hh Kh Ah hZ hU 64 x h q r hθ Sh hS ht
    (by intro T hT
        dsimp only [curveCenter, L]
        rw [zero_smul, add_zero, ownerCurve_zero,
          ← ownerObjective_eq_densityObjective _ _ hA hC,
          ← ownerObjective_eq_densityObjective _ _ hA hC]
        exact hmax T hT)
    (by rw [he]; exact hM)
    (by rw [he]; exact hsolve)
    (by intro T hT; rw [he]; exact KSSpinCompression.source_reconstruct v (owners x) T)
    (by filter_upwards [eventually_ownerCurve_pos hx h] with t hct
        intro T hT
        exact kraus_source_reconstruct v (ownerCurve x h t) (fun i => (hct i).le) T)
    (by filter_upwards [eventually_ownerCurve_pos hx h] with t hct
        exact KSSupportedCenterCurve.centerCurve_eq_supportedGradient V Hh Kh Ah B (L t)
          hZ.isHermitian hU 64 x h t (curve_sourceAdjoint v x h t (fun i => (hct i).le) hZ.isHermitian hU))
    (KSSupportedCenterCurve.centerVelocity_zero V Kh Ah B J hZ.isHermitian hU 64 (owners x) x h q
      (fun i => rfl) hArecon hKrecon hlegal)
    (by rw [KSSupportedCenterCurve.centerAcceleration_pairing V S Ah B hZ.isHermitian hU 64 x h q hArecon]
        exact hnegative)
  intro hmin
  apply hnot
  apply hmin.congr
  filter_upwards [eventually_ownerCurve_pos hx h] with t hct
  exact ownerPotential_eq_densityPotential _ _ hA
    (KSSpinSource.coefficientCovariance_posSemidef (fun i => (hct i).le)) θ

end MatrixSpencer.KSSpinLocalState
