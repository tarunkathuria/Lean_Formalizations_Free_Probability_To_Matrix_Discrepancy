import MatrixSpencer.KSDebitCenter
import MatrixSpencer.KSSpinLocalState

/-!
# Actual local descent curves with a fixed physical debit

This reproduces the existing spin local-state argument for an arbitrary
Hermitian center commuting with the sign involution, then specializes it
to the walk's center `signedLift H - doubled B`.  The physical transport
completion and the touching-majorant calculus are the proved existing
ones.  The conclusion excludes local minimality along a concrete family
of curves.  No numerical Hessian approximation, uniform mesh, value
oracle, or finite-walk theorem is asserted here.
-/

open Matrix Filter Topology
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
noncomputable section
namespace MatrixSpencer.KSDebitLocalState

open KSSpinLocalState

variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
local instance {k : Type*} [Fintype k] [DecidableEq k] : CStarAlgebra (Matrix k k ℂ) := {}

/-- The starting center includes any fixed debit; only its signed coefficient
increment varies along the curve. -/
def curveCenter (M : Matrix (n ⊕ n) (n ⊕ n) ℂ) (v : ι → n → ℂ)
    (h : ι → ℝ) (t : ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℂ :=
  M + t • (∑ i, h i • signedLift (atoms v i))

def curvePotential (M : Matrix (n ⊕ n) (n ⊕ n) ℂ) (v : ι → n → ℂ) (θ : ℝ)
    (x h : ι → ℝ) (t : ℝ) : ℝ :=
  ownerPotential (curveCenter M v h t) (KSSpinSource.family (atoms v))
    (KSSpinSource.coefficientCovariance (ownerCurve x h t)) θ

/-- The actual no-retirement hypotheses imply a nonzero curve excluding a
local minimum, now for every sign-commuting Hermitian starting center. -/
theorem exists_not_isLocalMin_curve [Nonempty ι] [Nonempty n]
    (M : Matrix (n ⊕ n) (n ⊕ n) ℂ) (hMherm : M.IsHermitian)
    (hJM : Commute KSSignSymmetry.signMatrix M) (v : ι → n → ℂ) (hv : ∀ i, v i ≠ 0)
    (x : ι → ℝ) (hx : ∀ i, |x i| < 1) {θ : ℝ} (hθ : 0 < θ)
    (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) (hS : S.PosDef) (ht : realTrace S = 1)
    (hmax : ∀ T ∈ densitySet,
      ownerObjective M (KSSpinSource.family (atoms v))
        (KSSpinSource.coefficientCovariance (owners x)) θ T ≤
      ownerObjective M (KSSpinSource.family (atoms v))
        (KSSpinSource.coefficientCovariance (owners x)) θ S)
    (hfail : ∀ i, owners x i * realTrace (stateTransport v x S *
      KSSpinCompression.compressedAtom (atoms v) i) < 1 - |x i|) :
    ∃ h : ι → ℝ, h ≠ 0 ∧ ¬ IsLocalMin (curvePotential M v θ x h) 0 := by
  let V := KSSpinCompression.embedding (atoms v)
  let B := KSSpinCompression.compressedAtom (atoms v)
  let J := KSSpinCompression.compressedSign (atoms v)
  let Z := stateTransport v x S
  have hc := owners_pos hx
  have hA := KSSpinSource.family_isHermitian (atoms v) (fun i => KSRankOne.atom_isHermitian (v i))
  have hC := KSSpinSource.coefficientCovariance_posSemidef (fun i => (hc i).le)
  have hJS := KSDebitCenter.optimizer_conjugate_eq_of_commute M hJM v
    (fun i => (hc i).le) hθ ⟨hS.posSemidef, ht⟩ hmax
  obtain ⟨h, U, hh, hU, hlegal, hnegative⟩ := actual_transport_descent v hv x hx S hS hJS hfail
  refine ⟨h, hh, ?_⟩
  let L := fun t => covarianceKraus (KSSpinSource.family (atoms v))
    (KSSpinSource.coefficientCovariance (ownerCurve x h t))
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
    (curveCenter M v h) L V hV Hh Kh Ah hZ hU 64 x h q r hθ Sh hS ht
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

/-- The concrete full-cube algorithm's PSD debit satisfies the generalized
center hypotheses without any extra symmetry assumption. -/
theorem exists_not_isLocalMin_debit_curve [Nonempty ι] [Nonempty n]
    (H B : Matrix n n ℂ) (hH : H.IsHermitian) (hB : B.PosSemidef)
    (v : ι → n → ℂ) (hv : ∀ i, v i ≠ 0)
    (x : ι → ℝ) (hx : ∀ i, |x i| < 1) {θ : ℝ} (hθ : 0 < θ)
    (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) (hS : S.PosDef) (ht : realTrace S = 1)
    (hmax : ∀ T ∈ densitySet,
      ownerObjective (KSDebitCenter.center H B) (KSSpinSource.family (atoms v))
        (KSSpinSource.coefficientCovariance (owners x)) θ T ≤
      ownerObjective (KSDebitCenter.center H B) (KSSpinSource.family (atoms v))
        (KSSpinSource.coefficientCovariance (owners x)) θ S)
    (hfail : ∀ i, owners x i * realTrace (stateTransport v x S *
      KSSpinCompression.compressedAtom (atoms v) i) < 1 - |x i|) :
    ∃ h : ι → ℝ, h ≠ 0 ∧
      ¬ IsLocalMin (curvePotential (KSDebitCenter.center H B) v θ x h) 0 :=
  exists_not_isLocalMin_curve (KSDebitCenter.center H B)
    (KSDebitCenter.center_isHermitian_of_posSemidef hH hB)
    (KSDebitCenter.signMatrix_commute_center H B) v hv x hx hθ S hS ht hmax hfail

end MatrixSpencer.KSDebitLocalState
