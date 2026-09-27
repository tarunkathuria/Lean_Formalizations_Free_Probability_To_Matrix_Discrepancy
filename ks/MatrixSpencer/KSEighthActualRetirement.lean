import MatrixSpencer.KSEighthFullSupport
import MatrixSpencer.KSArbitraryRetirement

/-! Genuine endpoint retirements for the  chosen block transport. -/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSEighthActualRetirement
open KSEighthActualState KSEighthFullSupport KSEighthBalanced KSEndpointRetirement

variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n] [Nonempty n]

theorem actual_retire
    (Q : Matrix n n ℂ) (v : ι → n → ℂ) (hv : ∀ i, v i ≠ 0)
    (x : ι → ℝ) (hx : ∀ i, |x i| ≤ (1 / 8 : ℝ)) {θ : ℝ} (hθ : 0 < θ)
    (i : ι) (δ : ℝ)
    (hp : δ ≤ owner x i * probe (KSEighthSupport.compressedVector v) (transport Q v x θ true) i)
    (hq : -δ ≤ owner x i * probe (KSEighthSupport.compressedVector v) (transport Q v x θ false) i) :
    ownerPotential (signedLift Q + δ • signedLift (KSRankOne.atom (v i))) (family v)
      (KSIndependentSource.coefficientCovariance (Function.update (owner x) i 0)) θ ≤
    ownerPotential (signedLift Q) (family v) (covariance x) θ := by
  let V := fullEmbedding v
  let Z := fullTransport Q v x θ
  let W := V * Z * Vᴴ
  have hc : ∀ i, 0 ≤ owner x i := fun i => (owner_pos x hx i).le
  have hC := covariance_posSemidef x hx
  have hZ : Z.PosDef := fullTransport_posDef Q v hv x hx hθ
  have he (T : Matrix (n ⊕ n) (n ⊕ n) ℂ) := covarianceSource_eq_kraus (family v) (family_isHermitian v) hC T
  apply KSArbitraryRetirement.owner_retire_of_supported_matrix_le (signedLift Q) _ (family v)
    (family_isHermitian v) hC
    (KSIndependentSource.coefficientCovariance_posSemidef (update_zero_nonneg hc i))
    (independent_covariance_delete_le (owner x) hc i) V (fullEmbedding_isometry v) hθ
    (fullDensity Q v x θ) (fullDensity_posDef Q v x hθ) (fullDensity_trace Q v x θ)
    (fullDensity_isMaxOn Q v x θ) hZ
  · rw [← he]
    exact actual_source_posDef Q v hv x hx hθ
  · rw [← he]
    exact actual_transport_solve Q v hv x hx hθ
  · intro T hT
    rw [← he]
    exact source_reconstruct v hv (owner x) hT.isHermitian
  · have hW : W.IsHermitian := Matrix.isHermitian_mul_mul_conjTranspose V hZ.isHermitian
    have hleft : realTrace (leftDensity (KSRankOne.atom (v i)) * W) =
        probe (KSEighthSupport.compressedVector v) (transport Q v x θ true) i := by
      have hh := independent_probe v Z (i, true)
      change realTrace (leftDensity (KSRankOne.atom (v i)) * W) = _ at hh
      rw [hh, realTrace_mul_comm]
      exact KSEighthBlocks.realTrace_mul_independent _ Z (i, true)
    have hright : realTrace (rightDensity (KSRankOne.atom (v i)) * W) =
        probe (KSEighthSupport.compressedVector v) (transport Q v x θ false) i := by
      have hh := independent_probe v Z (i, false)
      change realTrace (rightDensity (KSRankOne.atom (v i)) * W) = _ at hh
      rw [hh, realTrace_mul_comm]
      exact KSEighthBlocks.realTrace_mul_independent _ Z (i, false)
    change signedLift Q + δ • signedLift (KSRankOne.atom (v i)) +
      covarianceSource (family v) (KSIndependentSource.coefficientCovariance (Function.update (owner x) i 0)) W ≤
        signedLift Q + covarianceSource (family v) (covariance x) W
    have hd := independent_source_delete v (owner x) i hW
    change covarianceSource (family v) _ W = _ at hd
    rw [hd]
    have hstep := independent_step_le (KSRankOne.atom_posSemidef (v i))
      (hleft.symm ▸ hp) (hright.symm ▸ hq)
    have hs : δ • signedLift (KSRankOne.atom (v i)) ≤
        owner x i • (realTrace (rightDensity (KSRankOne.atom (v i)) * W) • rightDensity (KSRankOne.atom (v i)) +
          realTrace (leftDensity (KSRankOne.atom (v i)) * W) • leftDensity (KSRankOne.atom (v i))) := by
      simpa only [smul_add, smul_smul] using hstep
    have ha := add_le_add_left (sub_nonpos.mpr hs)
      (signedLift Q + covarianceSource (family v) (covariance x) W)
    simp only [add_zero] at ha
    convert ha using 1 <;> dsimp only [family, covariance] <;> abel

theorem actual_probe_nonneg
    (Q : Matrix n n ℂ) (v : ι → n → ℂ) (hv : ∀ i, v i ≠ 0)
    (x : ι → ℝ) (hx : ∀ i, |x i| ≤ (1 / 8 : ℝ)) {θ : ℝ} (hθ : 0 < θ)
    (i : ι) (b : Bool) : 0 ≤ probe (KSEighthSupport.compressedVector v) (transport Q v x θ b) i :=
  realTrace_mul_nonneg (transport_posDef Q v hv x hx hθ b).posSemidef (KSRankOne.atom_posSemidef _)

end MatrixSpencer.KSEighthActualRetirement
