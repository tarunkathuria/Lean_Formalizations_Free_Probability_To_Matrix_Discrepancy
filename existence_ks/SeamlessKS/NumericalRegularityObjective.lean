import SeamlessKS.NumericalRegularityDomain
import MatrixSpencer.KSComplexOwnerObjective
import MatrixSpencer.KSCompactResolvent
import MatrixSpencer.KSActualEnvelope
import MatrixSpencer.KSHolomorphicFidelity

/-!
# The actual owner objective in complex matrix coordinates

The source uses the fixed physical support and the compact-resolvent trace
root. Its restriction to positive real owner/density data is the original
owner objective. Complex time and non-Hermitian density perturbations are
used only to prove the local analytic estimates.
-/

open Matrix Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
noncomputable section
set_option maxHeartbeats 1200000
namespace SeamlessKS.NumericalRegularityObjective
open MatrixSpencer

variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
local instance {k : Type*} [Fintype k] [DecidableEq k] : CStarAlgebra (Matrix k k ℂ) := {}

abbrev Space (n : Type*) := KSComplexSpinSource.Space n

def slope (v : ι → n → ℂ) (h : ι → ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℂ :=
  ∑ i, h i • signedLift (KSRankOne.atom (v i))

def complexCenter (M : Matrix (n ⊕ n) (n ⊕ n) ℂ) (v : ι → n → ℂ)
    (h : ι → ℝ) (t : ℂ) : Matrix (n ⊕ n) (n ⊕ n) ℂ := M + t • slope v h

def objective (ζ : ℝ) (M : Matrix (n ⊕ n) (n ⊕ n) ℂ) (v : ι → n → ℂ)
    (θ : ℝ) (x h : ι → ℝ) (p : Space n) : ℂ :=
  Matrix.trace (complexCenter M v h p.1 * p.2) +
    2 * KSCompactResolvent.traceRoot (NumericalRegularityDomain.compressedDensity v p.2 *
      NumericalRegularityDomain.compressedSource ζ v x h p) +
    2 * (θ : ℂ) * KSCompactResolvent.traceRoot p.2

omit [DecidableEq ι] in
theorem slope_isHermitian (v : ι → n → ℂ) (h : ι → ℝ) : (slope v h).IsHermitian := by
  change (∑ i, h i • signedLift (KSRankOne.atom (v i)))ᴴ = _
  simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, star_trivial]
  exact Finset.sum_congr rfl (fun i _ => congrArg (fun Q => h i • Q)
    (signedLift_isHermitian (KSRankOne.atom_isHermitian (v i))).eq)

omit [DecidableEq ι] [Fintype n] [DecidableEq n] in
theorem complexCenter_real (M : Matrix (n ⊕ n) (n ⊕ n) ℂ) (v : ι → n → ℂ)
    (h : ι → ℝ) (t : ℝ) :
    complexCenter M v h (t : ℂ) = KSDebitLocalState.curveCenter M v h t := by
  simp only [complexCenter, KSDebitLocalState.curveCenter, slope, KSSpinLocalState.atoms,
    Complex.coe_smul]

omit [DecidableEq ι] [Fintype n] [DecidableEq n] in
theorem complexCenter_shift (M : Matrix (n ⊕ n) (n ⊕ n) ℂ) (v : ι → n → ℂ)
    (h : ι → ℝ) (t z : ℂ) :
    complexCenter M v h (t + z) = complexCenter M v h t + z • slope v h := by
  simp only [complexCenter, add_smul, add_assoc]

omit [DecidableEq ι] in
theorem contDiff_complexCenter (M : Matrix (n ⊕ n) (n ⊕ n) ℂ) (v : ι → n → ℂ)
    (h : ι → ℝ) : ContDiff ℂ ∞ (complexCenter M v h) :=
  contDiff_const.add (contDiff_id.smul contDiff_const)

def compressionCLM (v : ι → n → ℂ) :
    Matrix (n ⊕ n) (n ⊕ n) ℂ →L[ℂ]
      Matrix (NumericalRegularityDomain.Support v) (NumericalRegularityDomain.Support v) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := NumericalRegularityDomain.compressedDensity v
      map_add' := by
        intro X Y
        simp only [NumericalRegularityDomain.compressedDensity, KSSupportSymmetry.compress,
          Matrix.mul_add, Matrix.add_mul]
      map_smul' := by
        intro c X
        simp only [NumericalRegularityDomain.compressedDensity, KSSupportSymmetry.compress,
          Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply] }

omit [DecidableEq ι] in
theorem contDiff_compressedDensity (v : ι → n → ℂ) :
    ContDiff ℂ ∞ (NumericalRegularityDomain.compressedDensity v) :=
  (compressionCLM v).contDiff

theorem contDiffAt_compressedSource {ζ : ℝ} (hζ : 0 < ζ) (v : ι → n → ℂ) (x h : ι → ℝ)
    {p : Space n} (hp : ∀ i, |((x i : ℂ) + p.1 * (h i : ℂ)).im| < ζ) :
    ContDiffAt ℂ ∞ (NumericalRegularityDomain.compressedSource ζ v x h) p :=
  (compressionCLM v).contDiff.contDiffAt.comp p (NumericalRegularitySource.contDiffAt_source hζ v x h hp)

theorem contDiffAt_objective_of_domain {ζ : ℝ} (hζ : 0 < ζ) (M : Matrix (n ⊕ n) (n ⊕ n) ℂ)
    (v : ι → n → ℂ) (θ : ℝ) (x h : ι → ℝ) {p : Space n}
    (hpstrip : ∀ i, |((x i : ℂ) + p.1 * (h i : ℂ)).im| < ζ)
    (hS : KSCompactResolvent.Domain p.2)
    (hsource : KSCompactResolvent.Domain (NumericalRegularityDomain.compressedDensity v p.2 *
      NumericalRegularityDomain.compressedSource ζ v x h p)) :
    ContDiffAt ℂ ∞ (objective ζ M v θ x h) p := by
  have hcenter := (contDiff_complexCenter M v h).contDiffAt.comp p contDiffAt_fst
  have hlinear := (KSCompactResolvent.traceCLM (n := n ⊕ n)).contDiff.contDiffAt.comp p
    (hcenter.mul contDiffAt_snd)
  have hdensity := (contDiff_compressedDensity v).contDiffAt.comp p contDiffAt_snd
  have hproduct := hdensity.mul (contDiffAt_compressedSource hζ v x h hpstrip)
  have hroot := (KSCompactResolvent.traceRoot_analyticAt hsource).contDiffAt.comp p hproduct
  have hregularizer : ContDiffAt ℂ ∞ (fun p : Space n => KSCompactResolvent.traceRoot p.2) p :=
    (KSCompactResolvent.traceRoot_analyticAt hS).contDiffAt.comp p contDiffAt_snd
  exact (hlinear.add (contDiffAt_const.mul hroot)).add (contDiffAt_const.mul hregularizer)

theorem compressedSource_recenter (ζ : ℝ) (v : ι → n → ℂ) (x h : ι → ℝ)
    (t : ℝ) (p : Space n) :
    NumericalRegularityDomain.compressedSource ζ v x h p =
      NumericalRegularityDomain.compressedSource ζ v (fun i => x i + t * h i) h (p.1 - t, p.2) := by
  unfold NumericalRegularityDomain.compressedSource
  rw [← NumericalRegularitySource.source_shift]
  congr 2
  apply Prod.ext
  · dsimp
    ring
  · rfl

/-- The actual source domain is preserved around any admissible real time. -/
theorem product_domain {ζ : ℝ} (hζ : 0 < ζ) (v : ι → n → ℂ) (x h : ι → ℝ)
    (t₀ : ℝ) (S₀ : Matrix (n ⊕ n) (n ⊕ n) ℂ) {μ ρ : ℝ}
    (hμ : 0 < μ) (hfloor : μ • (1 : Matrix (n ⊕ n) (n ⊕ n) ℂ) ≤ S₀)
    (hρ : 0 < ρ) (hx : ∀ i, |x i + t₀ * h i| ≤ 1 - ρ) (hh : ∀ i, |h i| ≤ 2)
    (p : Space n) (ht : ‖p.1 - (t₀ : ℂ)‖ ≤ NumericalRegularity.radius μ ρ ζ)
    (hS : ‖p.2 - S₀‖ ≤ NumericalRegularity.radius μ ρ ζ) :
    KSCompactResolvent.Domain (NumericalRegularityDomain.compressedDensity v p.2 *
      NumericalRegularityDomain.compressedSource ζ v x h p) := by
  have hp := NumericalRegularityDomain.product_spectrum_subset_slitPlane hζ v
    (fun i => x i + t₀ * h i) h S₀ (p.2 - S₀) hμ hfloor hρ hx hh (p.1 - t₀) ht hS
  have he : S₀ + (p.2 - S₀) = p.2 := by abel
  rw [he] at hp
  rw [compressedSource_recenter ζ v x h t₀ p]
  exact hp

theorem density_domain {ζ : ℝ} (hζ : 0 < ζ) {S₀ : Matrix n n ℂ} {μ ρ : ℝ}
    (hμ : 0 < μ) (hfloor : μ • (1 : Matrix n n ℂ) ≤ S₀)
    (S : Matrix n n ℂ) (hS : ‖S - S₀‖ ≤ NumericalRegularity.radius μ ρ ζ) :
    KSCompactResolvent.Domain S := by
  have hnorm : ‖S - S₀‖ < μ := by
    have hr := NumericalRegularity.radius_le_density μ ρ ζ
    linarith
  have he : S₀ + (S - S₀) = S := by abel
  have ha := KSComplexSpinDomain.density_strictAccretive hfloor hnorm
  rw [he] at ha
  have hi : KSAccretiveProductDomain.StrictAccretive (1 : Matrix n n ℂ) := by
    simpa only [add_zero] using KSAccretiveProductDomain.one_add_strictAccretive
      (show ‖(0 : Matrix n n ℂ)‖ < 1 by simp)
  simpa only [Matrix.mul_one] using
    KSAccretiveProductDomain.product_spectrum_subset_slitPlane ha hi

/-- Complex smoothness on the explicit ball in product/operator norm. -/
theorem contDiffOn_objective {ζ : ℝ} (hζ : 0 < ζ) (M : Matrix (n ⊕ n) (n ⊕ n) ℂ) (v : ι → n → ℂ)
    (θ : ℝ) (x h : ι → ℝ) (t₀ : ℝ) (S₀ : Matrix (n ⊕ n) (n ⊕ n) ℂ) {μ ρ : ℝ}
    (hμ : 0 < μ) (hfloor : μ • (1 : Matrix (n ⊕ n) (n ⊕ n) ℂ) ≤ S₀)
    (hρ : 0 < ρ) (hx : ∀ i, |x i + t₀ * h i| ≤ 1 - ρ) (hh : ∀ i, |h i| ≤ 2) :
    ContDiffOn ℂ ∞ (objective ζ M v θ x h)
      (Metric.ball ((t₀ : ℂ), S₀) (NumericalRegularity.radius μ ρ ζ)) := by
  intro p hp
  have hn : ‖p - ((t₀ : ℂ), S₀)‖ < NumericalRegularity.radius μ ρ ζ := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hp
  have ht : ‖p.1 - (t₀ : ℂ)‖ ≤ NumericalRegularity.radius μ ρ ζ :=
    (le_max_left _ _).trans hn.le
  have hS : ‖p.2 - S₀‖ ≤ NumericalRegularity.radius μ ρ ζ :=
    (le_max_right _ _).trans hn.le
  have hpstrip : ∀ i, |((x i : ℂ) + p.1 * (h i : ℂ)).im| < ζ := by
    intro i
    have he : ((x i : ℂ) + p.1 * (h i : ℂ)).im =
        ((p.1 - (t₀ : ℂ)) * (h i : ℂ)).im := by
      simp only [Complex.add_im, Complex.mul_im, Complex.sub_re, Complex.sub_im,
        Complex.ofReal_re, Complex.ofReal_im]
      ring
    rw [he]
    have hb := Complex.abs_im_le_norm ((p.1 - (t₀ : ℂ)) * (h i : ℂ))
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs] at hb
    have hm := mul_le_mul ht (hh i) (abs_nonneg _) (NumericalRegularity.radius_pos hμ hρ hζ).le
    have hr := NumericalRegularity.radius_le_smoothing μ ρ ζ
    nlinarith
  exact (contDiffAt_objective_of_domain hζ M v θ x h hpstrip (density_domain hζ hμ hfloor p.2 hS)
    (product_domain hζ v x h t₀ S₀ hμ hfloor hρ hx hh p ht hS)).contDiffWithinAt

/-- Exact agreement with covariance fidelity on the fixed support. -/
theorem traceRoot_source_eq_fidelity {ζ : ℝ} (hζ : 0 < ζ)
    (v : ι → n → ℂ) (x h : ι → ℝ) (t : ℝ)
    {S : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hS : S.PosDef)
    (hc : ∀ i, 0 < Source.weight 64 ζ (x i + t * h i)) :
    KSCompactResolvent.traceRoot (NumericalRegularityDomain.compressedDensity v S *
      NumericalRegularityDomain.compressedSource ζ v x h ((t : ℂ), S)) =
      (fidelity S (covarianceSource (KSSpinSource.family (fun i => KSRankOne.atom (v i)))
        (KSSpinSource.coefficientCovariance (fun i => Source.weight 64 ζ (x i + t * h i))) S) : ℂ) := by
  unfold NumericalRegularityDomain.compressedSource
  rw [NumericalRegularitySource.source_real hζ]
  exact KSHolomorphicFidelity.traceRoot_covariance_eq_fidelity _
    (KSSpinSource.family_isHermitian _ (fun i => (KSRankOne.atom_posSemidef (v i)).isHermitian))
    (KSSpinCompression.coefficientCovariance_posDef hc) hS

/-- At every positive real state, all three complex terms agree exactly
with the original owner objective. The physical source may be singular. -/
theorem objective_real {ζ : ℝ} (hζ : 0 < ζ) (M : Matrix (n ⊕ n) (n ⊕ n) ℂ) (hM : M.IsHermitian)
    (v : ι → n → ℂ) (θ : ℝ) (x h : ι → ℝ) (t : ℝ)
    {S : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hS : S.PosDef)
    (hc : ∀ i, 0 < Source.weight 64 ζ (x i + t * h i)) :
    objective ζ M v θ x h ((t : ℂ), S) =
      (ownerObjective (KSDebitLocalState.curveCenter M v h t)
        (KSSpinSource.family (KSSpinLocalState.atoms v))
        (KSSpinSource.coefficientCovariance (fun i => Source.weight 64 ζ (x i + t * h i))) θ S : ℂ) := by
  have hcenter : (KSDebitLocalState.curveCenter M v h t).IsHermitian := by
    change (M + t • slope v h)ᴴ = M + t • slope v h
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, star_trivial,
      hM.eq, (slope_isHermitian v h).eq]
  rw [objective, complexCenter_real,
    KSComplexOwnerPerturbation.trace_pairing_real _ S hcenter hS.isHermitian,
    traceRoot_source_eq_fidelity hζ v x h t hS hc,
    KSHolomorphicFidelity.traceRoot_posDef hS]
  simp only [ownerObjective,
    Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_ofNat]
  rfl


end SeamlessKS.NumericalRegularityObjective
