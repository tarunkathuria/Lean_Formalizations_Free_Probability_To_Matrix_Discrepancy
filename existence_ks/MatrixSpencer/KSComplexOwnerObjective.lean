import MatrixSpencer.KSComplexSpinDomain
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
namespace MatrixSpencer.KSComplexOwnerObjective

variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
local instance {k : Type*} [Fintype k] [DecidableEq k] : CStarAlgebra (Matrix k k ℂ) := {}

abbrev Space (n : Type*) := KSComplexSpinSource.Space n

def slope (v : ι → n → ℂ) (h : ι → ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℂ :=
  ∑ i, h i • signedLift (KSRankOne.atom (v i))

def complexCenter (M : Matrix (n ⊕ n) (n ⊕ n) ℂ) (v : ι → n → ℂ)
    (h : ι → ℝ) (t : ℂ) : Matrix (n ⊕ n) (n ⊕ n) ℂ := M + t • slope v h

def objective (M : Matrix (n ⊕ n) (n ⊕ n) ℂ) (v : ι → n → ℂ)
    (θ : ℝ) (x h : ι → ℝ) (p : Space n) : ℂ :=
  Matrix.trace (complexCenter M v h p.1 * p.2) +
    2 * KSCompactResolvent.traceRoot (KSComplexSpinDomain.compressedDensity v p.2 *
      KSComplexSpinDomain.compressedSource v x h p) +
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
      Matrix (KSComplexSpinDomain.Support v) (KSComplexSpinDomain.Support v) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := KSComplexSpinDomain.compressedDensity v
      map_add' := by
        intro X Y
        simp only [KSComplexSpinDomain.compressedDensity, KSSupportSymmetry.compress,
          Matrix.mul_add, Matrix.add_mul]
      map_smul' := by
        intro c X
        simp only [KSComplexSpinDomain.compressedDensity, KSSupportSymmetry.compress,
          Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply] }

omit [DecidableEq ι] in
theorem contDiff_compressedDensity (v : ι → n → ℂ) :
    ContDiff ℂ ∞ (KSComplexSpinDomain.compressedDensity v) :=
  (compressionCLM v).contDiff

theorem contDiff_compressedSource (v : ι → n → ℂ) (x h : ι → ℝ) :
    ContDiff ℂ ∞ (KSComplexSpinDomain.compressedSource v x h) :=
  (compressionCLM v).contDiff.comp (KSComplexSpinSource.contDiff_source v x h)

theorem contDiffAt_objective_of_domain (M : Matrix (n ⊕ n) (n ⊕ n) ℂ)
    (v : ι → n → ℂ) (θ : ℝ) (x h : ι → ℝ) {p : Space n}
    (hS : KSCompactResolvent.Domain p.2)
    (hsource : KSCompactResolvent.Domain (KSComplexSpinDomain.compressedDensity v p.2 *
      KSComplexSpinDomain.compressedSource v x h p)) :
    ContDiffAt ℂ ∞ (objective M v θ x h) p := by
  have hcenter := (contDiff_complexCenter M v h).contDiffAt.comp p contDiffAt_fst
  have hlinear := (KSCompactResolvent.traceCLM (n := n ⊕ n)).contDiff.contDiffAt.comp p
    (hcenter.mul contDiffAt_snd)
  have hdensity := (contDiff_compressedDensity v).contDiffAt.comp p contDiffAt_snd
  have hproduct := hdensity.mul (contDiff_compressedSource v x h).contDiffAt
  have hroot := (KSCompactResolvent.traceRoot_analyticAt hsource).contDiffAt.comp p hproduct
  have hregularizer : ContDiffAt ℂ ∞ (fun p : Space n => KSCompactResolvent.traceRoot p.2) p :=
    (KSCompactResolvent.traceRoot_analyticAt hS).contDiffAt.comp p contDiffAt_snd
  exact (hlinear.add (contDiffAt_const.mul hroot)).add (contDiffAt_const.mul hregularizer)

theorem compressedSource_recenter (v : ι → n → ℂ) (x h : ι → ℝ)
    (t : ℝ) (p : Space n) :
    KSComplexSpinDomain.compressedSource v x h p =
      KSComplexSpinDomain.compressedSource v (fun i => x i + t * h i) h (p.1 - t, p.2) := by
  unfold KSComplexSpinDomain.compressedSource
  rw [← KSComplexSpinSource.source_shift]
  congr 2
  apply Prod.ext
  · dsimp
    ring
  · rfl

/-- The actual source domain is preserved around any admissible real time. -/
theorem product_domain (v : ι → n → ℂ) (x h : ι → ℝ)
    (t₀ : ℝ) (S₀ : Matrix (n ⊕ n) (n ⊕ n) ℂ) {μ ρ : ℝ}
    (hμ : 0 < μ) (hfloor : μ • (1 : Matrix (n ⊕ n) (n ⊕ n) ℂ) ≤ S₀)
    (hρ : 0 < ρ) (hx : ∀ i, |x i + t₀ * h i| ≤ 1 - ρ) (hh : ∀ i, |h i| ≤ 2)
    (p : Space n) (ht : ‖p.1 - (t₀ : ℂ)‖ ≤ KSComplexPerturbationRadius.radius μ ρ)
    (hS : ‖p.2 - S₀‖ ≤ KSComplexPerturbationRadius.radius μ ρ) :
    KSCompactResolvent.Domain (KSComplexSpinDomain.compressedDensity v p.2 *
      KSComplexSpinDomain.compressedSource v x h p) := by
  have hp := KSComplexSpinDomain.product_spectrum_subset_slitPlane v
    (fun i => x i + t₀ * h i) h S₀ (p.2 - S₀) hμ hfloor hρ hx hh (p.1 - t₀) ht hS
  have he : S₀ + (p.2 - S₀) = p.2 := by abel
  rw [he] at hp
  rw [compressedSource_recenter v x h t₀ p]
  exact hp

theorem density_domain {S₀ : Matrix n n ℂ} {μ ρ : ℝ}
    (hμ : 0 < μ) (hfloor : μ • (1 : Matrix n n ℂ) ≤ S₀)
    (S : Matrix n n ℂ) (hS : ‖S - S₀‖ ≤ KSComplexPerturbationRadius.radius μ ρ) :
    KSCompactResolvent.Domain S := by
  have hnorm : ‖S - S₀‖ < μ := by
    have hr := KSComplexPerturbationRadius.radius_le_density μ ρ
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
theorem contDiffOn_objective (M : Matrix (n ⊕ n) (n ⊕ n) ℂ) (v : ι → n → ℂ)
    (θ : ℝ) (x h : ι → ℝ) (t₀ : ℝ) (S₀ : Matrix (n ⊕ n) (n ⊕ n) ℂ) {μ ρ : ℝ}
    (hμ : 0 < μ) (hfloor : μ • (1 : Matrix (n ⊕ n) (n ⊕ n) ℂ) ≤ S₀)
    (hρ : 0 < ρ) (hx : ∀ i, |x i + t₀ * h i| ≤ 1 - ρ) (hh : ∀ i, |h i| ≤ 2) :
    ContDiffOn ℂ ∞ (objective M v θ x h)
      (Metric.ball ((t₀ : ℂ), S₀) (KSComplexPerturbationRadius.radius μ ρ)) := by
  intro p hp
  have hn : ‖p - ((t₀ : ℂ), S₀)‖ < KSComplexPerturbationRadius.radius μ ρ := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hp
  have ht : ‖p.1 - (t₀ : ℂ)‖ ≤ KSComplexPerturbationRadius.radius μ ρ :=
    (le_max_left _ _).trans hn.le
  have hS : ‖p.2 - S₀‖ ≤ KSComplexPerturbationRadius.radius μ ρ :=
    (le_max_right _ _).trans hn.le
  exact (contDiffAt_objective_of_domain M v θ x h (density_domain hμ hfloor p.2 hS)
    (product_domain v x h t₀ S₀ hμ hfloor hρ hx hh p ht hS)).contDiffWithinAt

/-- At every positive real state, all three complex terms agree exactly
with the original owner objective. The physical source may be singular. -/
theorem objective_real (M : Matrix (n ⊕ n) (n ⊕ n) ℂ) (hM : M.IsHermitian)
    (v : ι → n → ℂ) (θ : ℝ) (x h : ι → ℝ) (t : ℝ)
    {S : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hS : S.PosDef)
    (hc : ∀ i, 0 < 64 * (1 - (x i + t * h i) ^ 2)) :
    objective M v θ x h ((t : ℂ), S) =
      (ownerObjective (KSDebitLocalState.curveCenter M v h t)
        (KSSpinSource.family (KSSpinLocalState.atoms v))
        (KSSpinSource.coefficientCovariance (KSSpinLocalState.ownerCurve x h t)) θ S : ℂ) := by
  have hcenter : (KSDebitLocalState.curveCenter M v h t).IsHermitian := by
    change (M + t • slope v h)ᴴ = M + t • slope v h
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, star_trivial,
      hM.eq, (slope_isHermitian v h).eq]
  rw [objective, complexCenter_real,
    KSComplexOwnerPerturbation.trace_pairing_real _ S hcenter hS.isHermitian,
    KSHolomorphicFidelity.traceRoot_spin_source_eq_fidelity v x h t hS hc,
    KSHolomorphicFidelity.traceRoot_posDef hS]
  simp only [ownerObjective,
    Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_ofNat]
  rfl

variable [Nonempty n]

/-- Exact agreement in the full trace-zero Frobenius density chart. -/
theorem objective_chart_eq (M : Matrix (n ⊕ n) (n ⊕ n) ℂ) (hM : M.IsHermitian)
    (v : ι → n → ℂ) (θ : ℝ) (x h : ι → ℝ) (t : ℝ)
    (q : KSFrobeniusTangent.Coordinates (n ⊕ n))
    (hS : (KSFrobeniusTangent.chart (n ⊕ n) q : Matrix (n ⊕ n) (n ⊕ n) ℂ).PosDef)
    (hc : ∀ i, 0 < 64 * (1 - (x i + t * h i) ^ 2)) :
    objective M v θ x h ((t : ℂ), (KSFrobeniusTangent.chart (n ⊕ n) q : Matrix (n ⊕ n) (n ⊕ n) ℂ)) =
      (KSActualEnvelope.curveObjective M hM v θ x h (t, q) : ℂ) :=
  objective_real M hM v θ x h t hS hc

theorem objective_real_eq_curveObjective (M : Matrix (n ⊕ n) (n ⊕ n) ℂ) (hM : M.IsHermitian)
    (v : ι → n → ℂ) (θ : ℝ) (x h : ι → ℝ) (t : ℝ)
    (q : KSFrobeniusTangent.Coordinates (n ⊕ n))
    (hS : (KSFrobeniusTangent.chart (n ⊕ n) q : Matrix (n ⊕ n) (n ⊕ n) ℂ).PosDef)
    (hc : ∀ i, 0 < 64 * (1 - (x i + t * h i) ^ 2)) :
    (objective M v θ x h ((t : ℂ),
      (KSFrobeniusTangent.chart (n ⊕ n) q : Matrix (n ⊕ n) (n ⊕ n) ℂ))).re =
        KSActualEnvelope.curveObjective M hM v θ x h (t, q) := by
  rw [objective_chart_eq M hM v θ x h t q hS hc, Complex.ofReal_re]

end MatrixSpencer.KSComplexOwnerObjective
