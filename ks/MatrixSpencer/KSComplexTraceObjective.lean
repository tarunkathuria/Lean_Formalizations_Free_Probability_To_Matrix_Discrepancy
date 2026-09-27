import MatrixSpencer.KSComplexTraceDomain
import MatrixSpencer.KSComplexOwnerObjective
import MatrixSpencer.KSActualEnvelope
import MatrixSpencer.KSHolomorphicFidelity

/-!
# Analytic objective for a general trace-and-prepare source

The support frame is fixed. All spectral inverses and complex variables here
are analytic proof objects; numerical evaluations use the corresponding real
objective. Concrete source support lemmas discharge base-source positivity.
-/

open Matrix Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
noncomputable section
namespace MatrixSpencer.KSComplexTraceObjective

variable {ι n m : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
  [Fintype m] [DecidableEq m]
local instance {k : Type*} [Fintype k] [DecidableEq k] : CStarAlgebra (Matrix k k ℂ) := {}

abbrev Space (n : Type*) := KSComplexTraceSource.Space n

def complexCenter (M D : Matrix n n ℂ) (t : ℂ) : Matrix n n ℂ := M + t • D

def objective (V : Matrix n m ℂ) (M D : Matrix n n ℂ) (A : ι → Matrix n n ℂ)
    (θ : ℝ) (x h : ι → ℝ) (p : Space n) : ℂ :=
  Matrix.trace (complexCenter M D p.1 * p.2) +
    2 * KSCompactResolvent.traceRoot (KSComplexTraceDomain.compressedDensity V p.2 *
      KSComplexTraceDomain.compressedSource V A x h p) +
    2 * (θ : ℂ) * KSCompactResolvent.traceRoot p.2

theorem complexCenter_shift (M D : Matrix n n ℂ) (t z : ℂ) :
    complexCenter M D (t+z) = complexCenter M D t + z • D := by
  simp only [complexCenter, add_smul, add_assoc]

theorem contDiff_complexCenter (M D : Matrix n n ℂ) : ContDiff ℂ ∞ (complexCenter M D) :=
  contDiff_const.add (contDiff_id.smul contDiff_const)

def compressionCLM (V : Matrix n m ℂ) :
    Matrix n n ℂ →L[ℂ]
      Matrix m m ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := KSComplexTraceDomain.compressedDensity V
      map_add' := by
        intro X Y
        simp only [KSComplexTraceDomain.compressedDensity, KSSupportSymmetry.compress,
          Matrix.mul_add, Matrix.add_mul]
      map_smul' := by
        intro c X
        simp only [KSComplexTraceDomain.compressedDensity, KSSupportSymmetry.compress,
          Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply] }

omit [DecidableEq ι] in
theorem contDiff_compressedDensity (V : Matrix n m ℂ) :
    ContDiff ℂ ∞ (KSComplexTraceDomain.compressedDensity V) :=
  (compressionCLM V).contDiff

theorem contDiff_compressedSource (V : Matrix n m ℂ) (A : ι → Matrix n n ℂ) (x h : ι → ℝ) :
    ContDiff ℂ ∞ (KSComplexTraceDomain.compressedSource V A x h) :=
  (compressionCLM V).contDiff.comp (KSComplexTraceSource.contDiff_source A x h)

theorem contDiffAt_objective_of_domain (V : Matrix n m ℂ) (M D : Matrix n n ℂ)
    (A : ι → Matrix n n ℂ) (θ : ℝ) (x h : ι → ℝ) {p : Space n}
    (hS : KSCompactResolvent.Domain p.2)
    (hsource : KSCompactResolvent.Domain (KSComplexTraceDomain.compressedDensity V p.2 *
      KSComplexTraceDomain.compressedSource V A x h p)) :
    ContDiffAt ℂ ∞ (objective V M D A θ x h) p := by
  have hcenter := (contDiff_complexCenter M D).contDiffAt.comp p contDiffAt_fst
  have hlinear := (KSCompactResolvent.traceCLM (n := n)).contDiff.contDiffAt.comp p
    (hcenter.mul contDiffAt_snd)
  have hdensity := (contDiff_compressedDensity V).contDiffAt.comp p contDiffAt_snd
  have hproduct := hdensity.mul (contDiff_compressedSource V A x h).contDiffAt
  have hroot := (KSCompactResolvent.traceRoot_analyticAt hsource).contDiffAt.comp p hproduct
  have hregularizer : ContDiffAt ℂ ∞ (fun p : Space n => KSCompactResolvent.traceRoot p.2) p :=
    (KSCompactResolvent.traceRoot_analyticAt hS).contDiffAt.comp p contDiffAt_snd
  exact (hlinear.add (contDiffAt_const.mul hroot)).add (contDiffAt_const.mul hregularizer)

theorem compressedSource_recenter (V : Matrix n m ℂ) (A : ι → Matrix n n ℂ) (x h : ι → ℝ)
    (t : ℝ) (p : Space n) :
    KSComplexTraceDomain.compressedSource V A x h p =
      KSComplexTraceDomain.compressedSource V A (fun i => x i + t * h i) h (p.1 - t, p.2) := by
  unfold KSComplexTraceDomain.compressedSource
  rw [← KSComplexTraceSource.source_shift]
  congr 2
  apply Prod.ext
  · dsimp
    ring
  · rfl

/-- Actual simultaneous perturbation around an admissible real base point. -/
theorem product_domain (V : Matrix n m ℂ) (hV : Vᴴ * V = 1)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef) (x h : ι → ℝ)
    (t₀ : ℝ) (S₀ : Matrix n n ℂ)
    (hbase : (KSComplexTraceDomain.baseSource V A (fun i => x i+t₀*h i) h S₀).PosDef)
    {μ ρ : ℝ} (hμ : 0 < μ) (hfloor : μ • (1 : Matrix n n ℂ) ≤ S₀)
    (hρ : 0 < ρ) (hx : ∀ i, |x i+t₀*h i| ≤ 1-ρ) (hh : ∀ i, |h i| ≤ 2)
    (p : Space n) (ht : ‖p.1-(t₀ : ℂ)‖ ≤ KSComplexPerturbationRadius.radius μ ρ)
    (hS : ‖p.2-S₀‖ ≤ KSComplexPerturbationRadius.radius μ ρ) :
    KSCompactResolvent.Domain (KSComplexTraceDomain.compressedDensity V p.2 *
      KSComplexTraceDomain.compressedSource V A x h p) := by
  have hp := KSComplexTraceDomain.product_spectrum_subset_slitPlane V hV A hA
    (fun i => x i+t₀*h i) h S₀ (p.2-S₀) hbase hμ hfloor hρ hx hh (p.1-t₀) ht hS
  have he : S₀+(p.2-S₀)=p.2 := by abel
  rw [he] at hp
  rw [compressedSource_recenter V A x h t₀ p]
  exact hp

/-- Complex smoothness on the explicit ball in product/operator norm. -/
theorem contDiffOn_objective (V : Matrix n m ℂ) (hV : Vᴴ * V = 1)
    (M D : Matrix n n ℂ) (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (θ : ℝ) (x h : ι → ℝ) (t₀ : ℝ) (S₀ : Matrix n n ℂ)
    (hbase : (KSComplexTraceDomain.baseSource V A (fun i => x i+t₀*h i) h S₀).PosDef) {μ ρ : ℝ}
    (hμ : 0 < μ) (hfloor : μ • (1 : Matrix n n ℂ) ≤ S₀)
    (hρ : 0 < ρ) (hx : ∀ i, |x i + t₀ * h i| ≤ 1 - ρ) (hh : ∀ i, |h i| ≤ 2) :
    ContDiffOn ℂ ∞ (objective V M D A θ x h)
      (Metric.ball ((t₀ : ℂ), S₀) (KSComplexPerturbationRadius.radius μ ρ)) := by
  intro p hp
  have hn : ‖p - ((t₀ : ℂ), S₀)‖ < KSComplexPerturbationRadius.radius μ ρ := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hp
  have ht : ‖p.1 - (t₀ : ℂ)‖ ≤ KSComplexPerturbationRadius.radius μ ρ :=
    (le_max_left _ _).trans hn.le
  have hS : ‖p.2 - S₀‖ ≤ KSComplexPerturbationRadius.radius μ ρ :=
    (le_max_right _ _).trans hn.le
  exact (contDiffAt_objective_of_domain V M D A θ x h (KSComplexOwnerObjective.density_domain hμ hfloor p.2 hS)
    (product_domain V hV A hA x h t₀ S₀ hbase hμ hfloor hρ hx hh p ht hS)).contDiffWithinAt

/-- At a positive real point, the support-compressed trace is actual fidelity. -/
theorem objective_real (V : Matrix n m ℂ) (hV : Vᴴ * V = 1)
    (M D : Matrix n n ℂ) (hM : M.IsHermitian) (hD : D.IsHermitian)
    (A : ι → Matrix n n ℂ) (θ : ℝ) (x h : ι → ℝ) (t : ℝ)
    {S : Matrix n n ℂ} (hS : S.PosDef)
    (hp : (KSComplexTraceDomain.compressedSource V A x h ((t : ℂ),S)).PosDef)
    (hrec : V * KSComplexTraceDomain.compressedSource V A x h ((t : ℂ),S) * Vᴴ =
      KSComplexTraceSource.source A x h ((t : ℂ),S)) :
    objective V M D A θ x h ((t : ℂ),S) =
      (realTrace ((M + t • D) * S) +
        2 * fidelity S (KSComplexTraceSource.source A x h ((t : ℂ),S)) +
        2 * θ * realTrace (CFC.sqrt S) : ℝ) := by
  have hh : (M + t • D).IsHermitian := by
    change (M + t • D)ᴴ = M + t • D
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, star_trivial, hM.eq, hD.eq]
  have hc : complexCenter M D (t : ℂ) = M + t • D := by
    simp only [complexCenter, Complex.coe_smul]
  rw [objective, hc, KSComplexOwnerPerturbation.trace_pairing_real _ S hh hS.isHermitian]
  simp only [KSComplexTraceDomain.compressedDensity, KSSupportSymmetry.compress,
    Prod.snd]
  rw [
    KSHolomorphicFidelity.traceRoot_compressed_eq_fidelity V hV hS hp,
    hrec, KSHolomorphicFidelity.traceRoot_posDef hS]
  simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_ofNat]

end MatrixSpencer.KSComplexTraceObjective
