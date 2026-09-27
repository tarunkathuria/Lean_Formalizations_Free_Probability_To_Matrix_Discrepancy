import MatrixSpencer.KSComplexTraceObjective
import MatrixSpencer.KSComplexCompressionBounds
import MatrixSpencer.KSComplexObjectiveBound
import MatrixSpencer.KSComplexTraceBounds

/-!
# Value bound for the actual complex KS owner objective

The constructed trace-root function and actual fixed-support compression
are used throughout. Its analytic domain and concrete polynomial norm
bounds supply a finite arithmetic value cap for Cauchy's estimate.
-/

open Matrix Set Metric
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
noncomputable section
namespace MatrixSpencer.KSComplexTraceValueBound

variable {ι n k : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
  [Fintype k] [DecidableEq k]
local instance {k : Type*} [Fintype k] [DecidableEq k] : CStarAlgebra (Matrix k k ℂ) := {}
open KSComplexTraceObjective KSComplexTraceDomain KSCompactResolvent

/-- Actual complex objective bound from its physical matrix norms. The
support's dimension is bounded by the original physical dimension. -/
theorem objective_norm_le (V : Matrix n k ℂ) (hV : Vᴴ * V = 1)
    (hcard : Fintype.card k ≤ Fintype.card n)
    (M D : Matrix n n ℂ) (A : ι → Matrix n n ℂ)
    (x h : ι → ℝ) {θ R s m : ℝ} (hθ : 0 ≤ θ) (hR : 0 ≤ R)
    (p : KSComplexTraceSource.Space n)
    (hcenter : ‖complexCenter M D p.1‖ ≤ R) (hS : ‖p.2‖ ≤ s)
    (hsource : ‖KSComplexTraceSource.source A x h p‖ ≤ m)
    (hprod : Domain (compressedDensity V p.2 * compressedSource V A x h p))
    (hdensity : Domain p.2) :
    ‖objective V M D A θ x h p‖ ≤ KSComplexObjectiveBound.valueCap (Fintype.card n) R s m θ := by
  have hcard' : (Fintype.card k : ℝ) ≤ Fintype.card n := Nat.cast_le.mpr hcard
  have hq := KSCompactTraceRoots.traceRoot_product_caps hprod
    ((KSComplexCompressionBounds.compression_norm_le V hV p.2).trans hS)
    ((KSComplexCompressionBounds.compression_norm_le V hV (KSComplexTraceSource.source A x h p)).trans hsource)
  have hq' : ‖traceRoot (compressedDensity V p.2 * compressedSource V A x h p)‖ ≤
      (Fintype.card n : ℝ) * Real.sqrt (s * m) :=
    hq.trans (mul_le_mul_of_nonneg_right hcard' (Real.sqrt_nonneg _))
  have hr := (KSCompactTraceRoots.traceRoot_norm_le hdensity).trans
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hS) (Nat.cast_nonneg _))
  exact KSComplexObjectiveBound.value_norm_le (complexCenter M D p.1) p.2
    (traceRoot (compressedDensity V p.2 * compressedSource V A x h p)) (traceRoot p.2)
    hθ hR hcenter hS hq' hr

/-- Uniform value control on the actual analytic ball. Real time is
recentered before applying the polynomial estimate; no bound on t₀ is needed. -/
theorem objective_norm_le_on_ball (V : Matrix n k ℂ) (hV : Vᴴ * V = 1)
    (hcard : Fintype.card k ≤ Fintype.card n) (M D : Matrix n n ℂ)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (θ : ℝ) (x h : ι → ℝ) (t₀ : ℝ) (S₀ : Matrix n n ℂ)
    (hbase : (baseSource V A (fun i => x i+t₀*h i) h S₀).PosDef)
    {μ ρ R Dcap : ℝ}
    (hμ : 0 < μ) (hfloor : μ • (1 : Matrix n n ℂ) ≤ S₀)
    (hρ : 0 < ρ) (hx : ∀ i, |x i+t₀*h i| ≤ 1-ρ) (hh : ∀ i, |h i| ≤ 2)
    (hS₀ : ‖S₀‖ ≤ 1) (hcenter : ‖complexCenter M D (t₀ : ℂ)‖ ≤ R)
    (hD : ‖D‖ ≤ Dcap) (hR : 0 ≤ R) (hθ : 0 ≤ θ)
    (p : KSComplexTraceSource.Space n)
    (hp : p ∈ Metric.ball ((t₀ : ℂ),S₀) (KSComplexPerturbationRadius.radius μ ρ)) :
    ‖objective V M D A θ x h p‖ ≤ KSComplexObjectiveBound.valueCap (Fintype.card n)
      (R+Dcap) 2 (KSComplexTraceBounds.sourceBudget A) θ := by
  have hn : ‖p-((t₀ : ℂ),S₀)‖ < KSComplexPerturbationRadius.radius μ ρ := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hp
  have ht : ‖p.1-(t₀ : ℂ)‖ ≤ KSComplexPerturbationRadius.radius μ ρ :=
    (le_max_left _ _).trans hn.le
  have hS : ‖p.2-S₀‖ ≤ KSComplexPerturbationRadius.radius μ ρ :=
    (le_max_right _ _).trans hn.le
  have hr := KSComplexPerturbationRadius.radius_le_one μ ρ
  have htone := ht.trans hr
  have hStwo : ‖p.2‖ ≤ 2 := by
    have hb := norm_add_le (p.2-S₀) S₀
    rw [sub_add_cancel] at hb
    linarith
  have hxone : ∀ i, |x i+t₀*h i| ≤ 1 := fun i => by have hi := hx i; linarith
  have hsource : ‖KSComplexTraceSource.source A x h p‖ ≤
      KSComplexTraceBounds.sourceBudget A := by
    have hb := KSComplexTraceBounds.source_norm_le_budget A hA
      (fun i => x i+t₀*h i) h hxone hh (p.1-t₀) htone p.2 hStwo
    rw [← KSComplexTraceSource.source_shift] at hb
    have he : ((t₀ : ℂ)+(p.1-t₀),p.2)=p := by
      apply Prod.ext
      · dsimp; ring
      · rfl
    rwa [he] at hb
  have hcenter' : ‖complexCenter M D p.1‖ ≤ R+Dcap := by
    have he : complexCenter M D p.1 = complexCenter M D (t₀ : ℂ) + (p.1-t₀) • D := by
      rw [← complexCenter_shift]
      congr 1
      ring
    rw [he]
    apply (norm_add_le _ _).trans
    rw [norm_smul]
    have hm := mul_le_mul htone hD (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    linarith
  exact objective_norm_le V hV hcard M D A x h hθ
    (add_nonneg hR ((norm_nonneg _).trans hD)) p hcenter' hStwo hsource
    (product_domain V hV A hA x h t₀ S₀ hbase hμ hfloor hρ hx hh p ht hS)
    (KSComplexOwnerObjective.density_domain hμ hfloor p.2 hS)

end MatrixSpencer.KSComplexTraceValueBound
