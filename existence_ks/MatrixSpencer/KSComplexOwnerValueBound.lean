import MatrixSpencer.KSComplexOwnerObjective
import MatrixSpencer.KSComplexCompressionBounds
import MatrixSpencer.KSComplexObjectiveBound
import MatrixSpencer.KSComplexPolynomialBounds

/-!
# Value bound for the actual complex KS owner objective

The constructed trace-root function and actual fixed-support compression
are used throughout. Its analytic domain and concrete polynomial norm
bounds supply a finite arithmetic value cap for Cauchy's estimate.
-/

open Matrix Set Metric
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
noncomputable section
namespace MatrixSpencer.KSComplexOwnerValueBound

variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
local instance {k : Type*} [Fintype k] [DecidableEq k] : CStarAlgebra (Matrix k k ℂ) := {}
open KSComplexOwnerObjective KSComplexSpinDomain KSCompactResolvent

/-- Actual complex objective bound from its physical matrix norms. The
support's dimension is bounded by the original physical dimension. -/
theorem objective_norm_le (M : Matrix (n ⊕ n) (n ⊕ n) ℂ) (v : ι → n → ℂ)
    (x h : ι → ℝ) {θ R s m : ℝ} (hθ : 0 ≤ θ) (hR : 0 ≤ R)
    (p : KSComplexSpinSource.Space n)
    (hcenter : ‖complexCenter M v h p.1‖ ≤ R) (hS : ‖p.2‖ ≤ s)
    (hsource : ‖KSComplexSpinSource.source v x h p‖ ≤ m)
    (hprod : Domain (compressedDensity v p.2 * compressedSource v x h p))
    (hdensity : Domain p.2) :
    ‖objective M v θ x h p‖ ≤ KSComplexObjectiveBound.valueCap (Fintype.card (n ⊕ n)) R s m θ := by
  have hcard : (Fintype.card (Support v) : ℝ) ≤ Fintype.card (n ⊕ n) :=
    Nat.cast_le.mpr (KSComplexCompressionBounds.actual_support_card_le v)
  have hq := KSCompactTraceRoots.traceRoot_product_caps hprod
    ((KSComplexCompressionBounds.actual_compressedDensity_norm_le v p.2).trans hS)
    ((KSComplexCompressionBounds.actual_compressedSource_norm_le v x h p).trans hsource)
  have hq' : ‖traceRoot (compressedDensity v p.2 * compressedSource v x h p)‖ ≤
      (Fintype.card (n ⊕ n) : ℝ) * Real.sqrt (s * m) :=
    hq.trans (mul_le_mul_of_nonneg_right hcard (Real.sqrt_nonneg _))
  have hr := (KSCompactTraceRoots.traceRoot_norm_le hdensity).trans
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hS) (Nat.cast_nonneg _))
  exact KSComplexObjectiveBound.value_norm_le (complexCenter M v h p.1) p.2
    (traceRoot (compressedDensity v p.2 * compressedSource v x h p)) (traceRoot p.2)
    hθ hR hcenter hS hq' hr

/-- Uniform value control on the actual analytic ball. Real time is
recentered before applying the polynomial estimate; no bound on t₀ is needed. -/
theorem objective_norm_le_on_ball (M : Matrix (n ⊕ n) (n ⊕ n) ℂ)
    (v : ι → n → ℂ) (θ : ℝ) (x h : ι → ℝ) (t₀ : ℝ)
    (S₀ : Matrix (n ⊕ n) (n ⊕ n) ℂ) {μ ρ R : ℝ}
    (hμ : 0 < μ) (hfloor : μ • (1 : Matrix (n ⊕ n) (n ⊕ n) ℂ) ≤ S₀)
    (hρ : 0 < ρ) (hx : ∀ i, |x i + t₀ * h i| ≤ 1 - ρ) (hh : ∀ i, |h i| ≤ 2)
    (hS₀ : ‖S₀‖ ≤ 1) (hcenter : ‖complexCenter M v h (t₀ : ℂ)‖ ≤ R)
    (hR : 0 ≤ R) (hθ : 0 ≤ θ)
    (p : KSComplexSpinSource.Space n)
    (hp : p ∈ Metric.ball ((t₀ : ℂ), S₀) (KSComplexPerturbationRadius.radius μ ρ)) :
    ‖objective M v θ x h p‖ ≤ KSComplexObjectiveBound.valueCap (Fintype.card (n ⊕ n))
      (R + 2 * KSComplexPolynomialBounds.slopeBudget v) 2
      (KSComplexPolynomialBounds.sourceBudget v) θ := by
  have hn : ‖p - ((t₀ : ℂ), S₀)‖ < KSComplexPerturbationRadius.radius μ ρ := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hp
  have ht : ‖p.1 - (t₀ : ℂ)‖ ≤ KSComplexPerturbationRadius.radius μ ρ :=
    (le_max_left _ _).trans hn.le
  have hS : ‖p.2 - S₀‖ ≤ KSComplexPerturbationRadius.radius μ ρ :=
    (le_max_right _ _).trans hn.le
  have hr := KSComplexPerturbationRadius.radius_le_one μ ρ
  have htone := ht.trans hr
  have hStwo : ‖p.2‖ ≤ 2 := by
    have hb := norm_add_le (p.2 - S₀) S₀
    rw [sub_add_cancel] at hb
    linarith
  have hxone : ∀ i, |x i + t₀ * h i| ≤ 1 := fun i => by
    have hi := hx i
    linarith
  have hsource : ‖KSComplexSpinSource.source v x h p‖ ≤
      KSComplexPolynomialBounds.sourceBudget v := by
    have hb := KSComplexPolynomialBounds.source_norm_le_budget v
      (fun i => x i + t₀ * h i) h hxone hh (p.1 - t₀) htone p.2 hStwo
    rw [← KSComplexSpinSource.source_shift] at hb
    have he : ((t₀ : ℂ) + (p.1 - t₀), p.2) = p := by
      apply Prod.ext
      · dsimp; ring
      · rfl
    rwa [he] at hb
  have hcenter' : ‖complexCenter M v h p.1‖ ≤
      R + 2 * KSComplexPolynomialBounds.slopeBudget v := by
    have hb := KSComplexPolynomialBounds.center_norm_le v h hh
      (complexCenter M v h (t₀ : ℂ)) hcenter (p.1 - t₀) htone
    change ‖complexCenter M v h (t₀ : ℂ) + (p.1 - t₀) • slope v h‖ ≤ _ at hb
    rw [← complexCenter_shift] at hb
    have he : (t₀ : ℂ) + (p.1 - t₀) = p.1 := by ring
    rwa [he] at hb
  exact objective_norm_le M v x h hθ
    (by have := (KSComplexPolynomialBounds.slopeBudget_pos v).le; positivity)
    p hcenter' hStwo hsource
    (product_domain v x h t₀ S₀ hμ hfloor hρ hx hh p ht hS)
    (density_domain hμ hfloor p.2 hS)

end MatrixSpencer.KSComplexOwnerValueBound
