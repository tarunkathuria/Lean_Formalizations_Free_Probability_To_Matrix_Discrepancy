import SeamlessKS.NumericalRegularityObjective
import MatrixSpencer.KSComplexOwnerValueBound

/-! Explicit value caps for the new joint objective on its analytic ball. -/
open Matrix Set Metric
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
noncomputable section
namespace SeamlessKS
namespace NumericalRegularityBounds
open MatrixSpencer
open NumericalRegularityObjective NumericalRegularityDomain KSCompactResolvent
open KSOwnerInputBounds
variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
local instance {k : Type*} [Fintype k] [DecidableEq k] : CStarAlgebra (Matrix k k ℂ) := {}
set_option maxHeartbeats 1200000

def sourceBudget (v : ι → n → ℂ) : ℝ := 2 * KSComplexPolynomialBounds.sourceBudget v

theorem sourceBudget_pos (v : ι → n → ℂ) : 0 < sourceBudget v :=
  mul_pos (by norm_num) (KSComplexPolynomialBounds.sourceBudget_pos v)

theorem owner_norm_le {ζ x h : ℝ} (hζ : 0 ≤ ζ) (hζone : ζ ≤ 1)
    (hx : |x| ≤ 1) (hh : |h| ≤ 2) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖Source.complexWeight 64 ζ ((x : ℂ) + z * (h : ℂ))‖ ≤ 1280 := by
  have ha : ‖(x : ℂ) + z * (h : ℂ)‖ ≤ 3 := by
    apply (norm_add_le _ _).trans
    rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
    have hm := mul_le_mul hz hh (abs_nonneg h) (by norm_num : (0 : ℝ) ≤ 1)
    linarith
  exact (Source.norm_complexWeight_le (by norm_num : (0 : ℝ) ≤ 64) hζ hζone ha).trans (by norm_num)

theorem source_norm_le_budget {ζ : ℝ} (hζ : 0 ≤ ζ) (hζone : ζ ≤ 1)
    (v : ι → n → ℂ) (x h : ι → ℝ)
    (hx : ∀ i, |x i| ≤ 1) (hh : ∀ i, |h i| ≤ 2) (z : ℂ) (hz : ‖z‖ ≤ 1)
    (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) (hS : ‖S‖ ≤ 2) :
    ‖NumericalRegularitySource.source ζ v x h (z, S)‖ ≤ sourceBudget v := by
  have he (i : ι) : ‖NumericalRegularitySource.atom v i‖ ≤ matrixBound (NumericalRegularitySource.atom v i) :=
    norm_le_matrixBound _ (KSComplexSpinSource.atom_posSemidef v i).isHermitian
  calc _ ≤ ∑ i, ‖(Source.complexWeight 64 ζ ((x i : ℂ) + z * (h i : ℂ)) *
        Matrix.trace (NumericalRegularitySource.atom v i * S)) • NumericalRegularitySource.atom v i‖ := norm_sum_le _ _
    _ ≤ ∑ i, 2560 * (Fintype.card (n ⊕ n) : ℝ) * matrixBound (NumericalRegularitySource.atom v i) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul, norm_mul]
      have hbi : 0 ≤ matrixBound (NumericalRegularitySource.atom v i) := (matrixBound_pos _).le
      have hnorm := he i
      have ht := KSComplexObjectiveBound.norm_trace_mul_le_card_mul_norm (NumericalRegularitySource.atom v i) S
      have ht' : ‖Matrix.trace (NumericalRegularitySource.atom v i * S)‖ ≤
          (Fintype.card (n ⊕ n) : ℝ) * matrixBound (NumericalRegularitySource.atom v i) * 2 := by
        exact ht.trans (by gcongr)
      have ho := owner_norm_le hζ hζone (hx i) (hh i) hz
      calc _ ≤ 1280 * ((Fintype.card (n ⊕ n) : ℝ) * matrixBound (NumericalRegularitySource.atom v i) * 2) *
          matrixBound (NumericalRegularitySource.atom v i) := by gcongr
        _ = _ := by ring
    _ ≤ sourceBudget v := by
      rw [← Finset.mul_sum]
      unfold sourceBudget KSComplexPolynomialBounds.sourceBudget NumericalRegularitySource.atom
      linarith

/-- The actual objective is bounded using compressed matrix norms only. -/
theorem objective_norm_le (ζ : ℝ) (M : Matrix (n ⊕ n) (n ⊕ n) ℂ) (v : ι → n → ℂ)
    (x h : ι → ℝ) {θ R s m : ℝ} (hθ : 0 ≤ θ) (hR : 0 ≤ R)
    (p : KSComplexSpinSource.Space n)
    (hcenter : ‖complexCenter M v h p.1‖ ≤ R) (hS : ‖p.2‖ ≤ s)
    (hsource : ‖NumericalRegularitySource.source ζ v x h p‖ ≤ m)
    (hprod : Domain (compressedDensity v p.2 * compressedSource ζ v x h p))
    (hdensity : Domain p.2) :
    ‖objective ζ M v θ x h p‖ ≤ KSComplexObjectiveBound.valueCap (Fintype.card (n ⊕ n)) R s m θ := by
  have hcard : (Fintype.card (Support v) : ℝ) ≤ Fintype.card (n ⊕ n) :=
    Nat.cast_le.mpr (KSComplexCompressionBounds.actual_support_card_le v)
  have hd : ‖compressedDensity v p.2‖ ≤ s :=
    (KSComplexCompressionBounds.spin_compression_norm_le (fun i => KSRankOne.atom (v i)) p.2).trans hS
  have hm : ‖compressedSource ζ v x h p‖ ≤ m :=
    (KSComplexCompressionBounds.spin_compression_norm_le (fun i => KSRankOne.atom (v i)) _).trans hsource
  have hq := KSCompactTraceRoots.traceRoot_product_caps hprod hd hm
  have hq' : ‖traceRoot (compressedDensity v p.2 * compressedSource ζ v x h p)‖ ≤
      (Fintype.card (n ⊕ n) : ℝ) * Real.sqrt (s * m) :=
    hq.trans (mul_le_mul_of_nonneg_right hcard (Real.sqrt_nonneg _))
  have hr := (KSCompactTraceRoots.traceRoot_norm_le hdensity).trans
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hS) (Nat.cast_nonneg _))
  exact KSComplexObjectiveBound.value_norm_le (complexCenter M v h p.1) p.2
    (traceRoot (compressedDensity v p.2 * compressedSource ζ v x h p)) (traceRoot p.2)
    hθ hR hcenter hS hq' hr

/-- Uniform value control on the actual analytic ball. Real time is
recentered before applying the polynomial estimate; no bound on t₀ is needed. -/
theorem objective_norm_le_on_ball {ζ : ℝ} (hζ : 0 < ζ) (hζone : ζ ≤ 1) (M : Matrix (n ⊕ n) (n ⊕ n) ℂ)
    (v : ι → n → ℂ) (θ : ℝ) (x h : ι → ℝ) (t₀ : ℝ)
    (S₀ : Matrix (n ⊕ n) (n ⊕ n) ℂ) {μ ρ R : ℝ}
    (hμ : 0 < μ) (hfloor : μ • (1 : Matrix (n ⊕ n) (n ⊕ n) ℂ) ≤ S₀)
    (hρ : 0 < ρ) (hx : ∀ i, |x i + t₀ * h i| ≤ 1 - ρ) (hh : ∀ i, |h i| ≤ 2)
    (hS₀ : ‖S₀‖ ≤ 1) (hcenter : ‖complexCenter M v h (t₀ : ℂ)‖ ≤ R)
    (hR : 0 ≤ R) (hθ : 0 ≤ θ)
    (p : KSComplexSpinSource.Space n)
    (hp : p ∈ Metric.ball ((t₀ : ℂ), S₀) (NumericalRegularity.radius μ ρ ζ)) :
    ‖objective ζ M v θ x h p‖ ≤ KSComplexObjectiveBound.valueCap (Fintype.card (n ⊕ n))
      (R + 2 * KSComplexPolynomialBounds.slopeBudget v) 2
      (sourceBudget v) θ := by
  have hn : ‖p - ((t₀ : ℂ), S₀)‖ < NumericalRegularity.radius μ ρ ζ := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hp
  have ht : ‖p.1 - (t₀ : ℂ)‖ ≤ NumericalRegularity.radius μ ρ ζ :=
    (le_max_left _ _).trans hn.le
  have hS : ‖p.2 - S₀‖ ≤ NumericalRegularity.radius μ ρ ζ :=
    (le_max_right _ _).trans hn.le
  have hr := NumericalRegularity.radius_le_one μ ρ ζ
  have htone : ‖p.1 - (t₀ : ℂ)‖ ≤ 1 := by linarith
  have hStwo : ‖p.2‖ ≤ 2 := by
    have hb := norm_add_le (p.2 - S₀) S₀
    rw [sub_add_cancel] at hb
    linarith
  have hxone : ∀ i, |x i + t₀ * h i| ≤ 1 := fun i => by
    have hi := hx i
    linarith
  have hsource : ‖NumericalRegularitySource.source ζ v x h p‖ ≤
      sourceBudget v := by
    have hb := source_norm_le_budget hζ.le hζone v
      (fun i => x i + t₀ * h i) h hxone hh (p.1 - t₀) htone p.2 hStwo
    rw [← NumericalRegularitySource.source_shift] at hb
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
  exact objective_norm_le ζ M v x h hθ
    (by have := (KSComplexPolynomialBounds.slopeBudget_pos v).le; positivity)
    p hcenter' hStwo hsource
    (product_domain hζ v x h t₀ S₀ hμ hfloor hρ hx hh p ht hS)
    (density_domain hζ hμ hfloor p.2 hS)

end NumericalRegularityBounds
end SeamlessKS
