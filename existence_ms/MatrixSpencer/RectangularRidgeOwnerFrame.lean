import MatrixSpencer.DyadicOwnerFrame

/-! Optimizer-independent owner frames. These estimates hold at every positive
density of trace at most one. In particular, changing the regularizer does not
require comparing the old and new optimizers: each cap is imposed at the same
density at which its response is estimated. -/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.RectangularRidgeOwnerFrame
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n]
local instance ridgeOwnerFrameLocal1 {j : Type*} [Fintype j] [DecidableEq j] : CStarAlgebra (Matrix j j ℂ) := {}

def sourceDensity (A : ι → Matrix n n ℂ) (C : Matrix ι ι ℝ) (S : Matrix n n ℂ) :=
  krausCompressedDensity (covarianceKraus A C) S

def sourceTransport (A : ι → Matrix n n ℂ) (C : Matrix ι ι ℝ) (S : Matrix n n ℂ) :=
  transportOptimizer (sourceDensity A C S)
    (krausChannel (krausReducedFamily (covarianceKraus A C)) (sourceDensity A C S))

def ownedGram (A : ι → Matrix n n ℂ) (C : Matrix ι ι ℝ) (S : Matrix n n ℂ) : Matrix ι ι ℝ :=
  covarianceGram A S (krausSupportEmbedding (covarianceKraus A C) * sourceTransport A C S *
    (krausSupportEmbedding (covarianceKraus A C))ᴴ)

theorem sourceDensity_posDef (A : ι → Matrix n n ℂ) (C : Matrix ι ι ℝ)
    {S : Matrix n n ℂ} (hS : S.PosDef) : (sourceDensity A C S).PosDef :=
  krausCompressedDensity_posDef (covarianceKraus A C) hS

theorem sourceSource_posDef (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (C : Matrix ι ι ℝ) {S : Matrix n n ℂ} (hS : S.PosDef) :
    (krausChannel (krausReducedFamily (covarianceKraus A C)) (sourceDensity A C S)).PosDef :=
  krausReducedFamily_source_posDef (covarianceKraus A C)
    (mixedKraus_isHermitian A (CFC.sqrt C) hA) hS

theorem sourceTransport_posDef (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (C : Matrix ι ι ℝ) {S : Matrix n n ℂ} (hS : S.PosDef) : (sourceTransport A C S).PosDef :=
  transportOptimizer_posDef (sourceDensity_posDef A C hS) (sourceSource_posDef A hA C hS)

theorem sourceDensity_trace_le_one (A : ι → Matrix n n ℂ) (C : Matrix ι ι ℝ)
    {S : Matrix n n ℂ} (hS : S.PosSemidef) (htr : realTrace S ≤ 1) :
    realTrace (sourceDensity A C S) ≤ 1 :=
  (realTrace_isometry_compression_le hS (krausSupportEmbedding (covarianceKraus A C))
    (krausSupportEmbedding_isometry (covarianceKraus A C))).trans htr

theorem three_budgets (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (hN : ∀ i, ‖A i‖ ≤ 1) {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (hC1 : C ≤ 1)
    {S : Matrix n n ℂ} (hS : S.PosDef) (htr : realTrace S ≤ 1) :
    realTrace (balancedDensity (sourceDensity A C S) (sourceTransport A C S)) ≤
        Real.sqrt (Fintype.card ι : ℝ) ∧
      realTrace (balancedRoot (sourceDensity A C S) (sourceTransport A C S) *
        balancedRoot (sourceDensity A C S) (sourceTransport A C S)) ≤ (Fintype.card ι : ℝ) ∧
      realTrace ((sourceTransport A C S)⁻¹ *
        balancedDensity (sourceDensity A C S) (sourceTransport A C S)) ≤ (Fintype.card ι : ℝ) := by
  let V := krausSupportEmbedding (covarianceKraus A C)
  let A₀ := compressedOriginalFamily A V
  have hV : Vᴴ * V = 1 := krausSupportEmbedding_isometry (covarianceKraus A C)
  have hA₀ : ∀ i, (A₀ i).IsHermitian := fun i => isometry_compression_isHermitian V (hA i)
  have hN₀ : ∀ i, ‖A₀ i‖ ≤ 1 := fun i => isometry_compression_norm_le_one V hV (hA i) (hN i)
  have hB₀ : covarianceKraus A₀ C = krausReducedFamily (covarianceKraus A C) :=
    (krausReducedFamily_eq_covarianceKraus_compressed A C).symm
  have heq : covarianceSource A₀ C (sourceDensity A C S) =
      krausChannel (krausReducedFamily (covarianceKraus A C)) (sourceDensity A C S) := by
    rw [covarianceSource_eq_kraus A₀ hA₀ hC, hB₀]
  have hM : (covarianceSource A₀ C (sourceDensity A C S)).PosDef := by
    rw [heq]
    exact sourceSource_posDef A hA C hS
  have hb := compressed_balancedTransport_budgets A hA hN hC hC1 V hV hS htr hM
  change realTrace (balancedDensity (sourceDensity A C S)
      (transportOptimizer (sourceDensity A C S) (covarianceSource A₀ C (sourceDensity A C S)))) ≤ _ ∧
    realTrace (balancedRoot (sourceDensity A C S)
      (transportOptimizer (sourceDensity A C S) (covarianceSource A₀ C (sourceDensity A C S))) *
      balancedRoot (sourceDensity A C S)
      (transportOptimizer (sourceDensity A C S) (covarianceSource A₀ C (sourceDensity A C S)))) ≤ _ at hb
  rw [heq] at hb
  have hi := DyadicBalancedModel.balancedTransport_inverseDensity_budget A₀ hA₀ hN₀ hC hC1
    (sourceDensity_posDef A C hS) (sourceDensity_trace_le_one A C hS.posSemidef htr) hM
  dsimp only at hi
  rw [heq] at hi
  exact ⟨hb.1, hb.2, hi⟩

theorem balancedGram_cap (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (hC1 : C ≤ 1)
    {S : Matrix n n ℂ} (hS : S.PosDef) {t : ℝ} (ht : 0 ≤ t)
    (hcap : ∀ u : EuclideanSpace ℝ ι,
      u ∈ LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℝ) C).toLinearMap →
      WithLp.ofLp u ⬝ᵥ (ownedGram A C S *ᵥ WithLp.ofLp u) ≤
        t * (WithLp.ofLp u ⬝ᵥ WithLp.ofLp u)) :
    physicalRealGram (balancedDensity (sourceDensity A C S) (sourceTransport A C S))
      (balancedKraus (krausReducedFamily (covarianceKraus A C)) (sourceTransport A C S)) ≤
      algebraMap ℝ (Matrix ι ι ℝ) t :=
  compressed_balancedGram_cap A hA hC hC1 hS.posSemidef
    (sourceTransport A C S) (sourceTransport_posDef A hA C hS) ht hcap

theorem balanced_family_data (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (C : Matrix ι ι ℝ) {S : Matrix n n ℂ} (hS : S.PosDef) :
    let D := balancedKraus (krausReducedFamily (covarianceKraus A C)) (sourceTransport A C S)
    (∀ a, (D a).IsHermitian) ∧
      krausChannel D (balancedDensity (sourceDensity A C S) (sourceTransport A C S)) =
        balancedDensity (sourceDensity A C S) (sourceTransport A C S) := by
  dsimp only
  have hB := mixedKraus_isHermitian A (CFC.sqrt C) hA
  exact ⟨balancedKraus_isHermitian _ (krausReducedFamily_isHermitian _ hB) _,
    balancedKraus_fixedPoint _ (sourceTransport_posDef A hA C hS)
      (transportOptimizer_solve (sourceDensity_posDef A C hS) (sourceSource_posDef A hA C hS))⟩

end MatrixSpencer.RectangularRidgeOwnerFrame
