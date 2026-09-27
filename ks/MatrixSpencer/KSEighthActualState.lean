import MatrixSpencer.KSEighthSupport
import MatrixSpencer.KSEighthBlocks
import MatrixSpencer.KSCommonSource
import MatrixSpencer.KSArbitraryRetirement

/-! The actual full optimizer and fixed two-sign source frame of the old route. -/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSEighthActualState
open KSEighthBlocks KSEighthBalanced

variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n] [Nonempty n]
local instance stateCStar {s : Type*} [Fintype s] [DecidableEq s] : CStarAlgebra (Matrix s s ℂ) := {}

def family (v : ι → n → ℂ) := KSIndependentSource.family (fun i => KSRankOne.atom (v i))
def covariance (x : ι → ℝ) := KSIndependentSource.coefficientCovariance (owner x)
def kraus (v : ι → n → ℂ) (x : ι → ℝ) := covarianceKraus (family v) (covariance x)

def fullDensity (H : Matrix n n ℂ) (v : ι → n → ℂ) (x : ι → ℝ) (θ : ℝ) :=
  hermitianDensityOptimizer (signedLift H) (kraus v x) θ

def densityBlock (H : Matrix n n ℂ) (v : ι → n → ℂ) (x : ι → ℝ) (θ : ℝ) (b : Bool) :
    Matrix n n ℂ := if b then (fullDensity H v x θ : Matrix (n ⊕ n) (n ⊕ n) ℂ).toBlocks₁₁
      else (fullDensity H v x θ : Matrix (n ⊕ n) (n ⊕ n) ℂ).toBlocks₂₂

def supportDensity (H : Matrix n n ℂ) (v : ι → n → ℂ) (x : ι → ℝ) (θ : ℝ) (b : Bool) :=
  (KSEighthSupport.embedding v)ᴴ * densityBlock H v x θ b * KSEighthSupport.embedding v

def supportSource (H : Matrix n n ℂ) (v : ι → n → ℂ) (x : ι → ℝ) (θ : ℝ) (b : Bool) :=
  KSBalancedSpin.source (fun i => KSRankOne.atom (KSEighthSupport.compressedVector v i)) (owner x)
    (supportDensity H v x θ b)

def transport (H : Matrix n n ℂ) (v : ι → n → ℂ) (x : ι → ℝ) (θ : ℝ) (b : Bool) :=
  transportOptimizer (supportDensity H v x θ b) (supportSource H v x θ b)

def fullEmbedding (v : ι → n → ℂ) := doubledRect (KSEighthSupport.embedding v)

def fullTransport (H : Matrix n n ℂ) (v : ι → n → ℂ) (x : ι → ℝ) (θ : ℝ) :=
  blockDiag (transport H v x θ true) (transport H v x θ false)

theorem covariance_posSemidef (x : ι → ℝ) (hx : ∀ i, |x i| ≤ (1 / 8 : ℝ)) :
    (covariance x).PosSemidef := KSIndependentSource.coefficientCovariance_posSemidef
      (fun i => (owner_pos x hx i).le)

theorem family_isHermitian (v : ι → n → ℂ) (j : ι × Bool) : (family v j).IsHermitian :=
  KSIndependentSource.family_isHermitian _ (fun i => KSRankOne.atom_isHermitian (v i)) j

theorem fullDensity_posDef (H : Matrix n n ℂ) (v : ι → n → ℂ) (x : ι → ℝ)
    {θ : ℝ} (hθ : 0 < θ) : (fullDensity H v x θ : Matrix (n ⊕ n) (n ⊕ n) ℂ).PosDef :=
  hermitianDensityOptimizer_posDef _ _ hθ

theorem fullDensity_trace (H : Matrix n n ℂ) (v : ι → n → ℂ) (x : ι → ℝ) (θ : ℝ) :
    realTrace (fullDensity H v x θ : Matrix (n ⊕ n) (n ⊕ n) ℂ) = 1 :=
  hermitianDensityOptimizer_trace _ _ _

theorem fullDensity_isMaxOn (H : Matrix n n ℂ) (v : ι → n → ℂ) (x : ι → ℝ) (θ : ℝ) :
    ∀ T ∈ densitySet, densityObjective (signedLift H) (kraus v x) θ T ≤
      densityObjective (signedLift H) (kraus v x) θ (fullDensity H v x θ) :=
  densityOptimizer_isMaxOn _ _ _

theorem fullDensity_blockDiagonal (H : Matrix n n ℂ) (v : ι → n → ℂ) (x : ι → ℝ)
    (hx : ∀ i, |x i| ≤ (1 / 8 : ℝ)) {θ : ℝ} (hθ : 0 < θ) :
    (fullDensity H v x θ : Matrix (n ⊕ n) (n ⊕ n) ℂ) =
      blockDiag (densityBlock H v x θ true) (densityBlock H v x θ false) := by
  apply KSCommonSource.independent_optimizer_blockDiagonal H _
    (fun i => KSRankOne.atom_isHermitian (v i)) (fun i => (owner_pos x hx i).le) hθ
  · exact ⟨(fullDensity_posDef H v x hθ).posSemidef, fullDensity_trace H v x θ⟩
  · intro T hT
    change ownerObjective (signedLift H) (family v) (covariance x) θ T ≤
      ownerObjective (signedLift H) (family v) (covariance x) θ (fullDensity H v x θ)
    rw [ownerObjective_eq_densityObjective _ _ (family_isHermitian v) (covariance_posSemidef x hx),
      ownerObjective_eq_densityObjective _ _ (family_isHermitian v) (covariance_posSemidef x hx)]
    exact fullDensity_isMaxOn H v x θ T hT

theorem densityBlock_posDef (H : Matrix n n ℂ) (v : ι → n → ℂ) (x : ι → ℝ)
    {θ : ℝ} (hθ : 0 < θ) (b : Bool) : (densityBlock H v x θ b).PosDef := by
  cases b
  · exact posDef_toBlocks22 (fullDensity_posDef H v x hθ)
  · exact posDef_toBlocks11 (fullDensity_posDef H v x hθ)

theorem supportDensity_posDef (H : Matrix n n ℂ) (v : ι → n → ℂ) (x : ι → ℝ)
    {θ : ℝ} (hθ : 0 < θ) (b : Bool) : (supportDensity H v x θ b).PosDef :=
  posDef_isometry_compression (KSEighthSupport.embedding v)
    (krausSupportEmbedding_isometry _) (densityBlock_posDef H v x hθ b)

theorem supportSource_posDef (H : Matrix n n ℂ) (v : ι → n → ℂ) (hv : ∀ i, v i ≠ 0)
    (x : ι → ℝ) (hx : ∀ i, |x i| ≤ (1 / 8 : ℝ)) {θ : ℝ} (hθ : 0 < θ) (b : Bool) :
    (supportSource H v x θ b).PosDef := by
  exact KSEighthSupport.compressed_source_posDef v hv (densityBlock_posDef H v x hθ b)
    (owner x) (fun i => by have hh := KSEighthComparison.eighth_owner_lower (hx i); exact le_trans (by norm_num) hh)

theorem transport_posDef (H : Matrix n n ℂ) (v : ι → n → ℂ) (hv : ∀ i, v i ≠ 0)
    (x : ι → ℝ) (hx : ∀ i, |x i| ≤ (1 / 8 : ℝ)) {θ : ℝ} (hθ : 0 < θ) (b : Bool) :
    (transport H v x θ b).PosDef := transportOptimizer_posDef
      (supportDensity_posDef H v x hθ b) (supportSource_posDef H v hv x hx hθ b)

theorem transport_solve (H : Matrix n n ℂ) (v : ι → n → ℂ) (hv : ∀ i, v i ≠ 0)
    (x : ι → ℝ) (hx : ∀ i, |x i| ≤ (1 / 8 : ℝ)) {θ : ℝ} (hθ : 0 < θ) (b : Bool) :
    transport H v x θ b * supportSource H v x θ b * transport H v x θ b =
      supportDensity H v x θ b := transportOptimizer_solve
        (supportDensity_posDef H v x hθ b) (supportSource_posDef H v hv x hx hθ b)

theorem fullEmbedding_isometry (v : ι → n → ℂ) :
    (fullEmbedding v)ᴴ * fullEmbedding v = 1 := doubledRect_isometry (krausSupportEmbedding_isometry _)

theorem fullTransport_posDef (H : Matrix n n ℂ) (v : ι → n → ℂ) (hv : ∀ i, v i ≠ 0)
    (x : ι → ℝ) (hx : ∀ i, |x i| ≤ (1 / 8 : ℝ)) {θ : ℝ} (hθ : 0 < θ) :
    (fullTransport H v x θ).PosDef := blockDiag_posDef
      (transport_posDef H v hv x hx hθ true) (transport_posDef H v hv x hx hθ false)

end MatrixSpencer.KSEighthActualState
