import SeamlessKS.NumericalRegularitySource
import MatrixSpencer.KSComplexSpinDomain

/-! The new smooth source stays in the principal-root domain on an explicit
complex ball, with no lower bound for its positive eigenvalues. -/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace SeamlessKS
namespace NumericalRegularityDomain
open MatrixSpencer KSComplexSpinDomain KSAccretiveProductDomain
variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
local instance {k : Type*} [Fintype k] [DecidableEq k] : CStarAlgebra (Matrix k k ℂ) := {}
abbrev Support (v : ι → n → ℂ) :=
  KSSpinCompression.supportIndex (fun i => KSRankOne.atom (v i))

def frame (v : ι → n → ℂ) : Matrix (n ⊕ n) (Support v) ℂ :=
  KSSpinCompression.embedding (fun i => KSRankOne.atom (v i))

theorem frame_isometry (v : ι → n → ℂ) : (frame v)ᴴ * frame v = 1 :=
  KSSpinCompression.embedding_isometry _

def compressedDensity (v : ι → n → ℂ) (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) :
    Matrix (Support v) (Support v) ℂ := KSSupportSymmetry.compress (frame v) S

def compressedSource (ζ : ℝ) (v : ι → n → ℂ) (x h : ι → ℝ) (p : KSComplexSpinSource.Space n) :
    Matrix (Support v) (Support v) ℂ :=
  KSSupportSymmetry.compress (frame v) (NumericalRegularitySource.source ζ v x h p)

def baseSource (ζ : ℝ) (v : ι → n → ℂ) (x h : ι → ℝ)
    (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) : Matrix (Support v) (Support v) ℂ :=
  compressedSource ζ v x h (0, S)

theorem baseSource_posDef {ζ : ℝ} (hζ : 0 < ζ) (v : ι → n → ℂ) (x h : ι → ℝ)
    {S : Matrix (n ⊕ n) (n ⊕ n) ℂ} {μ ρ : ℝ}
    (hμ : 0 < μ) (hfloor : μ • (1 : Matrix (n ⊕ n) (n ⊕ n) ℂ) ≤ S)
    (hρ : 0 < ρ) (hx : ∀ i, |x i| ≤ 1 - ρ) : (baseSource ζ v x h S).PosDef := by
  have hc : ∀ i, 0 < Source.weight 64 ζ (x i) := by
    intro i
    exact Source.weight_pos (by norm_num) (by have hi := hx i; linarith)
  have hp := KSSpinCompression.compressed_source_posDef v hc (posDef_of_floor hμ hfloor)
  change (KSSupportSymmetry.compress (frame v) (NumericalRegularitySource.source ζ v x h (0, S))).PosDef
  rw [← Complex.ofReal_zero, NumericalRegularitySource.source_real hζ]
  simpa only [zero_mul, add_zero, KSSupportSymmetry.compress, frame,
    KSSpinCompression.embedding, covarianceCompressedSource] using hp

/-- The exact fixed-support whitener used solely to prove the domain bound. -/
def whitener (ζ : ℝ) (v : ι → n → ℂ) (x h : ι → ℝ)
    (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) : Matrix (Support v) (n ⊕ n) ℂ :=
  (CFC.sqrt (baseSource ζ v x h S))⁻¹ * (frame v)ᴴ

omit [DecidableEq ι] in
theorem whitener_congruence (ζ : ℝ) (v : ι → n → ℂ) (x h : ι → ℝ)
    (S X : Matrix (n ⊕ n) (n ⊕ n) ℂ) :
    whitener ζ v x h S * X * (whitener ζ v x h S)ᴴ =
      (CFC.sqrt (baseSource ζ v x h S))⁻¹ *
        KSSupportSymmetry.compress (frame v) X * (CFC.sqrt (baseSource ζ v x h S))⁻¹ := by
  have hs := ((CFC.sqrt_nonneg (baseSource ζ v x h S)).posSemidef.isHermitian.inv).eq
  simp only [whitener, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    hs, KSSupportSymmetry.compress, Matrix.mul_assoc]

theorem whitener_normalizes {ζ : ℝ} (hζ : 0 < ζ) (v : ι → n → ℂ) (x h : ι → ℝ)
    {S : Matrix (n ⊕ n) (n ⊕ n) ℂ} {μ ρ : ℝ}
    (hμ : 0 < μ) (hfloor : μ • (1 : Matrix (n ⊕ n) (n ⊕ n) ℂ) ≤ S)
    (hρ : 0 < ρ) (hx : ∀ i, |x i| ≤ 1 - ρ) :
    whitener ζ v x h S * NumericalRegularitySource.source ζ v x h (0, S) *
      (whitener ζ v x h S)ᴴ = 1 := by
  rw [whitener_congruence]
  change (CFC.sqrt (baseSource ζ v x h S))⁻¹ * baseSource ζ v x h S *
    (CFC.sqrt (baseSource ζ v x h S))⁻¹ = 1
  have hM := baseSource_posDef hζ v x h hμ hfloor hρ hx
  have hu := (CFC.sqrt (baseSource ζ v x h S)).isUnit_iff_isUnit_det.mp hM.posDef_sqrt.isUnit
  conv_lhs => lhs; rhs; rw [← CFC.sqrt_mul_sqrt_self _ hM.posSemidef.nonneg]
  rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul,
    Matrix.mul_nonsing_inv _ hu]

/-- The actual compressed source lies in the relative `1/16` ball. -/
theorem relative_source_bound {ζ : ℝ} (hζ : 0 < ζ) (v : ι → n → ℂ) (x h : ι → ℝ)
    (S Δ : Matrix (n ⊕ n) (n ⊕ n) ℂ) {μ ρ : ℝ}
    (hμ : 0 < μ) (hfloor : μ • (1 : Matrix (n ⊕ n) (n ⊕ n) ℂ) ≤ S)
    (hρ : 0 < ρ) (hx : ∀ i, |x i| ≤ 1 - ρ) (hh : ∀ i, |h i| ≤ 2)
    (z : ℂ) (hz : ‖z‖ ≤ NumericalRegularity.radius μ ρ ζ)
    (hΔ : ‖Δ‖ ≤ NumericalRegularity.radius μ ρ ζ) :
    ‖(CFC.sqrt (baseSource ζ v x h S))⁻¹ * compressedSource ζ v x h (z, S + Δ) *
      (CFC.sqrt (baseSource ζ v x h S))⁻¹ - 1‖ ≤ 1 / 16 := by
  have hp := NumericalRegularitySource.whitened_source_perturbation hζ v x h S Δ hμ hfloor hρ hx hh
    (whitener ζ v x h S) (whitener_normalizes hζ v x h hμ hfloor hρ hx) z hz hΔ
  simpa only [whitener_congruence, compressedSource] using hp

/-- The actual source is accretive throughout the arithmetic-radius ball. -/
theorem compressedSource_strictAccretive {ζ : ℝ} (hζ : 0 < ζ) (v : ι → n → ℂ) (x h : ι → ℝ)
    (S Δ : Matrix (n ⊕ n) (n ⊕ n) ℂ) {μ ρ : ℝ}
    (hμ : 0 < μ) (hfloor : μ • (1 : Matrix (n ⊕ n) (n ⊕ n) ℂ) ≤ S)
    (hρ : 0 < ρ) (hx : ∀ i, |x i| ≤ 1 - ρ) (hh : ∀ i, |h i| ≤ 2)
    (z : ℂ) (hz : ‖z‖ ≤ NumericalRegularity.radius μ ρ ζ)
    (hΔ : ‖Δ‖ ≤ NumericalRegularity.radius μ ρ ζ) :
    StrictAccretive (compressedSource ζ v x h (z, S + Δ)) := by
  have hM := baseSource_posDef hζ v x h hμ hfloor hρ hx
  have hu := (CFC.sqrt (baseSource ζ v x h S)).isUnit_iff_isUnit_det.mp hM.posDef_sqrt.isUnit
  have hp := relative_source_bound hζ v x h S Δ hμ hfloor hρ hx hh z hz hΔ
  have hb := sqrt_sandwich_strictAccretive hM (hp.trans_lt (by norm_num : (1 : ℝ) / 16 < 1))
  have he : CFC.sqrt (baseSource ζ v x h S) *
      (1 + ((CFC.sqrt (baseSource ζ v x h S))⁻¹ * compressedSource ζ v x h (z, S + Δ) *
        (CFC.sqrt (baseSource ζ v x h S))⁻¹ - 1)) * CFC.sqrt (baseSource ζ v x h S) =
        compressedSource ζ v x h (z, S + Δ) := by
    rw [← add_sub_assoc, add_sub_cancel_left]
    simp only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]
  rwa [he] at hb

theorem compressedDensity_strictAccretive {ζ : ℝ} (hζ : 0 < ζ) (v : ι → n → ℂ)
    {S Δ : Matrix (n ⊕ n) (n ⊕ n) ℂ} {μ ρ : ℝ}
    (hμ : 0 < μ) (hfloor : μ • (1 : Matrix (n ⊕ n) (n ⊕ n) ℂ) ≤ S)
    (hΔ : ‖Δ‖ ≤ NumericalRegularity.radius μ ρ ζ) :
    StrictAccretive (compressedDensity v (S + Δ)) := by
  apply compress_strictAccretive (frame v) (frame_isometry v)
  apply density_strictAccretive hfloor
  have hr := NumericalRegularity.radius_le_density μ ρ ζ
  linarith

/-- The principal-root spectral domain for the actual simultaneous complex
coefficient and density perturbation of the fixed-support spin problem. -/
theorem product_spectrum_subset_slitPlane {ζ : ℝ} (hζ : 0 < ζ) (v : ι → n → ℂ) (x h : ι → ℝ)
    (S Δ : Matrix (n ⊕ n) (n ⊕ n) ℂ) {μ ρ : ℝ}
    (hμ : 0 < μ) (hfloor : μ • (1 : Matrix (n ⊕ n) (n ⊕ n) ℂ) ≤ S)
    (hρ : 0 < ρ) (hx : ∀ i, |x i| ≤ 1 - ρ) (hh : ∀ i, |h i| ≤ 2)
    (z : ℂ) (hz : ‖z‖ ≤ NumericalRegularity.radius μ ρ ζ)
    (hΔ : ‖Δ‖ ≤ NumericalRegularity.radius μ ρ ζ) :
    spectrum ℂ (compressedDensity v (S + Δ) * compressedSource ζ v x h (z, S + Δ)) ⊆
      Complex.slitPlane :=
  KSAccretiveProductDomain.product_spectrum_subset_slitPlane
    (compressedDensity_strictAccretive hζ v hμ hfloor hΔ)
    (compressedSource_strictAccretive hζ v x h S Δ hμ hfloor hρ hx hh z hz hΔ)


end NumericalRegularityDomain
end SeamlessKS
