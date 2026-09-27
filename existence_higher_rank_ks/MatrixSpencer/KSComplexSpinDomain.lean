import MatrixSpencer.KSComplexSpinSource
import MatrixSpencer.KSSpinCompression
import MatrixSpencer.KSAccretiveProductDomain

/-!
# The actual compressed spin source stays in the square-root domain

The fixed support is the support of the original physical Pauli family.
Whitening its positive base source is used only in the analytic proof.
The perturbation radius depends on the density floor and the coefficient
margin, with no lower bound on the source's positive eigenvalues. Both
perturbations may be complex and non-Hermitian. Empty support is allowed.
-/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSComplexSpinDomain

variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
local instance {k : Type*} [Fintype k] [DecidableEq k] : CStarAlgebra (Matrix k k ℂ) := {}

open KSAccretiveProductDomain

theorem posDef_of_floor {S : Matrix n n ℂ} {μ : ℝ} (hμ : 0 < μ)
    (hfloor : μ • (1 : Matrix n n ℂ) ≤ S) : S.PosDef := by
  simpa only [add_sub_cancel] using
    (Matrix.PosDef.one.smul hμ).add_posSemidef (Matrix.le_iff.mp hfloor)

theorem quadratic_floor {S : Matrix n n ℂ} {μ : ℝ}
    (hfloor : μ • (1 : Matrix n n ℂ) ≤ S) (v : n → ℂ) :
    μ * ‖(WithLp.toLp 2 v : EuclideanSpace ℂ n)‖ ^ 2 ≤
      (star v ⬝ᵥ (S *ᵥ v)).re := by
  have hq := (Matrix.le_iff.mp hfloor).re_dotProduct_nonneg v
  have hs : (star v ⬝ᵥ v).re =
      ‖(WithLp.toLp 2 v : EuclideanSpace ℂ n)‖ ^ 2 := by
    have he : inner ℂ (WithLp.toLp 2 v : EuclideanSpace ℂ n) (WithLp.toLp 2 v) =
        star v ⬝ᵥ v := by
      rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
      rfl
    rw [← he]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) _
  change 0 ≤ (star v ⬝ᵥ ((S - μ • (1 : Matrix n n ℂ)) *ᵥ v)).re at hq
  simpa only [sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub, dotProduct_smul,
    Complex.sub_re, Complex.smul_re, smul_eq_mul, hs, sub_nonneg] using hq

/-- A physical density floor controls arbitrary complex additive errors. -/
theorem density_strictAccretive {S Δ : Matrix n n ℂ} {μ : ℝ}
    (hfloor : μ • (1 : Matrix n n ℂ) ≤ S) (hΔ : ‖Δ‖ < μ) :
    StrictAccretive (S + Δ) := by
  intro v hv
  have hw : (WithLp.toLp 2 v : EuclideanSpace ℂ n) ≠ 0 := by
    intro hz
    exact hv (congrArg WithLp.ofLp hz)
  have hn := sq_pos_of_pos (norm_pos_iff.mpr hw)
  have hq := quadratic_floor hfloor v
  have he := (abs_le.mp (abs_quadratic_le Δ v)).1
  simp only [add_mulVec, dotProduct_add, Complex.add_re]
  nlinarith [mul_lt_mul_of_pos_right hΔ hn]

variable {m : Type*} [Fintype m] [DecidableEq m]

omit [DecidableEq n] in
/-- Rectangular isometric compression preserves strict accretivity, even
when the compressed coordinate type is empty. -/
theorem compress_strictAccretive (V : Matrix n m ℂ) (hV : Vᴴ * V = 1)
    {S : Matrix n n ℂ} (hS : StrictAccretive S) :
    StrictAccretive (KSSupportSymmetry.compress V S) := by
  intro v hv
  have hw : V *ᵥ v ≠ 0 := by
    intro hz
    have he : Vᴴ *ᵥ (V *ᵥ v) = v := by rw [mulVec_mulVec, hV, one_mulVec]
    rw [hz, mulVec_zero] at he
    exact hv he.symm
  simpa only [star_mulVec, dotProduct_mulVec, vecMul_vecMul,
    KSSupportSymmetry.compress] using hS (V *ᵥ v) hw

abbrev Support (v : ι → n → ℂ) :=
  KSSpinCompression.supportIndex (fun i => KSRankOne.atom (v i))

def frame (v : ι → n → ℂ) : Matrix (n ⊕ n) (Support v) ℂ :=
  KSSpinCompression.embedding (fun i => KSRankOne.atom (v i))

theorem frame_isometry (v : ι → n → ℂ) : (frame v)ᴴ * frame v = 1 :=
  KSSpinCompression.embedding_isometry _

def compressedDensity (v : ι → n → ℂ) (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) :
    Matrix (Support v) (Support v) ℂ := KSSupportSymmetry.compress (frame v) S

def compressedSource (v : ι → n → ℂ) (x h : ι → ℝ) (p : KSComplexSpinSource.Space n) :
    Matrix (Support v) (Support v) ℂ :=
  KSSupportSymmetry.compress (frame v) (KSComplexSpinSource.source v x h p)

def baseSource (v : ι → n → ℂ) (x h : ι → ℝ)
    (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) : Matrix (Support v) (Support v) ℂ :=
  compressedSource v x h (0, S)

theorem baseSource_posDef (v : ι → n → ℂ) (x h : ι → ℝ)
    {S : Matrix (n ⊕ n) (n ⊕ n) ℂ} {μ ρ : ℝ}
    (hμ : 0 < μ) (hfloor : μ • (1 : Matrix (n ⊕ n) (n ⊕ n) ℂ) ≤ S)
    (hρ : 0 < ρ) (hx : ∀ i, |x i| ≤ 1 - ρ) : (baseSource v x h S).PosDef := by
  have hc : ∀ i, 0 < 64 * (1 - (x i) ^ 2) := by
    intro i
    have ho := KSComplexOwnerPerturbation.quadratic_owner_lower hρ (hx i)
    exact mul_pos (by norm_num) (hρ.trans_le ho)
  have hp := KSSpinCompression.compressed_source_posDef v hc (posDef_of_floor hμ hfloor)
  change (KSSupportSymmetry.compress (frame v) (KSComplexSpinSource.source v x h (0, S))).PosDef
  rw [← Complex.ofReal_zero, KSComplexSpinSource.source_real]
  simpa only [zero_mul, add_zero, KSSupportSymmetry.compress, frame,
    KSSpinCompression.embedding, covarianceCompressedSource] using hp

/-- The exact fixed-support whitener used solely to prove the domain bound. -/
def whitener (v : ι → n → ℂ) (x h : ι → ℝ)
    (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) : Matrix (Support v) (n ⊕ n) ℂ :=
  (CFC.sqrt (baseSource v x h S))⁻¹ * (frame v)ᴴ

omit [DecidableEq ι] in
theorem whitener_congruence (v : ι → n → ℂ) (x h : ι → ℝ)
    (S X : Matrix (n ⊕ n) (n ⊕ n) ℂ) :
    whitener v x h S * X * (whitener v x h S)ᴴ =
      (CFC.sqrt (baseSource v x h S))⁻¹ *
        KSSupportSymmetry.compress (frame v) X * (CFC.sqrt (baseSource v x h S))⁻¹ := by
  have hs := ((CFC.sqrt_nonneg (baseSource v x h S)).posSemidef.isHermitian.inv).eq
  simp only [whitener, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    hs, KSSupportSymmetry.compress, Matrix.mul_assoc]

theorem whitener_normalizes (v : ι → n → ℂ) (x h : ι → ℝ)
    {S : Matrix (n ⊕ n) (n ⊕ n) ℂ} {μ ρ : ℝ}
    (hμ : 0 < μ) (hfloor : μ • (1 : Matrix (n ⊕ n) (n ⊕ n) ℂ) ≤ S)
    (hρ : 0 < ρ) (hx : ∀ i, |x i| ≤ 1 - ρ) :
    whitener v x h S * KSComplexSpinSource.source v x h (0, S) *
      (whitener v x h S)ᴴ = 1 := by
  rw [whitener_congruence]
  change (CFC.sqrt (baseSource v x h S))⁻¹ * baseSource v x h S *
    (CFC.sqrt (baseSource v x h S))⁻¹ = 1
  have hM := baseSource_posDef v x h hμ hfloor hρ hx
  have hu := (CFC.sqrt (baseSource v x h S)).isUnit_iff_isUnit_det.mp hM.posDef_sqrt.isUnit
  conv_lhs => lhs; rhs; rw [← CFC.sqrt_mul_sqrt_self _ hM.posSemidef.nonneg]
  rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul,
    Matrix.mul_nonsing_inv _ hu]

/-- The actual compressed source lies in the relative `1/16` ball. -/
theorem relative_source_bound (v : ι → n → ℂ) (x h : ι → ℝ)
    (S Δ : Matrix (n ⊕ n) (n ⊕ n) ℂ) {μ ρ : ℝ}
    (hμ : 0 < μ) (hfloor : μ • (1 : Matrix (n ⊕ n) (n ⊕ n) ℂ) ≤ S)
    (hρ : 0 < ρ) (hx : ∀ i, |x i| ≤ 1 - ρ) (hh : ∀ i, |h i| ≤ 2)
    (z : ℂ) (hz : ‖z‖ ≤ KSComplexPerturbationRadius.radius μ ρ)
    (hΔ : ‖Δ‖ ≤ KSComplexPerturbationRadius.radius μ ρ) :
    ‖(CFC.sqrt (baseSource v x h S))⁻¹ * compressedSource v x h (z, S + Δ) *
      (CFC.sqrt (baseSource v x h S))⁻¹ - 1‖ ≤ 1 / 16 := by
  have hp := KSComplexSpinSource.whitened_source_perturbation v x h S Δ hμ hfloor hρ hx hh
    (whitener v x h S) (whitener_normalizes v x h hμ hfloor hρ hx) z hz hΔ
  simpa only [whitener_congruence, compressedSource] using hp

/-- The actual source is accretive throughout the arithmetic-radius ball. -/
theorem compressedSource_strictAccretive (v : ι → n → ℂ) (x h : ι → ℝ)
    (S Δ : Matrix (n ⊕ n) (n ⊕ n) ℂ) {μ ρ : ℝ}
    (hμ : 0 < μ) (hfloor : μ • (1 : Matrix (n ⊕ n) (n ⊕ n) ℂ) ≤ S)
    (hρ : 0 < ρ) (hx : ∀ i, |x i| ≤ 1 - ρ) (hh : ∀ i, |h i| ≤ 2)
    (z : ℂ) (hz : ‖z‖ ≤ KSComplexPerturbationRadius.radius μ ρ)
    (hΔ : ‖Δ‖ ≤ KSComplexPerturbationRadius.radius μ ρ) :
    StrictAccretive (compressedSource v x h (z, S + Δ)) := by
  have hM := baseSource_posDef v x h hμ hfloor hρ hx
  have hu := (CFC.sqrt (baseSource v x h S)).isUnit_iff_isUnit_det.mp hM.posDef_sqrt.isUnit
  have hp := relative_source_bound v x h S Δ hμ hfloor hρ hx hh z hz hΔ
  have hb := sqrt_sandwich_strictAccretive hM (hp.trans_lt (by norm_num : (1 : ℝ) / 16 < 1))
  have he : CFC.sqrt (baseSource v x h S) *
      (1 + ((CFC.sqrt (baseSource v x h S))⁻¹ * compressedSource v x h (z, S + Δ) *
        (CFC.sqrt (baseSource v x h S))⁻¹ - 1)) * CFC.sqrt (baseSource v x h S) =
        compressedSource v x h (z, S + Δ) := by
    rw [← add_sub_assoc, add_sub_cancel_left]
    simp only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]
  rwa [he] at hb

theorem compressedDensity_strictAccretive (v : ι → n → ℂ)
    {S Δ : Matrix (n ⊕ n) (n ⊕ n) ℂ} {μ ρ : ℝ}
    (hμ : 0 < μ) (hfloor : μ • (1 : Matrix (n ⊕ n) (n ⊕ n) ℂ) ≤ S)
    (hΔ : ‖Δ‖ ≤ KSComplexPerturbationRadius.radius μ ρ) :
    StrictAccretive (compressedDensity v (S + Δ)) := by
  apply compress_strictAccretive (frame v) (frame_isometry v)
  apply density_strictAccretive hfloor
  have hr := KSComplexPerturbationRadius.radius_le_density μ ρ
  linarith

/-- The principal-root spectral domain for the actual simultaneous complex
coefficient and density perturbation of the fixed-support spin problem. -/
theorem product_spectrum_subset_slitPlane (v : ι → n → ℂ) (x h : ι → ℝ)
    (S Δ : Matrix (n ⊕ n) (n ⊕ n) ℂ) {μ ρ : ℝ}
    (hμ : 0 < μ) (hfloor : μ • (1 : Matrix (n ⊕ n) (n ⊕ n) ℂ) ≤ S)
    (hρ : 0 < ρ) (hx : ∀ i, |x i| ≤ 1 - ρ) (hh : ∀ i, |h i| ≤ 2)
    (z : ℂ) (hz : ‖z‖ ≤ KSComplexPerturbationRadius.radius μ ρ)
    (hΔ : ‖Δ‖ ≤ KSComplexPerturbationRadius.radius μ ρ) :
    spectrum ℂ (compressedDensity v (S + Δ) * compressedSource v x h (z, S + Δ)) ⊆
      Complex.slitPlane :=
  KSAccretiveProductDomain.product_spectrum_subset_slitPlane
    (compressedDensity_strictAccretive v hμ hfloor hΔ)
    (compressedSource_strictAccretive v x h S Δ hμ hfloor hρ hx hh z hz hΔ)

end MatrixSpencer.KSComplexSpinDomain
