import MatrixSpencer.KSComplexTraceSource
import MatrixSpencer.KSComplexSpinDomain

/-!
# Fixed-support analytic domain of a general trace-and-prepare source

The frame and positivity of the compressed base source are supplied by the
concrete source's support theorem. The perturbation radius depends only on
the density floor and owner margin, not a smallest positive source eigenvalue.
These are analytic support lemmas, not an algorithm endpoint.
-/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSComplexTraceDomain
open KSAccretiveProductDomain

variable {ι n m : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
local instance {k : Type*} [Fintype k] [DecidableEq k] : CStarAlgebra (Matrix k k ℂ) := {}

def compressedDensity (V : Matrix n m ℂ) (S : Matrix n n ℂ) : Matrix m m ℂ :=
  KSSupportSymmetry.compress V S

def compressedSource (V : Matrix n m ℂ) (A : ι → Matrix n n ℂ)
    (x h : ι → ℝ) (p : KSComplexTraceSource.Space n) : Matrix m m ℂ :=
  KSSupportSymmetry.compress V (KSComplexTraceSource.source A x h p)

def baseSource (V : Matrix n m ℂ) (A : ι → Matrix n n ℂ) (x h : ι → ℝ)
    (S : Matrix n n ℂ) : Matrix m m ℂ := compressedSource V A x h (0,S)

/-- Exact whitening is a proof device only. -/
def whitener (V : Matrix n m ℂ) (A : ι → Matrix n n ℂ) (x h : ι → ℝ)
    (S : Matrix n n ℂ) : Matrix m n ℂ :=
  (CFC.sqrt (baseSource V A x h S))⁻¹ * Vᴴ

theorem whitener_congruence (V : Matrix n m ℂ) (A : ι → Matrix n n ℂ)
    (x h : ι → ℝ) (S X : Matrix n n ℂ) :
    whitener V A x h S * X * (whitener V A x h S)ᴴ =
      (CFC.sqrt (baseSource V A x h S))⁻¹ *
        KSSupportSymmetry.compress V X * (CFC.sqrt (baseSource V A x h S))⁻¹ := by
  have hs := ((CFC.sqrt_nonneg (baseSource V A x h S)).posSemidef.isHermitian.inv).eq
  simp only [whitener, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    hs, KSSupportSymmetry.compress, Matrix.mul_assoc]

theorem whitener_normalizes (V : Matrix n m ℂ) (A : ι → Matrix n n ℂ)
    (x h : ι → ℝ) (S : Matrix n n ℂ)
    (hbase : (baseSource V A x h S).PosDef) :
    whitener V A x h S * KSComplexTraceSource.source A x h (0,S) *
      (whitener V A x h S)ᴴ = 1 := by
  rw [whitener_congruence]
  change (CFC.sqrt (baseSource V A x h S))⁻¹ * baseSource V A x h S *
    (CFC.sqrt (baseSource V A x h S))⁻¹ = 1
  have hu := (CFC.sqrt (baseSource V A x h S)).isUnit_iff_isUnit_det.mp
    hbase.posDef_sqrt.isUnit
  conv_lhs => lhs; rhs; rw [← CFC.sqrt_mul_sqrt_self _ hbase.posSemidef.nonneg]
  rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul,
    Matrix.mul_nonsing_inv _ hu]

theorem relative_source_bound (V : Matrix n m ℂ) (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) (x h : ι → ℝ) (S Δ : Matrix n n ℂ)
    (hbase : (baseSource V A x h S).PosDef) {μ ρ : ℝ}
    (hμ : 0 < μ) (hfloor : μ • (1 : Matrix n n ℂ) ≤ S)
    (hρ : 0 < ρ) (hx : ∀ i, |x i| ≤ 1 - ρ) (hh : ∀ i, |h i| ≤ 2)
    (z : ℂ) (hz : ‖z‖ ≤ KSComplexPerturbationRadius.radius μ ρ)
    (hΔ : ‖Δ‖ ≤ KSComplexPerturbationRadius.radius μ ρ) :
    ‖(CFC.sqrt (baseSource V A x h S))⁻¹ * compressedSource V A x h (z,S+Δ) *
      (CFC.sqrt (baseSource V A x h S))⁻¹ - 1‖ ≤ 1 / 16 := by
  have hp := KSComplexTraceSource.whitened_source_perturbation A hA x h S Δ
    hμ hfloor hρ hx hh (whitener V A x h S) (whitener_normalizes V A x h S hbase)
    z hz hΔ
  simpa only [whitener_congruence, compressedSource] using hp

theorem compressedSource_strictAccretive (V : Matrix n m ℂ) (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) (x h : ι → ℝ) (S Δ : Matrix n n ℂ)
    (hbase : (baseSource V A x h S).PosDef) {μ ρ : ℝ}
    (hμ : 0 < μ) (hfloor : μ • (1 : Matrix n n ℂ) ≤ S)
    (hρ : 0 < ρ) (hx : ∀ i, |x i| ≤ 1 - ρ) (hh : ∀ i, |h i| ≤ 2)
    (z : ℂ) (hz : ‖z‖ ≤ KSComplexPerturbationRadius.radius μ ρ)
    (hΔ : ‖Δ‖ ≤ KSComplexPerturbationRadius.radius μ ρ) :
    StrictAccretive (compressedSource V A x h (z,S+Δ)) := by
  have hu := (CFC.sqrt (baseSource V A x h S)).isUnit_iff_isUnit_det.mp
    hbase.posDef_sqrt.isUnit
  have hp := relative_source_bound V A hA x h S Δ hbase hμ hfloor hρ hx hh z hz hΔ
  have hb := sqrt_sandwich_strictAccretive hbase
    (hp.trans_lt (by norm_num : (1 : ℝ) / 16 < 1))
  have he : CFC.sqrt (baseSource V A x h S) *
      (1 + ((CFC.sqrt (baseSource V A x h S))⁻¹ * compressedSource V A x h (z,S+Δ) *
        (CFC.sqrt (baseSource V A x h S))⁻¹ - 1)) * CFC.sqrt (baseSource V A x h S) =
        compressedSource V A x h (z,S+Δ) := by
    rw [← add_sub_assoc, add_sub_cancel_left]
    simp only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]
  rwa [he] at hb

theorem compressedDensity_strictAccretive (V : Matrix n m ℂ) (hV : Vᴴ * V = 1)
    {S Δ : Matrix n n ℂ} {μ ρ : ℝ}
    (hμ : 0 < μ) (hfloor : μ • (1 : Matrix n n ℂ) ≤ S)
    (hΔ : ‖Δ‖ ≤ KSComplexPerturbationRadius.radius μ ρ) :
    StrictAccretive (compressedDensity V (S+Δ)) := by
  apply KSComplexSpinDomain.compress_strictAccretive V hV
  apply KSComplexSpinDomain.density_strictAccretive hfloor
  have hr := KSComplexPerturbationRadius.radius_le_density μ ρ
  linarith

theorem product_spectrum_subset_slitPlane (V : Matrix n m ℂ) (hV : Vᴴ * V = 1)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (x h : ι → ℝ) (S Δ : Matrix n n ℂ)
    (hbase : (baseSource V A x h S).PosDef) {μ ρ : ℝ}
    (hμ : 0 < μ) (hfloor : μ • (1 : Matrix n n ℂ) ≤ S)
    (hρ : 0 < ρ) (hx : ∀ i, |x i| ≤ 1 - ρ) (hh : ∀ i, |h i| ≤ 2)
    (z : ℂ) (hz : ‖z‖ ≤ KSComplexPerturbationRadius.radius μ ρ)
    (hΔ : ‖Δ‖ ≤ KSComplexPerturbationRadius.radius μ ρ) :
    spectrum ℂ (compressedDensity V (S+Δ) * compressedSource V A x h (z,S+Δ)) ⊆
      Complex.slitPlane :=
  KSAccretiveProductDomain.product_spectrum_subset_slitPlane
    (compressedDensity_strictAccretive V hV hμ hfloor hΔ)
    (compressedSource_strictAccretive V A hA x h S Δ hbase hμ hfloor hρ hx hh z hz hΔ)

end MatrixSpencer.KSComplexTraceDomain
