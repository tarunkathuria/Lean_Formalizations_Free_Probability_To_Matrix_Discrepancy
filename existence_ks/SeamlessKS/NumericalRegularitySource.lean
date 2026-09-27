import SeamlessKS.NumericalRegularityOwner
import MatrixSpencer.KSComplexSpinSource

/-! The new smooth matrix source and its gap-free complex relative perturbation. -/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
noncomputable section
namespace SeamlessKS
namespace NumericalRegularitySource
open MatrixSpencer

variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
local instance {k : Type*} [Fintype k] [DecidableEq k] : CStarAlgebra (Matrix k k ℂ) := {}

abbrev Space (n : Type*) := KSComplexSpinSource.Space n
abbrev atom (v : ι → n → ℂ) (i : ι) := KSComplexSpinSource.atom v i

/-- The actual smooth source, on joint complex time/density coordinates. -/
def source (ζ : ℝ) (v : ι → n → ℂ) (x h : ι → ℝ) (p : Space n) : Matrix (n ⊕ n) (n ⊕ n) ℂ :=
  ∑ i, (Source.complexWeight 64 ζ ((x i : ℂ) + p.1 * (h i : ℂ)) *
    Matrix.trace (atom v i * p.2)) • atom v i

theorem source_real {ζ : ℝ} (hζ : 0 < ζ) (v : ι → n → ℂ) (x h : ι → ℝ)
    (t : ℝ) (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) :
    source ζ v x h ((t : ℂ), S) =
      covarianceSource (KSSpinSource.family (fun i => KSRankOne.atom (v i)))
        (KSSpinSource.coefficientCovariance (fun i => Source.weight 64 ζ (x i + t * h i))) S := by
  rw [KSSpinSource.source_eq_tracePrepare]
  unfold source
  apply Finset.sum_congr rfl
  intro i _
  rw [← Complex.ofReal_mul, ← Complex.ofReal_add, Source.complexWeight_real hζ]
  rfl

theorem contDiffAt_source {ζ : ℝ} (hζ : 0 < ζ) (v : ι → n → ℂ) (x h : ι → ℝ)
    {p : Space n} (hp : ∀ i, |((x i : ℂ) + p.1 * (h i : ℂ)).im| < ζ) :
    ContDiffAt ℂ ∞ (source ζ v x h) p := by
  apply ContDiffAt.sum
  intro i _
  have harg : ContDiffAt ℂ ∞ (fun q : Space n => (x i : ℂ) + q.1 * (h i : ℂ)) p :=
    contDiffAt_const.add (contDiffAt_fst.mul contDiffAt_const)
  have ho := (Source.complexWeight_analyticAt hζ 64 (hp i)).contDiffAt.comp p harg
  have ht : ContDiffAt ℂ ∞ (fun q : Space n => Matrix.trace (atom v i * q.2)) p :=
    (KSComplexSpinSource.traceCLM (n := n ⊕ n)).contDiff.contDiffAt.comp p
      (contDiffAt_const.mul contDiffAt_snd)
  exact (ho.mul ht).smul contDiffAt_const

theorem source_shift (ζ : ℝ) (v : ι → n → ℂ) (x h : ι → ℝ) (t : ℝ) (z : ℂ)
    (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) :
    source ζ v x h ((t : ℂ) + z, S) = source ζ v (fun i => x i + t * h i) h (z, S) := by
  apply Finset.sum_congr rfl
  intro i _
  congr 2
  congr 1
  simp only [Complex.ofReal_add, Complex.ofReal_mul]
  ring

def basePiece (ζ : ℝ) (v : ι → n → ℂ) (x : ι → ℝ)
    (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) (i : ι) : Matrix (n ⊕ n) (n ⊕ n) ℂ :=
  (Source.weight 64 ζ (x i) * realTrace (atom v i * S)) • atom v i

theorem basePiece_posSemidef (ζ : ℝ) (v : ι → n → ℂ) (x : ι → ℝ)
    {S : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hS : S.PosSemidef)
    {ρ : ℝ} (hρ : 0 < ρ) (hx : ∀ i, |x i| ≤ 1 - ρ) (i : ι) :
    (basePiece ζ v x S i).PosSemidef := by
  apply (KSComplexSpinSource.atom_posSemidef v i).smul
  exact mul_nonneg (Source.weight_nonneg (by norm_num) (by have hi := hx i; linarith))
    (realTrace_mul_nonneg (KSComplexSpinSource.atom_posSemidef v i) hS)

theorem source_zero_eq_pieces {ζ : ℝ} (hζ : 0 < ζ) (v : ι → n → ℂ) (x h : ι → ℝ)
    {S : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hS : S.IsHermitian) :
    source ζ v x h (0, S) = ∑ i, basePiece ζ v x S i := by
  have he := source_real hζ v x h 0 S
  rw [KSSpinSource.source_eq_tracePrepare_real _ _ hS] at he
  simpa only [Complex.ofReal_zero, zero_mul, add_zero, basePiece, atom, KSComplexSpinSource.atom] using he

theorem source_perturb_eq {ζ : ℝ} (v : ι → n → ℂ) (x h : ι → ℝ)
    (S Δ : Matrix (n ⊕ n) (n ⊕ n) ℂ) {μ ρ : ℝ}
    (hμ : 0 < μ) (hfloor : μ • (1 : Matrix (n ⊕ n) (n ⊕ n) ℂ) ≤ S)
    (hρ : 0 < ρ) (hx : ∀ i, |x i| ≤ 1 - ρ) (z : ℂ) :
    source ζ v x h (z, S + Δ) =
      ∑ i, (1 + NumericalRegularity.combinedError 64 ζ (x i) (z * (h i : ℂ))
        (atom v i) S Δ) • basePiece ζ v x S i := by
  apply Finset.sum_congr rfl
  intro i _
  have he := NumericalRegularity.coefficient_eq_base_mul_error (ζ := ζ) (atom v i) S Δ
    (KSComplexSpinSource.atom_posSemidef v i) (by norm_num : (0 : ℝ) < 64)
    hμ hfloor hρ (hx i) (z * (h i : ℂ))
  change (Source.complexWeight 64 ζ ((x i : ℂ) + z * (h i : ℂ)) *
    Matrix.trace (atom v i * (S + Δ))) • atom v i = _
  rw [he]
  ext a b
  simp only [basePiece, Matrix.smul_apply, smul_eq_mul, Complex.real_smul]
  ring

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- Any exact whitener sees a relative perturbation at most `1/16`.
There is no quantitative source-floor hypothesis. -/
theorem whitened_source_perturbation {ζ : ℝ} (hζ : 0 < ζ) (v : ι → n → ℂ) (x h : ι → ℝ)
    (S Δ : Matrix (n ⊕ n) (n ⊕ n) ℂ) {μ ρ : ℝ}
    (hμ : 0 < μ) (hfloor : μ • (1 : Matrix (n ⊕ n) (n ⊕ n) ℂ) ≤ S)
    (hρ : 0 < ρ) (hx : ∀ i, |x i| ≤ 1 - ρ) (hh : ∀ i, |h i| ≤ 2)
    (W : Matrix m (n ⊕ n) ℂ) (hW : W * source ζ v x h (0, S) * Wᴴ = 1)
    (z : ℂ) (hz : ‖z‖ ≤ NumericalRegularity.radius μ ρ ζ)
    (hΔ : ‖Δ‖ ≤ NumericalRegularity.radius μ ρ ζ) :
    ‖W * source ζ v x h (z, S + Δ) * Wᴴ - 1‖ ≤ 1 / 16 := by
  have hS := KSComplexOwnerPerturbation.density_posSemidef hμ hfloor
  rw [source_zero_eq_pieces hζ v x h hS.isHermitian] at hW
  rw [source_perturb_eq v x h S Δ hμ hfloor hρ hx z]
  apply KSComplexRelativeSource.whitened_source_perturbation
    (basePiece ζ v x S) (basePiece_posSemidef ζ v x hS hρ hx) W hW _ (by norm_num)
  intro i
  exact NumericalRegularity.combinedError_le (atom v i) S Δ
    (KSComplexSpinSource.atom_posSemidef v i) (by norm_num) hμ hfloor hρ hζ (hx i) (hh i) z hz hΔ

end NumericalRegularitySource
end SeamlessKS
