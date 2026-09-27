import MatrixSpencer.KSSpinSource
import MatrixSpencer.KSComplexPerturbationRadius

/-!
# The actual spin source on complex coefficient and density coordinates

This polynomial extension agrees with the original covariance source at
every real time, including on arbitrary complex density matrices. The
complex parameter is used in the analytic proof; it is not an evaluation
point of the numerical walk.
-/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
noncomputable section
namespace MatrixSpencer.KSComplexSpinSource

variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
local instance {k : Type*} [Fintype k] [DecidableEq k] : CStarAlgebra (Matrix k k ℂ) := {}

abbrev Space (n : Type*) := ℂ × Matrix (n ⊕ n) (n ⊕ n) ℂ

def traceCLM : Matrix n n ℂ →L[ℂ] ℂ :=
  (Matrix.traceLinearMap n ℂ ℂ).toContinuousLinearMap

def atom (v : ι → n → ℂ) (i : ι) : Matrix (n ⊕ n) (n ⊕ n) ℂ :=
  KSSpinSource.doubled (KSRankOne.atom (v i))

theorem atom_posSemidef (v : ι → n → ℂ) (i : ι) : (atom v i).PosSemidef :=
  KSSpinSource.doubled_posSemidef (KSRankOne.atom_posSemidef (v i))

def source (v : ι → n → ℂ) (x h : ι → ℝ) (p : Space n) : Matrix (n ⊕ n) (n ⊕ n) ℂ :=
  ∑ i, ((64 : ℂ) * (1 - ((x i : ℂ) + p.1 * (h i : ℂ)) ^ 2) *
    Matrix.trace (atom v i * p.2)) • atom v i

theorem source_real (v : ι → n → ℂ) (x h : ι → ℝ) (t : ℝ)
    (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) :
    source v x h ((t : ℂ), S) =
      covarianceSource (KSSpinSource.family (fun i => KSRankOne.atom (v i)))
        (KSSpinSource.coefficientCovariance (fun i => 64 * (1 - (x i + t * h i) ^ 2))) S := by
  rw [KSSpinSource.source_eq_tracePrepare]
  simp only [source, atom, Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_sub,
    Complex.ofReal_one, Complex.ofReal_pow, Complex.ofReal_add]

theorem contDiff_source (v : ι → n → ℂ) (x h : ι → ℝ) :
    ContDiff ℂ ∞ (source v x h) := by
  apply ContDiff.sum
  intro i _
  apply ContDiff.smul _ contDiff_const
  apply ContDiff.mul
  · exact contDiff_const.mul (contDiff_const.sub
      ((contDiff_const.add (contDiff_fst.mul contDiff_const)).pow 2))
  · exact (traceCLM (n := n ⊕ n)).contDiff.comp (contDiff_const.mul contDiff_snd)

/-- Recenter the actual coefficient polynomial at a real point on the walk line. -/
theorem source_shift (v : ι → n → ℂ) (x h : ι → ℝ) (t : ℝ) (z : ℂ)
    (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) :
    source v x h ((t : ℂ) + z, S) =
      source v (fun i => x i + t * h i) h (z, S) := by
  apply Finset.sum_congr rfl
  intro i _
  congr 2
  simp only [Complex.ofReal_add, Complex.ofReal_mul]
  ring

def basePiece (v : ι → n → ℂ) (x : ι → ℝ)
    (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) (i : ι) : Matrix (n ⊕ n) (n ⊕ n) ℂ :=
  (KSComplexOwnerPerturbation.baseOwner 64 (x i) * realTrace (atom v i * S)) • atom v i

theorem basePiece_posSemidef (v : ι → n → ℂ) (x : ι → ℝ)
    {S : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hS : S.PosSemidef)
    {ρ : ℝ} (hρ : 0 < ρ) (hx : ∀ i, |x i| ≤ 1 - ρ) (i : ι) :
    (basePiece v x S i).PosSemidef := by
  have ho := KSComplexOwnerPerturbation.quadratic_owner_lower hρ (hx i)
  apply (atom_posSemidef v i).smul
  exact mul_nonneg (mul_nonneg (by norm_num) (hρ.le.trans ho))
    (realTrace_mul_nonneg (atom_posSemidef v i) hS)

theorem source_zero_eq_pieces (v : ι → n → ℂ) (x h : ι → ℝ)
    {S : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hS : S.IsHermitian) :
    source v x h (0, S) = ∑ i, basePiece v x S i := by
  have he := source_real v x h 0 S
  rw [KSSpinSource.source_eq_tracePrepare_real _ _ hS] at he
  simpa only [Complex.ofReal_zero, zero_mul, add_zero, basePiece,
    KSComplexOwnerPerturbation.baseOwner, atom] using he

/-- Exact factorization of the actual polynomial source under simultaneous
complex coefficient and density perturbations. -/
theorem source_perturb_eq (v : ι → n → ℂ) (x h : ι → ℝ)
    (S Δ : Matrix (n ⊕ n) (n ⊕ n) ℂ) {μ ρ : ℝ}
    (hμ : 0 < μ) (hfloor : μ • (1 : Matrix (n ⊕ n) (n ⊕ n) ℂ) ≤ S)
    (hρ : 0 < ρ) (hx : ∀ i, |x i| ≤ 1 - ρ) (z : ℂ) :
    source v x h (z, S + Δ) =
      ∑ i, (1 + KSComplexOwnerPerturbation.combinedError (x i) (z * (h i : ℂ))
        (atom v i) S Δ) • basePiece v x S i := by
  apply Finset.sum_congr rfl
  intro i _
  have he := KSComplexOwnerPerturbation.coefficient_eq_base_mul_error 64
    (atom v i) S Δ (atom_posSemidef v i) hμ hfloor hρ (hx i) (z * (h i : ℂ))
  change (KSComplexOwnerPerturbation.owner 64 (x i) (z * (h i : ℂ)) *
    Matrix.trace (atom v i * (S + Δ))) • atom v i = _
  rw [he]
  ext a b
  simp only [basePiece, Matrix.smul_apply, smul_eq_mul, Complex.real_smul]
  ring

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- The actual spin source fits the fixed relative 1/16 ball after any
exact compression and whitening of its base value. No source spectral
gap enters the perturbation radius. -/
theorem whitened_source_perturbation (v : ι → n → ℂ) (x h : ι → ℝ)
    (S Δ : Matrix (n ⊕ n) (n ⊕ n) ℂ) {μ ρ : ℝ}
    (hμ : 0 < μ) (hfloor : μ • (1 : Matrix (n ⊕ n) (n ⊕ n) ℂ) ≤ S)
    (hρ : 0 < ρ) (hx : ∀ i, |x i| ≤ 1 - ρ) (hh : ∀ i, |h i| ≤ 2)
    (W : Matrix m (n ⊕ n) ℂ) (hW : W * source v x h (0, S) * Wᴴ = 1)
    (z : ℂ) (hz : ‖z‖ ≤ KSComplexPerturbationRadius.radius μ ρ)
    (hΔ : ‖Δ‖ ≤ KSComplexPerturbationRadius.radius μ ρ) :
    ‖W * source v x h (z, S + Δ) * Wᴴ - 1‖ ≤ 1 / 16 := by
  have hS := KSComplexOwnerPerturbation.density_posSemidef hμ hfloor
  rw [source_zero_eq_pieces v x h hS.isHermitian] at hW
  rw [source_perturb_eq v x h S Δ hμ hfloor hρ hx z]
  apply KSComplexRelativeSource.whitened_source_perturbation
    (basePiece v x S) (basePiece_posSemidef v x hS hρ hx) W hW _ (by norm_num)
  intro i
  have hp := KSComplexPerturbationRadius.radius_pos hμ hρ
  have hz' : ‖z * (h i : ℂ)‖ ≤ 2 * KSComplexPerturbationRadius.radius μ ρ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc _ ≤ KSComplexPerturbationRadius.radius μ ρ * 2 :=
        mul_le_mul hz (hh i) (abs_nonneg _) hp.le
      _ = _ := by ring
  exact (KSComplexOwnerPerturbation.combinedError_bound (atom v i) S Δ
    (atom_posSemidef v i) hμ hfloor hρ (hx i) (by positivity) (z * (h i : ℂ)) hz' hΔ).trans
    (KSComplexPerturbationRadius.combinedCap_le hμ hρ)

end MatrixSpencer.KSComplexSpinSource
