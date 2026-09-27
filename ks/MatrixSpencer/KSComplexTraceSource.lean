import MatrixSpencer.KSComplexSpinSource
import MatrixSpencer.KSComplexPerturbationRadius

/-!
# Complex trace-and-prepare sources for arbitrary PSD atoms

This is the common analytic extension for the eighth-cube independent source
and the grouped PSD source used by the thin-tree algorithm. It does not split
an atom's coefficient into independent signs. Complex variables occur only in
analytic error-bound proofs.
-/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
noncomputable section
namespace MatrixSpencer.KSComplexTraceSource

variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
local instance {k : Type*} [Fintype k] [DecidableEq k] : CStarAlgebra (Matrix k k ℂ) := {}

abbrev Space (n : Type*) := ℂ × Matrix n n ℂ

def traceCLM : Matrix n n ℂ →L[ℂ] ℂ :=
  (Matrix.traceLinearMap n ℂ ℂ).toContinuousLinearMap

def source (A : ι → Matrix n n ℂ) (x h : ι → ℝ) (p : Space n) : Matrix n n ℂ :=
  ∑ i, ((64 : ℂ) * (1 - ((x i : ℂ) + p.1 * (h i : ℂ)) ^ 2) *
    Matrix.trace (A i * p.2)) • A i

theorem contDiff_source (A : ι → Matrix n n ℂ) (x h : ι → ℝ) :
    ContDiff ℂ ∞ (source A x h) := by
  apply ContDiff.sum
  intro i _
  apply ContDiff.smul _ contDiff_const
  apply ContDiff.mul
  · exact contDiff_const.mul (contDiff_const.sub
      ((contDiff_const.add (contDiff_fst.mul contDiff_const)).pow 2))
  · exact (traceCLM (n := n)).contDiff.comp (contDiff_const.mul contDiff_snd)

/-- Recenter the actual coefficient polynomial at a real point on the walk line. -/
theorem source_shift (A : ι → Matrix n n ℂ) (x h : ι → ℝ) (t : ℝ) (z : ℂ)
    (S : Matrix n n ℂ) :
    source A x h ((t : ℂ) + z, S) =
      source A (fun i => x i + t * h i) h (z, S) := by
  apply Finset.sum_congr rfl
  intro i _
  congr 2
  simp only [Complex.ofReal_add, Complex.ofReal_mul]
  ring

def basePiece (A : ι → Matrix n n ℂ) (x : ι → ℝ)
    (S : Matrix n n ℂ) (i : ι) : Matrix n n ℂ :=
  (KSComplexOwnerPerturbation.baseOwner 64 (x i) * realTrace (A i * S)) • A i

theorem basePiece_posSemidef (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) (x : ι → ℝ)
    {S : Matrix n n ℂ} (hS : S.PosSemidef)
    {ρ : ℝ} (hρ : 0 < ρ) (hx : ∀ i, |x i| ≤ 1 - ρ) (i : ι) :
    (basePiece A x S i).PosSemidef := by
  have ho := KSComplexOwnerPerturbation.quadratic_owner_lower hρ (hx i)
  apply (hA i).smul
  exact mul_nonneg (mul_nonneg (by norm_num) (hρ.le.trans ho))
    (realTrace_mul_nonneg (hA i) hS)

theorem source_zero_eq_pieces (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) (x h : ι → ℝ)
    {S : Matrix n n ℂ} (hS : S.IsHermitian) :
    source A x h (0, S) = ∑ i, basePiece A x S i := by
  apply Finset.sum_congr rfl
  intro i _
  rw [KSComplexOwnerPerturbation.trace_pairing_real _ S (hA i).isHermitian hS]
  ext a b
  simp only [basePiece, KSComplexOwnerPerturbation.baseOwner,
    Matrix.smul_apply, smul_eq_mul, Complex.real_smul, zero_mul, add_zero,
    Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_pow,
    Complex.ofReal_ofNat]

/-- Exact factorization of the actual polynomial source under simultaneous
complex coefficient and density perturbations. -/
theorem source_perturb_eq (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) (x h : ι → ℝ)
    (S Δ : Matrix n n ℂ) {μ ρ : ℝ}
    (hμ : 0 < μ) (hfloor : μ • (1 : Matrix n n ℂ) ≤ S)
    (hρ : 0 < ρ) (hx : ∀ i, |x i| ≤ 1 - ρ) (z : ℂ) :
    source A x h (z, S + Δ) =
      ∑ i, (1 + KSComplexOwnerPerturbation.combinedError (x i) (z * (h i : ℂ))
        (A i) S Δ) • basePiece A x S i := by
  apply Finset.sum_congr rfl
  intro i _
  have he := KSComplexOwnerPerturbation.coefficient_eq_base_mul_error 64
    (A i) S Δ (hA i) hμ hfloor hρ (hx i) (z * (h i : ℂ))
  change (KSComplexOwnerPerturbation.owner 64 (x i) (z * (h i : ℂ)) *
    Matrix.trace (A i * (S + Δ))) • A i = _
  rw [he]
  ext a b
  simp only [basePiece, Matrix.smul_apply, smul_eq_mul, Complex.real_smul]
  ring

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- The actual trace source fits the fixed relative 1/16 ball after any
exact compression and whitening of its base value. No source spectral
gap enters the perturbation radius. -/
theorem whitened_source_perturbation (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) (x h : ι → ℝ)
    (S Δ : Matrix n n ℂ) {μ ρ : ℝ}
    (hμ : 0 < μ) (hfloor : μ • (1 : Matrix n n ℂ) ≤ S)
    (hρ : 0 < ρ) (hx : ∀ i, |x i| ≤ 1 - ρ) (hh : ∀ i, |h i| ≤ 2)
    (W : Matrix m n ℂ) (hW : W * source A x h (0, S) * Wᴴ = 1)
    (z : ℂ) (hz : ‖z‖ ≤ KSComplexPerturbationRadius.radius μ ρ)
    (hΔ : ‖Δ‖ ≤ KSComplexPerturbationRadius.radius μ ρ) :
    ‖W * source A x h (z, S + Δ) * Wᴴ - 1‖ ≤ 1 / 16 := by
  have hS := KSComplexOwnerPerturbation.density_posSemidef hμ hfloor
  rw [source_zero_eq_pieces A hA x h hS.isHermitian] at hW
  rw [source_perturb_eq A hA x h S Δ hμ hfloor hρ hx z]
  apply KSComplexRelativeSource.whitened_source_perturbation
    (basePiece A x S) (basePiece_posSemidef A hA x hS hρ hx) W hW _ (by norm_num)
  intro i
  have hp := KSComplexPerturbationRadius.radius_pos hμ hρ
  have hz' : ‖z * (h i : ℂ)‖ ≤ 2 * KSComplexPerturbationRadius.radius μ ρ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc _ ≤ KSComplexPerturbationRadius.radius μ ρ * 2 :=
        mul_le_mul hz (hh i) (abs_nonneg _) hp.le
      _ = _ := by ring
  exact (KSComplexOwnerPerturbation.combinedError_bound (A i) S Δ
    (hA i) hμ hfloor hρ (hx i) (by positivity) (z * (h i : ℂ)) hz' hΔ).trans
    (KSComplexPerturbationRadius.combinedCap_le hμ hρ)

end MatrixSpencer.KSComplexTraceSource
