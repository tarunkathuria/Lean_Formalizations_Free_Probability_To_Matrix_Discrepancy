import MatrixSpencer.KSComplexRelativeSource
import MatrixSpencer.TraceSqrtConcavity

/-!
# Complex owner and density perturbations

The density perturbation matrix and owner increment are genuinely complex.
The trace-pairing bound uses only positivity of the unperturbed source piece.
Relative bounds use the density floor and endpoint margin, never a smallest
positive eigenvalue of the source.
-/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSComplexOwnerPerturbation

variable {n : Type*} [Fintype n] [DecidableEq n]
local instance {k : Type*} [Fintype k] [DecidableEq k] : CStarAlgebra (Matrix k k ℂ) := {}

def column (B : Matrix n n ℂ) (j : n) : EuclideanSpace ℂ n :=
  WithLp.toLp 2 (fun i => B i j)

theorem conjugate_diag_inner (B Δ : Matrix n n ℂ) (j : n) :
    (Bᴴ * Δ * B) j j =
      inner ℂ (column B j) (Matrix.toEuclideanCLM (𝕜 := ℂ) Δ (column B j)) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  change (∑ k, (∑ l, star (B l j) * Δ l k) * B k j) =
    ∑ l, star (B l j) * (∑ k, Δ l k * B k j)
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem gram_realTrace (B : Matrix n n ℂ) :
    realTrace (Bᴴ * B) = ∑ j, ‖column B j‖ ^ 2 := by
  unfold realTrace Matrix.trace Matrix.diag
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  have he := congrArg Complex.re (conjugate_diag_inner B 1 j)
  simp only [Matrix.mul_one, map_one, ContinuousLinearMap.one_apply] at he
  change RCLike.re ((Bᴴ * B) j j) = RCLike.re (inner ℂ (column B j) (column B j)) at he
  rwa [inner_self_eq_norm_sq] at he

theorem norm_trace_conjugate_le (B Δ : Matrix n n ℂ) :
    ‖Matrix.trace (Bᴴ * Δ * B)‖ ≤ ‖Δ‖ * realTrace (Bᴴ * B) := by
  rw [gram_realTrace, Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  change ‖(Bᴴ * Δ * B) j j‖ ≤ ‖Δ‖ * ‖column B j‖ ^ 2
  rw [conjugate_diag_inner]
  have hh := norm_inner_le_norm (𝕜 := ℂ) (column B j) (Matrix.toEuclideanCLM (𝕜 := ℂ) Δ (column B j))
  have hop := (Matrix.toEuclideanCLM (𝕜 := ℂ) Δ).le_opNorm (column B j)
  have hmul := mul_le_mul_of_nonneg_left hop (norm_nonneg (column B j))
  change ‖column B j‖ * ‖Matrix.toEuclideanCLM (𝕜 := ℂ) Δ (column B j)‖ ≤
    ‖column B j‖ * (‖Δ‖ * ‖column B j‖) at hmul
  calc
    _ ≤ ‖column B j‖ * (‖Δ‖ * ‖column B j‖) := hh.trans hmul
    _ = _ := by ring


theorem norm_trace_mul_le (P Δ : Matrix n n ℂ) (hP : P.PosSemidef) :
    ‖Matrix.trace (P * Δ)‖ ≤ ‖Δ‖ * realTrace P := by
  have hs := (CFC.sqrt_nonneg P).posSemidef.isHermitian.eq
  have hg : (CFC.sqrt P)ᴴ * CFC.sqrt P = P := by
    rw [hs, CFC.sqrt_mul_sqrt_self P hP.nonneg]
  have ht : Matrix.trace ((CFC.sqrt P)ᴴ * Δ * CFC.sqrt P) = Matrix.trace (P * Δ) := by
    rw [hs, Matrix.trace_mul_cycle, CFC.sqrt_mul_sqrt_self P hP.nonneg]
  have hh := norm_trace_conjugate_le (CFC.sqrt P) Δ
  rwa [ht, hg] at hh

/-- A density floor supplies the relative trace bound without any source
eigenvalue assumption and without commutation between `P` and `S`. -/
theorem relative_trace_error (P S Δ : Matrix n n ℂ) (hP : P.PosSemidef)
    {μ r : ℝ} (hμ : 0 < μ) (hfloor : μ • (1 : Matrix n n ℂ) ≤ S)
    (hΔ : ‖Δ‖ ≤ r) :
    ‖Matrix.trace (P * Δ)‖ ≤ (r / μ) * realTrace (P * S) := by
  have htrace := realTrace_nonneg hP
  have hr : 0 ≤ r := (norm_nonneg Δ).trans hΔ
  have hmono := realTrace_mul_mono hP hfloor
  simp only [Matrix.mul_smul, Matrix.mul_one, realTrace_smul] at hmono
  calc
    _ ≤ ‖Δ‖ * realTrace P := norm_trace_mul_le P Δ hP
    _ ≤ r * realTrace P := mul_le_mul_of_nonneg_right hΔ htrace
    _ = (r / μ) * (μ * realTrace P) := by field_simp
    _ ≤ (r / μ) * realTrace (P * S) :=
      mul_le_mul_of_nonneg_left hmono (div_nonneg hr hμ.le)

theorem density_posSemidef {S : Matrix n n ℂ} {μ : ℝ} (hμ : 0 < μ)
    (hfloor : μ • (1 : Matrix n n ℂ) ≤ S) : S.PosSemidef :=
  Matrix.nonneg_iff_posSemidef.mp
    (((Matrix.PosSemidef.one : (1 : Matrix n n ℂ).PosSemidef).smul hμ.le).nonneg.trans hfloor)

omit [DecidableEq n] in
theorem trace_pairing_real (P S : Matrix n n ℂ)
    (hP : P.IsHermitian) (hS : S.IsHermitian) :
    Matrix.trace (P * S) = (realTrace (P * S) : ℂ) := by
  symm
  apply Complex.conj_eq_iff_re.mp
  change star (Matrix.trace (P * S)) = Matrix.trace (P * S)
  rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hP.eq, hS.eq,
    Matrix.trace_mul_comm]

/-- Division is total; a zero base trace has zero relative error. -/
def traceError (P S Δ : Matrix n n ℂ) : ℂ :=
  Matrix.trace (P * Δ) / (realTrace (P * S) : ℂ)

theorem traceError_bound (P S Δ : Matrix n n ℂ) (hP : P.PosSemidef)
    {μ r : ℝ} (hμ : 0 < μ) (hfloor : μ • (1 : Matrix n n ℂ) ≤ S)
    (hΔ : ‖Δ‖ ≤ r) : ‖traceError P S Δ‖ ≤ r / μ := by
  have hr : 0 ≤ r := (norm_nonneg Δ).trans hΔ
  have hp := realTrace_mul_nonneg hP (density_posSemidef hμ hfloor)
  by_cases hpzero : realTrace (P * S) = 0
  · simp only [traceError, hpzero, Complex.ofReal_zero, div_zero, norm_zero]
    exact div_nonneg hr hμ.le
  · have hppos : 0 < realTrace (P * S) := lt_of_le_of_ne hp (Ne.symm hpzero)
    rw [traceError, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hppos]
    exact (div_le_iff₀ hppos).mpr (relative_trace_error P S Δ hP hμ hfloor hΔ)

/-- Exact multiplicative trace factorization, including zero source pieces.
If the base trace is zero, the proved trace estimate forces the perturbation
trace to vanish as well. -/
theorem trace_eq_base_mul_error (P S Δ : Matrix n n ℂ) (hP : P.PosSemidef)
    {μ : ℝ} (hμ : 0 < μ) (hfloor : μ • (1 : Matrix n n ℂ) ≤ S) :
    Matrix.trace (P * (S + Δ)) = (realTrace (P * S) : ℂ) * (1 + traceError P S Δ) := by
  rw [Matrix.mul_add, Matrix.trace_add,
    trace_pairing_real P S hP.isHermitian (density_posSemidef hμ hfloor).isHermitian]
  by_cases hpzero : realTrace (P * S) = 0
  · have hh := relative_trace_error P S Δ hP hμ hfloor (le_refl ‖Δ‖)
    rw [hpzero, mul_zero] at hh
    have hq : Matrix.trace (P * Δ) = 0 := norm_eq_zero.mp (le_antisymm hh (norm_nonneg _))
    simp only [hpzero, Complex.ofReal_zero, hq, add_zero, zero_mul]
  · have hp : (realTrace (P * S) : ℂ) ≠ 0 := by exact_mod_cast hpzero
    unfold traceError
    field_simp


section Scalar

/-- The actual holomorphic quadratic owner, including its real scale. -/
def owner (u x : ℝ) (z : ℂ) : ℂ := (u : ℂ) * (1 - ((x : ℂ) + z) ^ 2)

def baseOwner (u x : ℝ) : ℝ := u * (1 - x ^ 2)

theorem owner_zero (u x : ℝ) : owner u x 0 = (baseOwner u x : ℂ) := by
  simp [owner, baseOwner]

theorem quadratic_owner_displacement {x r : ℝ} (hx : |x| ≤ 1) (_hr : 0 ≤ r)
    (z : ℂ) (hz : ‖z‖ ≤ r) :
    ‖(1 - ((x : ℂ) + z) ^ 2) - (1 - (x : ℂ) ^ 2)‖ ≤ 2 * r + r ^ 2 := by
  have he : (1 - ((x : ℂ) + z) ^ 2) - (1 - (x : ℂ) ^ 2) =
      -(2 * (x : ℂ) * z) - z ^ 2 := by ring
  rw [he]
  calc
    _ ≤ ‖-(2 * (x : ℂ) * z)‖ + ‖z ^ 2‖ := norm_sub_le _ _
    _ = 2 * |x| * ‖z‖ + ‖z‖ ^ 2 := by
      simp only [norm_neg, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
      norm_num
    _ ≤ 2 * r + r ^ 2 := by
      have hp := mul_le_mul_of_nonneg_right hx (norm_nonneg z)
      have hs := pow_le_pow_left₀ (norm_nonneg z) hz 2
      nlinarith

theorem quadratic_owner_lower {x ρ : ℝ} (hρ : 0 < ρ) (hx : |x| ≤ 1 - ρ) :
    ρ ≤ 1 - x ^ 2 := by
  have hxone : |x| ≤ 1 := by linarith
  nlinarith [sq_abs x, abs_nonneg x, mul_nonneg (abs_nonneg x) (sub_nonneg.mpr hxone)]

/-- A relative owner error with the scale cancelled exactly. -/
def ownerError (x : ℝ) (z : ℂ) : ℂ :=
  ((1 - ((x : ℂ) + z) ^ 2) - (1 - (x : ℂ) ^ 2)) / ((1 - x ^ 2 : ℝ) : ℂ)

theorem ownerError_bound {x ρ r : ℝ} (hρ : 0 < ρ) (hx : |x| ≤ 1 - ρ)
    (hr : 0 ≤ r) (z : ℂ) (hz : ‖z‖ ≤ r) :
    ‖ownerError x z‖ ≤ (2 * r + r ^ 2) / ρ := by
  have hb := quadratic_owner_lower hρ hx
  have hbpos : 0 < 1 - x ^ 2 := hρ.trans_le hb
  have hn := quadratic_owner_displacement (by linarith : |x| ≤ 1) hr z hz
  rw [ownerError, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hbpos]
  exact (div_le_div_of_nonneg_right hn hbpos.le).trans
    (div_le_div_of_nonneg_left (by positivity) hρ hb)

/-- The actual owner is its positive real base times `1 + ownerError`;
this identity explains why the scale `u` does not enter the relative cap. -/
theorem owner_eq_base_mul_error (u : ℝ) {x ρ : ℝ} (hρ : 0 < ρ)
    (hx : |x| ≤ 1 - ρ) (z : ℂ) :
    owner u x z = (baseOwner u x : ℂ) * (1 + ownerError x z) := by
  have hbpos : 0 < 1 - x ^ 2 := hρ.trans_le (quadratic_owner_lower hρ hx)
  have hb : (((1 - x ^ 2 : ℝ) : ℂ)) ≠ 0 := by exact_mod_cast ne_of_gt hbpos
  unfold owner baseOwner ownerError
  push_cast
  push_cast at hb
  field_simp [hb]
  ring

/-- The requested relative error for the actual scaled owner. Its positive
scale cancels, so the bound depends only on the endpoint margin and increment. -/
theorem owner_scaled_relative_bound {u x ρ r : ℝ} (hu : 0 < u)
    (hρ : 0 < ρ) (hx : |x| ≤ 1 - ρ) (hr : 0 ≤ r) (z : ℂ) (hz : ‖z‖ ≤ r) :
    ‖owner u x z - (baseOwner u x : ℂ)‖ / baseOwner u x ≤ (2 * r + r ^ 2) / ρ := by
  have hbase : 0 < baseOwner u x := mul_pos hu
    (hρ.trans_le (quadratic_owner_lower hρ hx))
  have he : owner u x z - (baseOwner u x : ℂ) =
      (baseOwner u x : ℂ) * ownerError x z := by
    rw [owner_eq_base_mul_error u hρ hx z]
    ring
  rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hbase,
    mul_div_cancel_left₀ _ (ne_of_gt hbase)]
  exact ownerError_bound hρ hx hr z hz

/-- Independent relative errors combine multiplicatively, over `ℂ`. -/
theorem product_error_bound (ec ep : ℂ) {Rc Rp : ℝ}
    (hRc : 0 ≤ Rc) (_hRp : 0 ≤ Rp) (hc : ‖ec‖ ≤ Rc) (hp : ‖ep‖ ≤ Rp) :
    ‖(1 + ec) * (1 + ep) - 1‖ ≤ (1 + Rc) * (1 + Rp) - 1 := by
  have he : (1 + ec) * (1 + ep) - 1 = ec + ep + ec * ep := by ring
  rw [he]
  calc
    _ ≤ ‖ec‖ + ‖ep‖ + ‖ec * ep‖ := (norm_add_le _ _).trans
      (add_le_add_right (norm_add_le _ _) _)
    _ ≤ Rc + Rp + Rc * Rp := by
      rw [norm_mul]
      exact add_le_add (add_le_add hc hp) (mul_le_mul hc hp (norm_nonneg _) hRc)
    _ = _ := by ring

end Scalar

/-- The actual relative coefficient error when both the quadratic owner
and its trace pairing are perturbed. -/
def combinedError (x : ℝ) (z : ℂ) (P S Δ : Matrix n n ℂ) : ℂ :=
  (1 + ownerError x z) * (1 + traceError P S Δ) - 1

def combinedCap (ρ μ rc rp : ℝ) : ℝ :=
  (1 + (2 * rc + rc ^ 2) / ρ) * (1 + rp / μ) - 1

theorem combinedError_bound (P S Δ : Matrix n n ℂ) (hP : P.PosSemidef)
    {μ ρ rc rp x : ℝ} (hμ : 0 < μ) (hfloor : μ • (1 : Matrix n n ℂ) ≤ S)
    (hρ : 0 < ρ) (hx : |x| ≤ 1 - ρ) (hrc : 0 ≤ rc)
    (z : ℂ) (hz : ‖z‖ ≤ rc) (hΔ : ‖Δ‖ ≤ rp) :
    ‖combinedError x z P S Δ‖ ≤ combinedCap ρ μ rc rp := by
  have hrp : 0 ≤ rp := (norm_nonneg Δ).trans hΔ
  exact product_error_bound (ownerError x z) (traceError P S Δ)
    (by positivity) (div_nonneg hrp hμ.le)
    (ownerError_bound hρ hx hrc z hz) (traceError_bound P S Δ hP hμ hfloor hΔ)

/-- This connects the proved relative error to the actual perturbed owner
times the actual complex trace pairing. The real scale `u` is arbitrary. -/
theorem coefficient_eq_base_mul_error (u : ℝ) (P S Δ : Matrix n n ℂ) (hP : P.PosSemidef)
    {μ ρ x : ℝ} (hμ : 0 < μ) (hfloor : μ • (1 : Matrix n n ℂ) ≤ S)
    (hρ : 0 < ρ) (hx : |x| ≤ 1 - ρ) (z : ℂ) :
    owner u x z * Matrix.trace (P * (S + Δ)) =
      ((baseOwner u x * realTrace (P * S) : ℝ) : ℂ) * (1 + combinedError x z P S Δ) := by
  rw [owner_eq_base_mul_error u hρ hx z, trace_eq_base_mul_error P S Δ hP hμ hfloor]
  unfold combinedError
  push_cast
  ring

variable {ι m : Type*} [Fintype ι] [DecidableEq ι] [Fintype m] [DecidableEq m]


theorem combined_partition_perturbation (E : ι → Matrix m m ℂ)
    (hE : ∀ i, (E i).PosSemidef) (hsum : (∑ i, E i) = 1)
    (P : ι → Matrix n n ℂ) (hP : ∀ i, (P i).PosSemidef) (S Δ : Matrix n n ℂ)
    {μ ρ rc rp : ℝ} (hμ : 0 < μ) (hfloor : μ • (1 : Matrix n n ℂ) ≤ S)
    (hρ : 0 < ρ) (hrc : 0 ≤ rc) (x : ι → ℝ) (hx : ∀ i, |x i| ≤ 1 - ρ)
    (z : ι → ℂ) (hz : ∀ i, ‖z i‖ ≤ rc) (hΔ : ‖Δ‖ ≤ rp) :
    ‖(∑ i, (1 + combinedError (x i) (z i) (P i) S Δ) • E i) - 1‖ ≤
      combinedCap ρ μ rc rp := by
  have hrp : 0 ≤ rp := (norm_nonneg Δ).trans hΔ
  have hc : 0 ≤ (2 * rc + rc ^ 2) / ρ := by positivity
  have hp : 0 ≤ rp / μ := div_nonneg hrp hμ.le
  apply KSComplexRelativeSource.partition_perturbation E hE hsum
    (fun i => combinedError (x i) (z i) (P i) S Δ) _
    (fun i => combinedError_bound (P i) S Δ (hP i) hμ hfloor hρ (hx i) hrc (z i) (hz i) hΔ)
  unfold combinedCap
  nlinarith [mul_nonneg hc hp]

end MatrixSpencer.KSComplexOwnerPerturbation
