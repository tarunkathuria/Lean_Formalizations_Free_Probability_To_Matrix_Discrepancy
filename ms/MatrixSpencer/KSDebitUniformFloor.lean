import MatrixSpencer.KSOwnerInputBounds
import MatrixSpencer.KSOptimizerFloor
import MatrixSpencer.KSDebitPreparedCurvature

/-!
# An arithmetic optimizer floor uniform over the cube

All budgets use finite sums of input-entry matrix bounds and scalar arithmetic.
They contain no optimized value, operator-norm computation, support eigenvalue
bound, or maximum over a compact set. The same floor applies to every actual
state debit and to any fixed PSD debit below its input-derived scalar bound.
-/

open Matrix Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSDebitUniformFloor

open KSOwnerInputBounds KSPotentialModels KSLiveCurve
variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
variable {N : ℕ}
local instance {k : Type*} [Fintype k] [DecidableEq k] : CStarAlgebra (Matrix k k ℂ) := {}

/-- An arithmetic upper bound for all signed sums of the physical atoms. -/
def atomBudget (v : ι → n → ℂ) : ℝ := 1 + ∑ i, matrixBound (KSRankOne.atom (v i))

/-- The covariance entries are at most `32`, since natural owners are at most `64`. -/
def spinBudget (v : ι → n → ℂ) : ℝ :=
  1 + 32 * ∑ j, (matrixBound (KSSpinSource.family (fun i => KSRankOne.atom (v i)) j)) ^ 2

omit [DecidableEq ι] [DecidableEq n] in
theorem atomBudget_pos (v : ι → n → ℂ) : 0 < atomBudget v := by
  have h := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => (matrixBound_pos (KSRankOne.atom (v i))).le)
  unfold atomBudget
  linarith

omit [DecidableEq ι] [DecidableEq n] in
theorem spinBudget_pos (v : ι → n → ℂ) : 0 < spinBudget v := by
  unfold spinBudget
  positivity

omit [DecidableEq n] in
theorem krausBudget_le_spinBudget (v : ι → n → ℂ) (c : ι → ℝ)
    (hc : ∀ i, 0 ≤ c i) (hc64 : ∀ i, c i ≤ 64) :
    krausBudget (KSSpinSource.family (fun i => KSRankOne.atom (v i)))
      (KSSpinSource.coefficientCovariance c) ≤ spinBudget v := by
  unfold krausBudget spinBudget
  simp only [KSSpinSource.coefficientCovariance, Matrix.diagonal_apply]
  simp only [abs_ite, abs_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  rw [Finset.mul_sum]
  apply add_le_add_left
  apply Finset.sum_le_sum
  intro j _
  rw [abs_of_nonneg (div_nonneg (hc j.1) (by norm_num))]
  have hh : c j.1 / 2 ≤ 32 := by linarith [hc64 j.1]
  simpa only [pow_two, mul_assoc] using
    mul_le_mul_of_nonneg_right hh (sq_nonneg (matrixBound
      (KSSpinSource.family (fun i => KSRankOne.atom (v i)) j)))

theorem spin_kraus_budget (v : ι → n → ℂ) (c : ι → ℝ)
    (hc : ∀ i, 0 ≤ c i) (hc64 : ∀ i, c i ≤ 64) :
    (∑ j, (covarianceKraus (KSSpinSource.family (fun i => KSRankOne.atom (v i)))
      (KSSpinSource.coefficientCovariance c) j)ᴴ *
      covarianceKraus (KSSpinSource.family (fun i => KSRankOne.atom (v i)))
        (KSSpinSource.coefficientCovariance c) j) ≤
      spinBudget v • (1 : Matrix (n ⊕ n) (n ⊕ n) ℂ) := by
  exact (covarianceKraus_budget _
    (KSSpinSource.family_isHermitian _ (fun i => KSRankOne.atom_isHermitian (v i)))
    (KSSpinSource.coefficientCovariance_posSemidef hc)).trans
    (smul_le_smul_of_nonneg_right (krausBudget_le_spinBudget v c hc hc64) zero_le_one)

omit [DecidableEq ι] in
theorem signed_sum_norm_le_atomBudget (v : ι → n → ℂ) (y : ι → ℝ)
    (hy : ∀ i, |y i| ≤ 1) : ‖∑ i, y i • KSRankOne.atom (v i)‖ ≤ atomBudget v := by
  calc
    ‖∑ i, y i • KSRankOne.atom (v i)‖ ≤ ∑ i, ‖y i • KSRankOne.atom (v i)‖ := norm_sum_le _ _
    _ ≤ ∑ i, matrixBound (KSRankOne.atom (v i)) := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul, Real.norm_eq_abs]
      exact (mul_le_mul (hy i) (norm_le_matrixBound _ (KSRankOne.atom_isHermitian (v i)))
        (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
    _ ≤ atomBudget v := by unfold atomBudget; linarith

/-- Scalar debit bound computed from the original atoms and label count. -/
def debitBound (v : Fin N → n → ℂ) (δ η : ℝ) : ℝ := δ * atomBudget v + N * η

def centerRadius (v : Fin N → n → ℂ) (δ η : ℝ) : ℝ := 1 + atomBudget v + debitBound v δ η

def uniformFloor (v : Fin N → n → ℂ) (δ η θ : ℝ) : ℝ :=
  (θ / KSOptimizerFloor.inputDenominator (n := n ⊕ n) (centerRadius v δ η) (spinBudget v) θ) ^ 2

omit [DecidableEq n] in
theorem debitBound_nonneg (v : Fin N → n → ℂ) {δ η : ℝ} (hδ : 0 ≤ δ) (hη : 0 ≤ η) :
    0 ≤ debitBound v δ η := by
  unfold debitBound
  exact add_nonneg (mul_nonneg hδ (atomBudget_pos v).le) (mul_nonneg (Nat.cast_nonneg _) hη)

omit [DecidableEq n] in
theorem centerRadius_pos (v : Fin N → n → ℂ) {δ η : ℝ} (hδ : 0 ≤ δ) (hη : 0 ≤ η) :
    0 < centerRadius v δ η := by
  unfold centerRadius
  linarith [atomBudget_pos v, debitBound_nonneg v hδ hη]

omit [DecidableEq n] in
theorem uniformFloor_pos [Nonempty n] (v : Fin N → n → ℂ) {δ η θ : ℝ}
    (hδ : 0 ≤ δ) (hη : 0 ≤ η) (hθ : 0 < θ) : 0 < uniformFloor v δ η θ :=
  KSOptimizerFloor.inputFloor_pos (centerRadius_pos v hδ hη).le hθ

/-- PSD doubling preserves a supplied scalar order bound. -/
theorem doubled_le_scalar {B : Matrix n n ℂ} {b : ℝ} (hB : B ≤ b • (1 : Matrix n n ℂ)) :
    KSSpinSource.doubled B ≤ b • (1 : Matrix (n ⊕ n) (n ⊕ n) ℂ) := by
  have h := KSSpinSource.doubled_posSemidef (Matrix.le_iff.mp hB)
  apply Matrix.le_iff.mpr
  convert h using 1
  ext i j
  cases i <;> cases j <;>
    simp [KSSpinSource.doubled, Matrix.fromBlocks, Matrix.one_apply, Matrix.sub_apply, Matrix.smul_apply]

theorem fixed_center_norm [Nonempty n] (v : Fin N → n → ℂ) {δ η : ℝ}
    (hδ : 0 ≤ δ) (hη : 0 ≤ η) {B : Matrix n n ℂ} (hB : B.PosSemidef)
    (hcap : B ≤ debitBound v δ η • (1 : Matrix n n ℂ))
    {y : Fin N → ℝ} (hy : y ∈ ksCube 1) :
    ‖KSDebitCenter.center (center (fun i => KSRankOne.atom (v i)) y) B‖ ≤ centerRadius v δ η := by
  have hd : ‖KSSpinSource.doubled B‖ ≤ debitBound v δ η := by
    apply (CStarAlgebra.norm_le_iff_le_algebraMap _ (debitBound_nonneg v hδ hη)
      (KSSpinSource.doubled_posSemidef hB).nonneg).mpr
    simpa only [Algebra.algebraMap_eq_smul_one] using doubled_le_scalar hcap
  have hc : ‖signedLift (center (fun i => KSRankOne.atom (v i)) y)‖ ≤ atomBudget v := by
    rw [signedLift_norm (center_isHermitian _ (fun i => KSRankOne.atom_isHermitian (v i)) y)]
    exact signed_sum_norm_le_atomBudget v y (fun i => abs_le.mpr ⟨hy.1 i, hy.2 i⟩)
  exact (norm_sub_le _ _).trans (by dsimp only [centerRadius]; linarith)

/-- Any fixed admissible debit shares the same arithmetic density floor. -/
theorem fixed_debit_optimizer_floor [Nonempty n] (v : Fin N → n → ℂ) {δ η θ : ℝ}
    (hδ : 0 ≤ δ) (hη : 0 ≤ η) (hθ : 0 < θ) {B : Matrix n n ℂ}
    (hB : B.PosSemidef) (hcap : B ≤ debitBound v δ η • (1 : Matrix n n ℂ))
    {y : Fin N → ℝ} (hy : y ∈ ksCube 1) :
    uniformFloor v δ η θ • (1 : Matrix (n ⊕ n) (n ⊕ n) ℂ) ≤
      densityOptimizer (KSDebitCenter.center (center (fun i => KSRankOne.atom (v i)) y) B)
        (covarianceKraus (KSSpinSource.family (fun i => KSRankOne.atom (v i)))
          (KSSpinSource.coefficientCovariance (naturalOwners 64 y))) θ := by
  apply KSOptimizerFloor.densityOptimizer_floor _
    (KSDebitCenter.center_isHermitian_of_posSemidef
      (center_isHermitian _ (fun i => KSRankOne.atom_isHermitian (v i)) y) hB) _ hθ
    (fixed_center_norm v hδ hη hB hcap hy)
  exact spin_kraus_budget v _ (naturalOwners_nonneg (by norm_num) le_rfl hy)
    (fun i => by dsimp only [naturalOwners]; nlinarith [sq_nonneg (y i)])

/-- The actual debit is bounded by the same input scalar at every state. -/
theorem debit_norm_le [Nonempty n] (v : Fin N → n → ℂ) {δ η : ℝ}
    (hδ : 0 ≤ δ) (hη : 0 ≤ η) (x : Fin N → ℝ) :
    ‖KSDebitBudget.debit (fun i => KSRankOne.atom (v i)) δ η x‖ ≤ debitBound v δ η := by
  have hs : ‖∑ i ∈ ksFrozen 1 x, KSRankOne.atom (v i)‖ ≤ atomBudget v := by
    calc
      _ ≤ ∑ i ∈ ksFrozen 1 x, ‖KSRankOne.atom (v i)‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ ksFrozen 1 x, matrixBound (KSRankOne.atom (v i)) :=
        Finset.sum_le_sum (fun i _ => norm_le_matrixBound _ (KSRankOne.atom_isHermitian (v i)))
      _ ≤ ∑ i, matrixBound (KSRankOne.atom (v i)) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => (matrixBound_pos _).le)
      _ ≤ atomBudget v := by unfold atomBudget; linarith
  have hc : ((ksFrozen 1 x).card : ℝ) ≤ N := by
    exact_mod_cast (show (ksFrozen 1 x).card ≤ N by simpa using Finset.card_le_univ (ksFrozen 1 x))
  unfold KSDebitBudget.debit
  apply (norm_add_le _ _).trans
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg hδ, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) hη), norm_one, mul_one]
  exact add_le_add (mul_le_mul_of_nonneg_left hs hδ) (mul_le_mul_of_nonneg_right hc hη)

theorem debit_le_scalar [Nonempty n] (v : Fin N → n → ℂ) {δ η : ℝ}
    (hδ : 0 ≤ δ) (hη : 0 ≤ η) (x : Fin N → ℝ) :
    KSDebitBudget.debit (fun i => KSRankOne.atom (v i)) δ η x ≤
      debitBound v δ η • (1 : Matrix n n ℂ) := by
  have h := (CStarAlgebra.norm_le_iff_le_algebraMap _ (debitBound_nonneg v hδ hη)
    (KSDebitBudget.debit_posSemidef _ (fun i => KSRankOne.atom_posSemidef (v i)) hδ hη x).nonneg).mp
      (debit_norm_le v hδ hη x)
  simpa only [Algebra.algebraMap_eq_smul_one] using h

/-- The canonical optimizer of the actual state has the positive uniform floor. -/
theorem state_optimizer_floor [Nonempty n] (v : Fin N → n → ℂ) {δ η θ : ℝ}
    (hδ : 0 ≤ δ) (hη : 0 ≤ η) (hθ : 0 < θ) {x : Fin N → ℝ} (hx : x ∈ ksCube 1) :
    uniformFloor v δ η θ • (1 : Matrix (n ⊕ n) (n ⊕ n) ℂ) ≤
      densityOptimizer
        (KSDebitCenter.center (center (fun i => KSRankOne.atom (v i)) x)
          (KSDebitBudget.debit (fun i => KSRankOne.atom (v i)) δ η x))
        (covarianceKraus (KSSpinSource.family (fun i => KSRankOne.atom (v i)))
          (KSSpinSource.coefficientCovariance (naturalOwners 64 x))) θ :=
  fixed_debit_optimizer_floor v hδ hη hθ
    (KSDebitBudget.debit_posSemidef _ (fun i => KSRankOne.atom_posSemidef (v i)) hδ hη x)
    (debit_le_scalar v hδ hη x) hx

omit [DecidableEq n] in
/-- Removing dead labels can only decrease the arithmetic source budget. -/
theorem spinBudget_restrict (v : Fin N → n → ℂ) (x : Fin N → ℝ) :
    spinBudget (fun i : Live 1 x => v i) ≤ spinBudget v := by
  let f := fun i : Fin N => ∑ a : Fin 4,
    (matrixBound (KSSpinSource.pauli (KSRankOne.atom (v i)) a)) ^ 2
  have hs := Fintype.sum_subtype_add_sum_subtype (fun i : Fin N => |x i| < 1) f
  have hn : 0 ≤ ∑ i : {i : Fin N // ¬ |x i| < 1}, f i := by
    apply Finset.sum_nonneg
    intro i _
    exact Finset.sum_nonneg (fun a _ => sq_nonneg _)
  have hle : (∑ i : Live 1 x, f i) ≤ ∑ i, f i := by linarith
  simp only [spinBudget, Fintype.sum_prod_type, KSSpinSource.family]
  exact add_le_add_left (mul_le_mul_of_nonneg_left hle (by norm_num)) _

/-- The same floor holds for the full-density optimizer after removing dead coefficient labels. -/
theorem restricted_fixed_debit_optimizer_floor [Nonempty n]
    (v : Fin N → n → ℂ) {δ η θ : ℝ} (hδ : 0 ≤ δ) (hη : 0 ≤ η) (hθ : 0 < θ)
    {B : Matrix n n ℂ} (hB : B.PosSemidef)
    (hcap : B ≤ debitBound v δ η • (1 : Matrix n n ℂ))
    (x : Fin N → ℝ) {y : Fin N → ℝ} (hy : y ∈ ksCube 1) :
    uniformFloor v δ η θ • (1 : Matrix (n ⊕ n) (n ⊕ n) ℂ) ≤
      densityOptimizer (KSDebitCenter.center (center (fun i => KSRankOne.atom (v i)) y) B)
        (covarianceKraus (KSSpinSource.family (fun i : Live 1 x => KSRankOne.atom (v i)))
          (KSSpinSource.coefficientCovariance (fun i : Live 1 x => naturalOwners 64 y i))) θ := by
  apply KSOptimizerFloor.densityOptimizer_floor _
    (KSDebitCenter.center_isHermitian_of_posSemidef
      (center_isHermitian _ (fun i => KSRankOne.atom_isHermitian (v i)) y) hB) _ hθ
    (fixed_center_norm v hδ hη hB hcap hy)
  exact (spin_kraus_budget (fun i : Live 1 x => v i) _
    (fun i => naturalOwners_nonneg (by norm_num) le_rfl hy i)
    (fun i => by dsimp only [naturalOwners]; nlinarith [sq_nonneg (y i)])).trans
    (smul_le_smul_of_nonneg_right (spinBudget_restrict v x) zero_le_one)

/-- Uniform floor for the exact live-curve optimizer used by the actual envelope. -/
theorem live_curve_optimizer_floor [Nonempty n]
    (v : Fin N → n → ℂ) {δ η θ : ℝ} (hδ : 0 ≤ δ) (hη : 0 ≤ η) (hθ : 0 < θ)
    {B : Matrix n n ℂ} (hB : B.PosSemidef)
    (hcap : B ≤ debitBound v δ η • (1 : Matrix n n ℂ))
    (x : Fin N → ℝ) (h : Live 1 x → ℝ) (t : ℝ) (hy : path 1 x h t ∈ ksCube 1) :
    uniformFloor v δ η θ • (1 : Matrix (n ⊕ n) (n ⊕ n) ℂ) ≤
      (hermitianDensityOptimizer
        (KSDebitLocalState.curveCenter
          (KSDebitCenter.center (center (fun i => KSRankOne.atom (v i)) x) B)
          (fun i : Live 1 x => v i) h t)
        (covarianceKraus (KSSpinSource.family (fun i : Live 1 x => KSRankOne.atom (v i)))
          (KSSpinSource.coefficientCovariance
            (KSSpinLocalState.ownerCurve (fun i : Live 1 x => x i) h t))) θ :
        Matrix (n ⊕ n) (n ⊕ n) ℂ) := by
  have hc : KSDebitLocalState.curveCenter
      (KSDebitCenter.center (center (fun i => KSRankOne.atom (v i)) x) B)
      (fun i : Live 1 x => v i) h t =
      KSDebitCenter.center (center (fun i => KSRankOne.atom (v i)) (path 1 x h t)) B := by
    rw [KSDebitPreparedCurvature.center_path_fixed_debit, sum_extend_smul]
    rfl
  have ho : KSSpinLocalState.ownerCurve (fun i : Live 1 x => x i) h t =
      (fun i : Live 1 x => naturalOwners 64 (path 1 x h t) i) := by
    funext i
    simp only [KSSpinLocalState.ownerCurve, naturalOwners, path_live]
  rw [hc, ho]
  exact restricted_fixed_debit_optimizer_floor v hδ hη hθ hB hcap x hy

/-- Actual state debit specialization, with no independent debit-bound premise. -/
theorem actual_live_curve_optimizer_floor [Nonempty n]
    (v : Fin N → n → ℂ) {δ η θ : ℝ} (hδ : 0 ≤ δ) (hη : 0 ≤ η) (hθ : 0 < θ)
    (x : Fin N → ℝ) (h : Live 1 x → ℝ) (t : ℝ) (hy : path 1 x h t ∈ ksCube 1) :
    uniformFloor v δ η θ • (1 : Matrix (n ⊕ n) (n ⊕ n) ℂ) ≤
      (hermitianDensityOptimizer
        (KSDebitLocalState.curveCenter
          (KSDebitCenter.center (center (fun i => KSRankOne.atom (v i)) x)
            (KSDebitBudget.debit (fun i => KSRankOne.atom (v i)) δ η x))
          (fun i : Live 1 x => v i) h t)
        (covarianceKraus (KSSpinSource.family (fun i : Live 1 x => KSRankOne.atom (v i)))
          (KSSpinSource.coefficientCovariance
            (KSSpinLocalState.ownerCurve (fun i : Live 1 x => x i) h t))) θ :
        Matrix (n ⊕ n) (n ⊕ n) ℂ) :=
  live_curve_optimizer_floor v hδ hη hθ
    (KSDebitBudget.debit_posSemidef _ (fun i => KSRankOne.atom_posSemidef (v i)) hδ hη x)
    (debit_le_scalar v hδ hη x) x h t hy

end MatrixSpencer.KSDebitUniformFloor
