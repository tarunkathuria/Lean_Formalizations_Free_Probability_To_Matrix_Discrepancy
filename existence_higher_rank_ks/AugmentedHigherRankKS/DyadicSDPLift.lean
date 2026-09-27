import HigherRankKS.CarrierSmoothness
import MatrixSpencer.BalancedTransport
import MatrixSpencer.SignedLift
import MatrixSpencer.FidelityContinuity
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.IntegralRepresentation

/-! The dyadic power hypograph used by the higher-rank value SDP. -/
open Matrix MatrixSpencer HigherRankKS Filter Set
open scoped BigOperators Topology MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace AugmentedHigherRankKS.DyadicSDP
variable {n : Type*} [Fintype n] [DecidableEq n]
local instance dyadicSDPCStar : CStarAlgebra (Matrix n n ℂ) := {}

/-- The positive solution of the Schur equation dominates every positive
feasible off-diagonal block. -/
theorem block_maximal_of_posDef {M P Y Z : Matrix n n ℂ}
    (hM : M.PosDef) (hY : Y.PosSemidef) (hZ : Z.PosSemidef)
    (hblock : (Matrix.fromBlocks M Y Y P).PosSemidef)
    (hsolve : Z * M⁻¹ * Z = P) : Y ≤ Z := by
  let J := transportInverseSqrt M
  have hJ : J.PosDef := transportInverseSqrt_posDef hM
  letI : Invertible M := hM.isUnit.invertible
  have hsq : J * J = M⁻¹ := by
    apply hM.isUnit.mul_right_cancel
    rw [Matrix.inv_mul_of_invertible]
    change transportInverseSqrt M * transportInverseSqrt M * M = 1
    rw [Matrix.mul_assoc, transportInverseSqrt_mul_self_matrix hM,
      transportInverseSqrt_mul_sqrt hM]
  have hschur : Y * M⁻¹ * Y ≤ P := by
    have hs := (hM.fromBlocks₁₁ Y P).mp (by simpa only [hY.isHermitian.eq] using hblock)
    exact sub_nonneg.mp (by simpa only [hY.isHermitian.eq] using hs.nonneg)
  have hjy : (J * Y * J).PosSemidef := by
    simpa only [hJ.isHermitian.eq] using hY.conjTranspose_mul_mul_same J
  have hjz : (J * Z * J).PosSemidef := by
    simpa only [hJ.isHermitian.eq] using hZ.conjTranspose_mul_mul_same J
  have hord : J * (Y * M⁻¹ * Y) * J ≤ J * P * J := by
    exact hJ.isHermitian.isSelfAdjoint.conjugate_le_conjugate hschur
  have hleft : (J * Y * J)^2 = J * (Y * M⁻¹ * Y) * J := by
    rw [← hsq]; noncomm_ring
  have hright : (J * Z * J)^2 = J * P * J := by
    rw [← hsolve, ← hsq]; noncomm_ring
  rw [← hleft, ← hright] at hord
  have hle := CFC.sqrt_le_sqrt _ _ hord
  rw [CFC.sqrt_sq _ hjy.nonneg, CFC.sqrt_sq _ hjz.nonneg] at hle
  have hback := hM.posDef_sqrt.isHermitian.isSelfAdjoint.conjugate_le_conjugate hle
  have hSJ : CFC.sqrt M * J = 1 := sqrt_mul_transportInverseSqrt hM
  have hJS : J * CFC.sqrt M = 1 := transportInverseSqrt_mul_sqrt hM
  simp only [Matrix.mul_assoc, hJS, Matrix.mul_one] at hback
  simpa only [← Matrix.mul_assoc, hSJ, Matrix.one_mul] using hback

/-- The explicit target after one more geometric-mean step. -/
def target (p : ℝ) (M : Matrix n n ℂ) (j : ℕ) : Matrix n n ℂ :=
  p ^ ((1 : ℝ) / 2 ^ j) • CFC.rpow M (1 - (1 : ℝ) / 2 ^ j)

@[simp] theorem target_zero (p : ℝ) {M : Matrix n n ℂ} (hM : M.PosSemidef) :
    target p M 0 = p • 1 := by
  simp only [target, pow_zero, div_one, Real.rpow_one, sub_self]
  simp only [CFC.rpow_eq_pow, CFC.rpow_zero M hM.nonneg]

theorem target_posSemidef {p : ℝ} (hp : 0 ≤ p) (M : Matrix n n ℂ) (j : ℕ) :
    (target p M j).PosSemidef := by
  exact Matrix.nonneg_iff_posSemidef.mp
    (smul_nonneg (Real.rpow_nonneg hp _) CFC.rpow_nonneg)

lemma exponent_nonneg (j : ℕ) : 0 ≤ 1 - (1 : ℝ) / 2 ^ j := by
  have hpow : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  exact sub_nonneg.mpr ((div_le_one (by positivity)).mpr hpow)

lemma exponent_le_one (j : ℕ) : 1 - (1 : ℝ) / 2 ^ j ≤ 1 := sub_le_self _ (by positivity)

lemma dyadic_double (j : ℕ) :
    (1 : ℝ) / 2 ^ (j + 1) + 1 / 2 ^ (j + 1) = 1 / 2 ^ j := by
  rw [pow_succ]; field_simp; ring

theorem target_schur {p : ℝ} (hp : 0 ≤ p) {M : Matrix n n ℂ}
    (hM : M.PosDef) (j : ℕ) :
    target p M (j + 1) * M⁻¹ * target p M (j + 1) = target p M j := by
  letI : Invertible M := hM.isUnit.invertible
  have hinv : M⁻¹ = CFC.rpow M (-1) := by
    apply hM.isUnit.mul_left_cancel
    rw [Matrix.mul_inv_of_invertible]
    nth_rw 1 [← CFC.rpow_one M hM.posSemidef.nonneg]
    simp only [CFC.rpow_eq_pow]
    rw [← CFC.rpow_add hM.isUnit]
    norm_num [CFC.rpow_zero M hM.posSemidef.nonneg]
  simp only [target, hinv, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    CFC.rpow_eq_pow]
  rw [← CFC.rpow_add hM.isUnit, ← CFC.rpow_add hM.isUnit,
    ← Real.rpow_add_of_nonneg hp (by positivity) (by positivity), dyadic_double]
  congr 2
  linarith [dyadic_double j]

theorem target_block_posDef {p : ℝ} (hp : 0 ≤ p) {M : Matrix n n ℂ}
    (hM : M.PosDef) (j : ℕ) :
    (Matrix.fromBlocks M (target p M (j + 1)) (target p M (j + 1))
      (target p M j)).PosSemidef := by
  letI : Invertible M := hM.isUnit.invertible
  have hh := (target_posSemidef hp M (j+1)).isHermitian.eq
  have hb := (hM.fromBlocks₁₁ (target p M (j+1)) (target p M j)).mpr
    (show (target p M j - (target p M (j+1))ᴴ * M⁻¹ * target p M (j+1)).PosSemidef by
      rw [hh, target_schur hp hM, sub_self]; exact Matrix.PosSemidef.zero)
  simpa only [hh] using hb

/-- Monotonicity is used only to pass through a harmless positive-definite
approximation of a possibly singular carrier. -/
theorem target_mono {p : ℝ} (hp : 0 ≤ p) (j : ℕ)
    {M N : Matrix n n ℂ} (hMN : M ≤ N) : target p M j ≤ target p N j := by
  exact smul_le_smul_of_nonneg_left
    (CFC.rpow_le_rpow ⟨exponent_nonneg j, exponent_le_one j⟩ hMN)
    (Real.rpow_nonneg hp _)


theorem block_increase_diagonal {M P Y M' P' : Matrix n n ℂ}
    (hblock : (Matrix.fromBlocks M Y Y P).PosSemidef)
    (hM : M ≤ M') (hP : P ≤ P') :
    (Matrix.fromBlocks M' Y Y P').PosSemidef := by
  have hd := posSemidef_fromBlocks_diagonal (sub_nonneg.mpr hM).posSemidef
    (sub_nonneg.mpr hP).posSemidef
  have h := hblock.add hd
  simpa only [Matrix.fromBlocks_add, add_zero, add_sub_cancel] using h

theorem target_regularize_tendsto (p : ℝ) {M : Matrix n n ℂ}
    (hM : M.PosSemidef) (j : ℕ) :
    Tendsto (fun t => target p (regularize M t) j) (𝓝[>] 0) (𝓝 (target p M j)) := by
  have hc : ContinuousOn (fun M : Matrix n n ℂ => CFC.rpow M (1 - 1 / 2 ^ j))
      {M | M.PosSemidef} :=
    continuousOn_iff_continuous_restrict.mpr (continuous_matrix_rpow_psd (exponent_nonneg j))
  have he : ∀ᶠ t : ℝ in 𝓝[>] 0, (regularize M t).PosSemidef := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (regularize_posDef hM ht).posSemidef
  have hlim := (hc M hM).tendsto.comp
    (tendsto_nhdsWithin_iff.mpr ⟨regularize_tendsto M, he⟩)
  exact hlim.const_smul _

/-- The explicit attaining blocks remain feasible for singular carriers. -/
theorem target_block {p : ℝ} (hp : 0 ≤ p) {M : Matrix n n ℂ}
    (hM : M.PosSemidef) (j : ℕ) :
    (Matrix.fromBlocks M (target p M (j+1)) (target p M (j+1)) (target p M j)).PosSemidef := by
  let B := fun t : ℝ => Matrix.fromBlocks (regularize M t)
    (target p (regularize M t) (j+1)) (target p (regularize M t) (j+1))
    (target p (regularize M t) j)
  have hc : Continuous (fun P : (Matrix n n ℂ) × (Matrix n n ℂ) × (Matrix n n ℂ) =>
      Matrix.fromBlocks P.1 P.2.1 P.2.1 P.2.2) := by
    apply continuous_pi; intro i; apply continuous_pi; intro k
    cases i <;> cases k <;> fun_prop
  have hl : Tendsto B (𝓝[>] 0)
      (𝓝 (Matrix.fromBlocks M (target p M (j+1)) (target p M (j+1)) (target p M j))) :=
    hc.continuousAt.tendsto.comp ((regularize_tendsto M).prodMk_nhds
      ((target_regularize_tendsto p hM (j+1)).prodMk_nhds (target_regularize_tendsto p hM j)))
  apply Matrix.nonneg_iff_posSemidef.mp
  apply ge_of_tendsto hl
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (target_block_posDef hp (regularize_posDef hM ht) j).nonneg

/-- A single SDP block propagates the sharp dyadic upper bound, including at
a singular carrier. -/
theorem step_upper {p : ℝ} (hp : 0 ≤ p) {M P Y : Matrix n n ℂ}
    (hM : M.PosSemidef) (hY : Y.PosSemidef) (j : ℕ)
    (hblock : (Matrix.fromBlocks M Y Y P).PosSemidef)
    (hP : P ≤ target p M j) : Y ≤ target p M (j+1) := by
  apply ge_of_tendsto (target_regularize_tendsto p hM (j+1))
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hreg := regularize_posDef hM ht
  have hmono := le_regularize M (le_of_lt ht)
  apply block_maximal_of_posDef hreg hY (target_posSemidef hp _ _)
  · exact block_increase_diagonal hblock hmono (hP.trans (target_mono hp j hmono))
  · exact target_schur hp hreg j

/-- All feasible SDP chains are below the actual power source. -/
theorem chain_upper {p : ℝ} (hp : 0 ≤ p) {M : Matrix n n ℂ}
    (hM : M.PosSemidef) (Y : ℕ → Matrix n n ℂ) (k : ℕ)
    (hzero : Y 0 = p • 1) (hY : ∀ j ≤ k, (Y j).PosSemidef)
    (hb : ∀ j < k, (Matrix.fromBlocks M (Y (j+1)) (Y (j+1)) (Y j)).PosSemidef) :
    Y k ≤ target p M k := by
  induction k with
  | zero => rw [hzero, target_zero p hM]
  | succ k ih =>
    exact step_upper hp hM (hY (k+1) le_rfl) k (hb k (by omega))
      (ih (fun j hj => hY j (by omega)) (fun j hj => hb j (by omega)))


/-- A finite prefix of a matrix sequence contains all variables and
constraints of the lift; terms after `k` are unused. -/
def Feasible (M : Matrix n n ℂ) (p : ℝ) (k : ℕ) (Y : ℕ → Matrix n n ℂ) : Prop :=
  Y 0 = p • 1 ∧ (∀ j ≤ k, (Y j).PosSemidef) ∧
    ∀ j < k, (Matrix.fromBlocks M (Y (j+1)) (Y (j+1)) (Y j)).PosSemidef

theorem target_feasible {p : ℝ} (hp : 0 ≤ p) {M : Matrix n n ℂ}
    (hM : M.PosSemidef) (k : ℕ) : Feasible M p k (target p M) :=
  ⟨target_zero p hM, fun j _ => target_posSemidef hp M j,
    fun j _ => target_block hp hM j⟩

theorem feasible_le_carrierPower {M : Matrix n n ℂ} (hM : M.PosSemidef)
    {k : ℕ} {Y : ℕ → Matrix n n ℂ} (h : Feasible M (realTrace M) k Y) :
    Y k ≤ carrierPower ((1 : ℝ) / 2 ^ k) M :=
  chain_upper (realTrace_nonneg hM) hM Y k h.1 h.2.1 h.2.2

/-- The matrix power source is exactly the greatest feasible final block. -/
theorem carrierPower_exact {M : Matrix n n ℂ} (hM : M.PosSemidef) (k : ℕ) :
    ∃ Y : ℕ → Matrix n n ℂ, Feasible M (realTrace M) k Y ∧
      Y k = carrierPower ((1 : ℝ) / 2 ^ k) M ∧
      ∀ Y', Feasible M (realTrace M) k Y' → Y' k ≤ Y k := by
  refine ⟨target (realTrace M) M, target_feasible (realTrace_nonneg hM) hM k, rfl, ?_⟩
  intro Y hY
  exact feasible_le_carrierPower hM hY


end AugmentedHigherRankKS.DyadicSDP
