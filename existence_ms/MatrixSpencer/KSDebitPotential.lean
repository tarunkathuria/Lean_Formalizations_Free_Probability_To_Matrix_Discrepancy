import MatrixSpencer.KSDebitBudget
import MatrixSpencer.KSVarianceBounds

/-!
# Exact potential values for the numerical walk's debit

Adding a scalar identity debit subtracts that scalar from the genuine
optimized potential. This accounts for the scalar debit in an accepted
endpoint test; it is an equality for the actual density optimization.
-/

open Matrix Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSDebitPotential

variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
local instance {k : Type*} [Fintype k] [DecidableEq k] : CStarAlgebra (Matrix k k ℂ) := {}

theorem ownerObjective_sub_scalar (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ)
    (C : Matrix ι ι ℝ) (θ r : ℝ) (S : Matrix n n ℂ) (ht : realTrace S = 1) :
    ownerObjective (H - r • (1 : Matrix n n ℂ)) A C θ S = ownerObjective H A C θ S - r := by
  simp only [ownerObjective, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul,
    realTrace_sub, realTrace_smul, ht, mul_one]
  ring

theorem ownerPotential_sub_scalar [Nonempty n]
    (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) {θ : ℝ} (hθ : 0 < θ) (r : ℝ) :
    ownerPotential (H - r • (1 : Matrix n n ℂ)) A C θ = ownerPotential H A C θ - r := by
  obtain ⟨S, hS, _, hp, hmax⟩ := exists_ownerOptimizer H A hA hC hθ
  obtain ⟨T, hT, _, hp', hmax'⟩ := exists_ownerOptimizer (H - r • (1 : Matrix n n ℂ))
    A hA hC hθ
  rw [hp', hp, ownerObjective_sub_scalar H A C θ r T hT.2]
  have hu := hmax T hT
  have hl := hmax' S hS
  rw [ownerObjective_sub_scalar H A C θ r S hS.2,
    ownerObjective_sub_scalar H A C θ r T hT.2] at hl
  linarith

theorem center_add_scalar_debit (H B : Matrix n n ℂ) (r : ℝ) :
    KSDebitCenter.center H (B + r • (1 : Matrix n n ℂ)) =
      KSDebitCenter.center H B - r • (1 : Matrix (n ⊕ n) (n ⊕ n) ℂ) := by
  ext i j
  cases i <;> cases j <;>
    simp [KSDebitCenter.center, KSSpinSource.doubled, signedLift, Matrix.fromBlocks,
      Matrix.one_apply, sub_add_eq_sub_sub]

def potential (H B : Matrix n n ℂ) (v : ι → n → ℂ) (c : ι → ℝ) (θ : ℝ) : ℝ :=
  ownerPotential (KSDebitCenter.center H B) (KSSpinSource.family (fun i => KSRankOne.atom (v i)))
    (KSSpinSource.coefficientCovariance c) θ


theorem potential_add_scalar_debit [Nonempty n]
    (H B : Matrix n n ℂ) (v : ι → n → ℂ) {c : ι → ℝ} (hc : ∀ i, 0 ≤ c i)
    {θ : ℝ} (hθ : 0 < θ) (r : ℝ) :
    potential H (B + r • (1 : Matrix n n ℂ)) v c θ = potential H B v c θ - r := by
  unfold potential
  rw [center_add_scalar_debit]
  exact ownerPotential_sub_scalar _ _
    (KSSpinSource.family_isHermitian _ (fun i => KSRankOne.atom_isHermitian (v i)))
    (KSSpinSource.coefficientCovariance_posSemidef hc) hθ r

/-- Numerical acceptance and its two value errors imply the claimed true
decrease after the algorithm adds the scalar debit. -/
theorem accepted_retirement_decreases {old queried reportedOld reportedQueried η : ℝ}
    (hold : |reportedOld - old| ≤ η / 8)
    (hquery : |reportedQueried - queried| ≤ η / 8)
    (haccept : reportedQueried - reportedOld ≤ η / 2) :
    queried - η ≤ old - η / 4 := by
  rcases abs_le.mp hold with ⟨hol, hou⟩
  rcases abs_le.mp hquery with ⟨hql, hqu⟩
  linarith

/-- A genuine nonincreasing query is necessarily detected by the finite
numerical test. The test needs value estimates, not a transport computation. -/
theorem nonincreasing_query_is_accepted {old queried reportedOld reportedQueried η : ℝ}
    (hη : 0 ≤ η) (hold : |reportedOld - old| ≤ η / 8)
    (hquery : |reportedQueried - queried| ≤ η / 8)
    (hsafe : queried ≤ old) : reportedQueried - reportedOld ≤ η / 2 := by
  rcases abs_le.mp hold with ⟨hol, hou⟩
  rcases abs_le.mp hquery with ⟨hql, hqu⟩
  linarith

/-- Monotonicity in the center is for the actual density maximization. -/
theorem ownerPotential_mono_center [Nonempty n]
    {H K : Matrix n n ℂ} (hHK : H ≤ K)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) {θ : ℝ} (hθ : 0 < θ) :
    ownerPotential H A C θ ≤ ownerPotential K A C θ := by
  obtain ⟨S, hS, _, hp, _⟩ := exists_ownerOptimizer H A hA hC hθ
  obtain ⟨T, hT, _, hp', hmax'⟩ := exists_ownerOptimizer K A hA hC hθ
  have hd := realTrace_mul_nonneg (Matrix.le_iff.mp hHK) hS.1
  rw [Matrix.sub_mul, realTrace_sub] at hd
  have ho : ownerObjective H A C θ S ≤ ownerObjective K A C θ S := by
    unfold ownerObjective
    linarith
  rw [hp, hp']
  exact ho.trans (hmax' S hS)

theorem potential_le_zero_debit [Nonempty n]
    (H : Matrix n n ℂ) {B : Matrix n n ℂ} (hB : B.PosSemidef)
    (v : ι → n → ℂ) {c : ι → ℝ} (hc : ∀ i, 0 ≤ c i)
    {θ : ℝ} (hθ : 0 < θ) :
    potential H B v c θ ≤ potential H 0 v c θ := by
  apply ownerPotential_mono_center _ _
    (KSSpinSource.family_isHermitian _ (fun i => KSRankOne.atom_isHermitian (v i)))
    (KSSpinSource.coefficientCovariance_posSemidef hc) hθ
  rw [KSDebitCenter.center_zero_debit]
  exact sub_le_self _ (KSSpinSource.doubled_posSemidef hB).nonneg

/-- The actual optimized potential controls the physical signing matrix,
with precisely the scalar upper bound on the accumulated debit. -/
theorem norm_le_potential_add [Nonempty n]
    {H B : Matrix n n ℂ} (hH : H.IsHermitian) {r : ℝ}
    (hB : B ≤ r • (1 : Matrix n n ℂ))
    (v : ι → n → ℂ) {c : ι → ℝ} (hc : ∀ i, 0 ≤ c i)
    {θ : ℝ} (hθ : 0 < θ) : ‖H‖ ≤ potential H B v c θ + r := by
  have hA := KSSpinSource.family_isHermitian
    (fun i => KSRankOne.atom (v i)) (fun i => KSRankOne.atom_isHermitian (v i))
  have hC := KSSpinSource.coefficientCovariance_posSemidef hc
  have hl := ks_norm_le_signedLift_ownerPotential hH _ hA hC hθ.le
  have hd := KSSpinSource.doubled_mono hB
  have hm : potential H (r • (1 : Matrix n n ℂ)) v c θ ≤ potential H B v c θ := by
    apply ownerPotential_mono_center _ _ hA hC hθ
    exact sub_le_sub_left hd _
  have hs := potential_add_scalar_debit H 0 v hc hθ r
  rw [zero_add] at hs
  rw [hs] at hm
  have hz : potential H 0 v c θ =
      ownerPotential (signedLift H) (KSSpinSource.family (fun i => KSRankOne.atom (v i)))
        (KSSpinSource.coefficientCovariance c) θ := by
    simp only [potential, KSDebitCenter.center_zero_debit]
  rw [hz] at hm
  linarith

end MatrixSpencer.KSDebitPotential
