import SeamlessKS.Parameters
import MatrixSpencer.KSOptimizerFloor
import MatrixSpencer.DensityDomain

/-!
# Actual cube/debit bounds and the full optimizer floor

The generic source statements allow a sub-Parseval live family and arbitrary
weights in [0,128]. The full-density optimizer floor is obtained from the
proved stationarity theorem and an actual potential cap, independent of a
positive source eigenvalue. No floor or norm cap is supplied to the concrete
Parseval-state specialization.
-/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace SeamlessKS.StateBounds
open MatrixSpencer

variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
local instance {k : Type*} [Fintype k] [DecidableEq k] : CStarAlgebra (Matrix k k ℂ) := {}

def signedSum (v : ι → n → ℂ) (x : ι → ℝ) : Matrix n n ℂ :=
  ∑ i, x i • KSRankOne.atom (v i)

omit [DecidableEq ι] in
theorem signedSum_isHermitian (v : ι → n → ℂ) (x : ι → ℝ) :
    (signedSum v x).IsHermitian := by
  change (∑ i, x i • KSRankOne.atom (v i))ᴴ = ∑ i, x i • KSRankOne.atom (v i)
  simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, star_trivial,
    fun i => (KSRankOne.atom_isHermitian (v i)).eq]

omit [DecidableEq ι] in
theorem subparseval_atom_norm_le_one (v : ι → n → ℂ)
    (hp : (∑ i, KSRankOne.atom (v i)) ≤ 1) (i : ι) :
    ‖KSRankOne.atom (v i)‖ ≤ 1 := by
  have hle : KSRankOne.atom (v i) ≤ 1 :=
    (Finset.single_le_sum
      (fun j (_ : j ∈ Finset.univ) => (KSRankOne.atom_posSemidef (v j)).nonneg)
      (Finset.mem_univ i)).trans hp
  apply (CStarAlgebra.norm_le_iff_le_algebraMap _ zero_le_one
    (KSRankOne.atom_posSemidef (v i)).nonneg).mpr
  simpa using hle

omit [DecidableEq ι] in
theorem subparseval_square_sum_le_one (v : ι → n → ℂ)
    (hp : (∑ i, KSRankOne.atom (v i)) ≤ 1) :
    (∑ i, KSRankOne.atom (v i)*KSRankOne.atom (v i)) ≤ 1 := by
  calc
    _ = ∑ i, realTrace (KSRankOne.atom (v i)) • KSRankOne.atom (v i) := by
      simp only [KSRankOne.atom_sq_real]
    _ ≤ ∑ i, (1:ℝ) • KSRankOne.atom (v i) := by
      apply Finset.sum_le_sum
      intro i _
      apply smul_le_smul_of_nonneg_right
      · simpa only [KSRankOne.atom_norm] using subparseval_atom_norm_le_one v hp i
      · exact (KSRankOne.atom_posSemidef (v i)).nonneg
    _ = ∑ i, KSRankOne.atom (v i) := by simp
    _ ≤ 1 := hp

omit [DecidableEq ι] in
theorem signedSum_le_one (v : ι → n → ℂ)
    (hp : (∑ i, KSRankOne.atom (v i)) ≤ 1) (x : ι → ℝ)
    (hx : ∀ i, |x i| ≤ 1) : signedSum v x ≤ 1 := by
  calc
    _ ≤ ∑ i, (1:ℝ) • KSRankOne.atom (v i) := by
      apply Finset.sum_le_sum
      intro i _
      exact smul_le_smul_of_nonneg_right (abs_le.mp (hx i)).2
        (KSRankOne.atom_posSemidef (v i)).nonneg
    _ = ∑ i, KSRankOne.atom (v i) := by simp
    _ ≤ 1 := hp

omit [DecidableEq ι] in
theorem neg_one_le_signedSum (v : ι → n → ℂ)
    (hp : (∑ i, KSRankOne.atom (v i)) ≤ 1) (x : ι → ℝ)
    (hx : ∀ i, |x i| ≤ 1) : -(1 : Matrix n n ℂ) ≤ signedSum v x := by
  have hh := signedSum_le_one v hp (fun i => -x i) (by intro i; simpa using hx i)
  have he : signedSum v (fun i => -x i) = -signedSum v x := by
    simp [signedSum, Finset.sum_neg_distrib]
  rw [he] at hh
  simpa only [neg_neg] using neg_le_neg hh

omit [DecidableEq ι] in
theorem signedSum_norm_le_one [Nonempty n] (v : ι → n → ℂ)
    (hp : (∑ i, KSRankOne.atom (v i)) ≤ 1) (x : ι → ℝ)
    (hx : ∀ i, |x i| ≤ 1) : ‖signedSum v x‖ ≤ 1 := by
  apply hermitian_norm_le_of_order (signedSum_isHermitian v x)
  · simpa only [one_smul] using neg_one_le_signedSum v hp x hx
  · simpa only [one_smul] using signedSum_le_one v hp x hx

theorem debit_norm_le {B : Matrix n n ℂ} (hB : B.PosSemidef)
    {rho : ℝ} (hrho : 0 ≤ rho) (hcap : B ≤ rho • (1 : Matrix n n ℂ)) : ‖B‖ ≤ rho := by
  apply (CStarAlgebra.norm_le_iff_le_algebraMap _ hrho hB.nonneg).mpr
  simpa only [Algebra.algebraMap_eq_smul_one] using hcap

theorem doubled_debit_norm_le {B : Matrix n n ℂ} (hB : B.PosSemidef)
    {rho : ℝ} (hrho : 0 ≤ rho) (hcap : B ≤ rho • (1 : Matrix n n ℂ)) :
    ‖KSSpinSource.doubled B‖ ≤ rho := by
  apply (CStarAlgebra.norm_le_iff_le_algebraMap _ hrho
    (KSSpinSource.doubled_posSemidef hB).nonneg).mpr
  have hh := KSSpinSource.doubled_mono hcap
  simpa only [KSSpinSource.doubled_smul, KSSpinSource.doubled_one,
    Algebra.algebraMap_eq_smul_one] using hh

omit [DecidableEq ι] in
theorem center_norm_le [Nonempty n] (v : ι → n → ℂ)
    (hp : (∑ i, KSRankOne.atom (v i)) ≤ 1) (x : ι → ℝ)
    (hx : ∀ i, |x i| ≤ 1) {B : Matrix n n ℂ} (hB : B.PosSemidef)
    {rho : ℝ} (hrho : 0 ≤ rho) (hcap : B ≤ rho • (1 : Matrix n n ℂ)) :
    ‖KSDebitCenter.center (signedSum v x) B‖ ≤ 1+rho := by
  have hs := signedSum_norm_le_one v hp x hx
  have hb := doubled_debit_norm_le hB hrho hcap
  unfold KSDebitCenter.center
  have hn := norm_sub_le (signedLift (signedSum v x)) (KSSpinSource.doubled B)
  rw [signedLift_norm (signedSum_isHermitian v x)] at hn
  linarith

/-- The source bound for a live subfamily, without a source eigenvalue. -/
theorem subparseval_source_variance_le (v : ι → n → ℂ)
    (hp : (∑ i, KSRankOne.atom (v i)) ≤ 1) (c : ι → ℝ)
    (hc : ∀ i, c i ≤ 128) :
    covarianceSource (KSSpinSource.family (fun i => KSRankOne.atom (v i)))
      (KSSpinSource.coefficientCovariance c) 1 ≤
        (256:ℝ) • (1 : Matrix (n ⊕ n) (n ⊕ n) ℂ) := by
  calc
    _ ≤ covarianceSource (KSSpinSource.family (fun i => KSRankOne.atom (v i)))
        (KSSpinSource.coefficientCovariance (fun _ => 128)) 1 := by
      rw [KSSpinSource.source_identity, KSSpinSource.source_identity]
      apply Finset.sum_le_sum
      intro i _
      apply smul_le_smul_of_nonneg_right (by linarith [hc i])
      apply Matrix.PosSemidef.nonneg
      apply KSSpinSource.doubled_posSemidef
      simpa only [pow_two] using (KSRankOne.atom_posSemidef (v i)).pow 2
    _ = (256:ℝ) • KSSpinSource.doubled
        (∑ i, KSRankOne.atom (v i)*KSRankOne.atom (v i)) := by
      rw [KSSpinSource.source_identity_constant]
      norm_num
    _ ≤ _ := by
      have hh := smul_le_smul_of_nonneg_left
        (KSSpinSource.doubled_mono (subparseval_square_sum_le_one v hp))
        (by norm_num : (0:ℝ) ≤ 256)
      simpa only [KSSpinSource.doubled_one] using hh

/-- Generic value cap at a real line point with center norm at most two. -/
theorem ownerPotential_le_thirtysix [Nonempty n]
    (v : ι → n → ℂ) (hp : (∑ i, KSRankOne.atom (v i)) ≤ 1)
    (c : ι → ℝ) (hc0 : ∀ i, 0 ≤ c i) (hc128 : ∀ i, c i ≤ 128)
    (M : Matrix (n ⊕ n) (n ⊕ n) ℂ) (hM : M.IsHermitian) (hMnorm : ‖M‖ ≤ 2)
    {theta : ℝ} (htheta : 0 < theta)
    (hreg : theta*Real.sqrt (Fintype.card (n ⊕ n) : ℝ) ≤ 1) :
    ownerPotential M (KSSpinSource.family (fun i => KSRankOne.atom (v i)))
      (KSSpinSource.coefficientCovariance c) theta ≤ 36 := by
  have hh := ks_ownerPotential_le_variance hM
    (KSSpinSource.family (fun i => KSRankOne.atom (v i)))
    (KSSpinSource.family_isHermitian _ (fun i => KSRankOne.atom_isHermitian _))
    (KSSpinSource.coefficientCovariance_posSemidef hc0) htheta.le
    (subparseval_source_variance_le v hp c hc128)
  have hsqrt : Real.sqrt (256:ℝ) = 16 := by norm_num
  rw [hsqrt] at hh
  linarith

/-- Canonical FULL density floor for an arbitrary supported source.
Faithfulness and stationarity are discharged by the general optimizer theorem. -/
theorem optimizer_floor [Nonempty n]
    (v : ι → n → ℂ) (hp : (∑ i, KSRankOne.atom (v i)) ≤ 1)
    (c : ι → ℝ) (hc0 : ∀ i, 0 ≤ c i) (hc128 : ∀ i, c i ≤ 128)
    (M : Matrix (n ⊕ n) (n ⊕ n) ℂ) (hM : M.IsHermitian) (hMnorm : ‖M‖ ≤ 2)
    {theta : ℝ} (htheta : 0 < theta)
    (hreg : theta*Real.sqrt (Fintype.card (n ⊕ n) : ℝ) ≤ 1) :
    (theta/40)^2 • (1 : Matrix (n ⊕ n) (n ⊕ n) ℂ) ≤
      densityOptimizer M (covarianceKraus
        (KSSpinSource.family (fun i => KSRankOne.atom (v i)))
        (KSSpinSource.coefficientCovariance c)) theta := by
  have hA := KSSpinSource.family_isHermitian (fun i => KSRankOne.atom (v i))
    (fun i => KSRankOne.atom_isHermitian (v i))
  have hC := KSSpinSource.coefficientCovariance_posSemidef hc0
  apply KSOptimizerFloor.densityOptimizer_floor_of_potential_cap M hM _ htheta
    (by norm_num : (0:ℝ) < 40)
  rw [← ownerPotential_eq_densityPotential M _ hA hC theta]
  have hh := ownerPotential_le_thirtysix v hp c hc0 hc128 M hM hMnorm htheta hreg
  linarith

/-- Every actual canonical full-density optimizer also has norm at most one. -/
theorem optimizer_norm_le_one [Nonempty n]
    (M : Matrix (n ⊕ n) (n ⊕ n) ℂ) (v : ι → n → ℂ)
    (c : ι → ℝ) (theta : ℝ) :
    ‖densityOptimizer M (covarianceKraus
      (KSSpinSource.family (fun i => KSRankOne.atom (v i)))
      (KSSpinSource.coefficientCovariance c)) theta‖ ≤ 1 :=
  density_norm_le_one (densityOptimizer_mem _ _ _)

section OriginalInput
variable {N d : ℕ}

/-- The original-input choice of theta meets the generic regularizer budget. -/
theorem original_regularizer_budget (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑ i, KSRankOne.atom (v i)) = 1) :
    Input.theta v * Real.sqrt (Fintype.card (Fin d ⊕ Fin d) : ℝ) ≤ 1 := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  have hh := ksRegularizerScale_budget (n := Fin d) (Input.epsilon v)
  rw [← Input.theta_eq_regularizer v] at hh
  have hu := Input.delta_le_one v hp
  dsimp only [Input.delta] at hu
  linarith

theorem actual_center_norm_le_two (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑ i, KSRankOne.atom (v i)) = 1) (x : Fin N → ℝ)
    (hx : ∀ i, |x i| ≤ 1) {B : Matrix (Fin d) (Fin d) ℂ}
    (hB : B.PosSemidef) (hcap : B ≤ Parameters.rho N • (1 : Matrix (Fin d) (Fin d) ℂ)) :
    ‖KSDebitCenter.center (signedSum v x) B‖ ≤ 2 := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  have hh := center_norm_le v hp.le x hx hB (Parameters.rho_pos (Input.labels_pos v hd hp)).le hcap
  have hr := Parameters.rho_le_one v hd hp
  linarith

theorem actual_optimizer_floor [Nonempty (Fin d)] (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑ i, KSRankOne.atom (v i)) = 1) (x : Fin N → ℝ)
    (hx : ∀ i, |x i| ≤ 1) {B : Matrix (Fin d) (Fin d) ℂ}
    (hB : B.PosSemidef) (hcap : B ≤ Parameters.rho N • (1 : Matrix (Fin d) (Fin d) ℂ))
    (c : Fin N → ℝ) (hc0 : ∀ i, 0 ≤ c i) (hc128 : ∀ i, c i ≤ 128) :
    Parameters.densityFloor v • (1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℂ) ≤
      densityOptimizer (KSDebitCenter.center (signedSum v x) B)
        (covarianceKraus (KSSpinSource.family (fun i => KSRankOne.atom (v i)))
          (KSSpinSource.coefficientCovariance c)) (Input.theta v) := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  exact optimizer_floor v hp.le c hc0 hc128 _
    (KSDebitCenter.center_isHermitian (signedSum_isHermitian v x) hB.isHermitian)
    (actual_center_norm_le_two v hd hp x hx hB hcap)
    (Input.theta_pos v hd hp) (original_regularizer_budget v hd hp)

end OriginalInput
end SeamlessKS.StateBounds
