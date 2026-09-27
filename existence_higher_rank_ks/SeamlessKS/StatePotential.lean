import SeamlessKS.State
import SeamlessKS.LocalComparison

/-! The account-free potential and a proof-only scalar allowance for boundary rounding. -/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace SeamlessKS.StatePotential
open MatrixSpencer SeamlessKS.State

variable {N : ℕ} {ρ : ℝ} {n : Type*} [Fintype n] [DecidableEq n]
local instance {k : Type*} [Fintype k] [DecidableEq k] : CStarAlgebra (Matrix k k ℂ) := {}

def signedSum (v : Fin N → n → ℂ) (x : Fin N → ℝ) : Matrix n n ℂ :=
  ∑ i, x i • KSRankOne.atom (v i)

/-- Compatibility with generic fixed-center analytic lemmas: the actual walk
always uses zero here. This is not stored state or an error matrix. -/
def debit (_v : Fin N → n → ℂ) (_s : CubeState N ρ) : Matrix n n ℂ := 0

def potential (v : Fin N → n → ℂ) (θ ζ : ℝ) (s : CubeState N ρ) : ℝ :=
  KSDebitPotential.potential (signedSum v s.coeff) (debit v s) v
    (SourceTransport.smoothWeights ζ s.coeff) θ

theorem signedSum_isHermitian (v : Fin N → n → ℂ) (x : Fin N → ℝ) :
    (signedSum v x).IsHermitian := by
  change (∑ i, x i • KSRankOne.atom (v i))ᴴ = ∑ i, x i • KSRankOne.atom (v i)
  simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, star_trivial,
    (KSRankOne.atom_isHermitian _).eq]

theorem debit_bounds (v : Fin N → n → ℂ) (_hparseval : ∑ i, KSRankOne.atom (v i)=1)
    (s : CubeState N ρ) : (debit v s).PosSemidef ∧ debit v s≤ρ • (1:Matrix n n ℂ) := by
  constructor
  · exact Matrix.PosSemidef.zero
  · exact smul_nonneg s.rho_nonneg zero_le_one

theorem norm_le_potential [Nonempty n]
    (v : Fin N → n → ℂ) {θ : ℝ} (hθ : 0 < θ) (ζ : ℝ) (s : CubeState N ρ) :
    ‖signedSum v s.coeff‖≤potential v θ ζ s := by
  have hh := KSDebitPotential.norm_le_potential_add (signedSum_isHermitian v s.coeff)
    (B := (0 : Matrix n n ℂ)) (r := 0) (by simp) v
    (c := SourceTransport.smoothWeights ζ s.coeff)
    (fun i => Source.weight_nonneg (by norm_num) (coeff_abs_le s i)) hθ
  simpa only [add_zero] using hh

theorem norm_le_potential_add [Nonempty n]
    (v : Fin N → n → ℂ) (_hparseval : ∑ i, KSRankOne.atom (v i)=1)
    {θ : ℝ} (hθ : 0 < θ) (ζ : ℝ) (s : CubeState N ρ) :
    ‖signedSum v s.coeff‖≤potential v θ ζ s+ρ :=
  (norm_le_potential v hθ ζ s).trans (le_add_of_nonneg_right s.rho_nonneg)

theorem signedSum_difference (v : Fin N → n → ℂ) (x y : Fin N → ℝ) :
    signedSum v y=signedSum v x+∑ i, (y i-x i) • KSRankOne.atom (v i) := by
  simp only [signedSum,sub_smul,Finset.sum_sub_distrib]
  abel

/-- A proof-only allowance for labels that have not yet reached an endpoint.
The algorithm neither stores nor evaluates this expression. -/
def reserve (v : Fin N → n → ℂ) (s : CubeState N ρ) : ℝ :=
  ∑ i, if |s.coeff i| < 1 then ρ * ‖KSRankOne.atom (v i)‖ else 0

/-- The scalar account is used only for the finite probability argument. -/
def account (v : Fin N → n → ℂ) (θ ζ : ℝ) (s : CubeState N ρ) : ℝ :=
  potential v θ ζ s + reserve v s

theorem reserve_nonneg (v : Fin N → n → ℂ) (s : CubeState N ρ) : 0 ≤ reserve v s := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact mul_nonneg s.rho_nonneg (norm_nonneg _)
  · exact le_rfl

theorem reserve_le (v : Fin N → n → ℂ) (s : CubeState N ρ) :
    reserve v s ≤ ρ * ∑ i, ‖KSRankOne.atom (v i)‖ := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  split_ifs
  · exact le_rfl
  · exact mul_nonneg s.rho_nonneg (norm_nonneg _)

theorem reserve_mono (v : Fin N → n → ℂ) (s t : CubeState N ρ)
    (hfrozen : ∀ i, |s.coeff i|=1 → t.coeff i=s.coeff i) :
    reserve v t ≤ reserve v s := by
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : |s.coeff i| < 1
  · simp only [if_pos hi]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg s.rho_nonneg (norm_nonneg _)
  · have he : |s.coeff i|=1 := le_antisymm (coeff_abs_le s i) (not_lt.mp hi)
    simp only [hfrozen i he, if_neg hi, le_refl]

theorem norm_le_account [Nonempty n]
    (v : Fin N → n → ℂ) {θ : ℝ} (hθ : 0 < θ) (ζ : ℝ) (s : CubeState N ρ) :
    ‖signedSum v s.coeff‖≤account v θ ζ s :=
  (norm_le_potential v hθ ζ s).trans (le_add_of_nonneg_right (reserve_nonneg v s))

/-- A temporary comparison matrix can be bounded by a scalar without becoming
part of the state or of any potential query. -/
theorem zero_debit_le_add [Nonempty n] (H D : Matrix n n ℂ)
    (v : Fin N → n → ℂ) {c : Fin N → ℝ} (hc : ∀ i, 0 ≤ c i)
    {θ r : ℝ} (hθ : 0 < θ) (hD : D ≤ r • (1 : Matrix n n ℂ)) :
    KSDebitPotential.potential H 0 v c θ ≤ KSDebitPotential.potential H D v c θ+r := by
  have hm : KSDebitPotential.potential H (r • (1 : Matrix n n ℂ)) v c θ ≤
      KSDebitPotential.potential H D v c θ := by
    apply KSDebitPotential.ownerPotential_mono_center _ _
      (KSSpinSource.family_isHermitian _ (fun i => KSRankOne.atom_isHermitian (v i)))
      (KSSpinSource.coefficientCovariance_posSemidef hc) hθ
    exact sub_le_sub_left (KSSpinSource.doubled_mono hD) _
  have hs := KSDebitPotential.potential_add_scalar_debit H 0 v hc hθ r
  rw [zero_add] at hs
  rw [hs] at hm
  linarith

theorem prepare_potential_add_cost [Nonempty n] (hρ : 0 ≤ ρ) (v : Fin N → n → ℂ)
    {θ : ℝ} (hθ : 0 < θ) (ζ : ℝ) (s : CubeState N ρ) :
    potential v θ ζ (prepare hρ s).toCubeState ≤ potential v θ ζ s +
      ∑ i, snapDistance s i * ‖KSRankOne.atom (v i)‖ := by
  let D : Matrix n n ℂ := ∑ i, snapDistance s i • KSRankOne.atom (v i)
  have hD : D ≤ (∑ i, snapDistance s i * ‖KSRankOne.atom (v i)‖) • (1 : Matrix n n ℂ) := by
    calc
      D ≤ ∑ i, snapDistance s i • (‖KSRankOne.atom (v i)‖ • (1 : Matrix n n ℂ)) := by
        apply Finset.sum_le_sum
        intro i _
        apply smul_le_smul_of_nonneg_left _ (snapDistance_nonneg s i)
        simpa only [Algebra.algebraMap_eq_smul_one] using
          (CStarAlgebra.norm_le_iff_le_algebraMap _ (norm_nonneg _)
            (KSRankOne.atom_posSemidef (v i)).nonneg).mp le_rfl
      _ = _ := by simp only [smul_smul, Finset.sum_smul]
  have hcomp := LocalComparison.simultaneous_boundary_snap (signedSum v s.coeff) 0 v
    s.coeff (prepare hρ s).coeff (coeff_abs_le s) (by
      intro i
      by_cases hb : 1-|s.coeff i|≤ρ
      · right
        simp only [prepare,KSCubePreparation.snap,if_pos hb,
          KSCubePreparation.endpoint_abs (by norm_num : (0:ℝ)≤1)]
      · left
        simp only [prepare,KSCubePreparation.snap,if_neg hb]) ζ hθ
  rw [← signedSum_difference v s.coeff (prepare hρ s).coeff, zero_add] at hcomp
  have hzero := zero_debit_le_add (signedSum v (prepare hρ s).coeff) D v
    (c := SourceTransport.smoothWeights ζ (prepare hρ s).coeff) (fun i => Source.weight_nonneg (by norm_num) (coeff_abs_le (prepare hρ s).toCubeState i)) hθ hD
  change potential v θ ζ (prepare hρ s).toCubeState ≤ _ at hzero
  change KSDebitPotential.potential (signedSum v (prepare hρ s).coeff) D v
      (SourceTransport.smoothWeights ζ (prepare hρ s).coeff) θ ≤ potential v θ ζ s at hcomp
  linarith

theorem prepare_reserve_cost (hρ : 0 ≤ ρ) (v : Fin N → n → ℂ) (s : CubeState N ρ) :
    reserve v (prepare hρ s).toCubeState + ∑ i, snapDistance s i * ‖KSRankOne.atom (v i)‖ ≤
      reserve v s := by
  rw [reserve, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : |s.coeff i| < 1
  · by_cases hj : |(prepare hρ s).coeff i| < 1
    · obtain ⟨he, hz⟩ := snapDistance_live s i hj
      simp only [if_pos hi, if_pos hj, hz, zero_mul, add_zero, le_refl]
    · simp only [if_pos hi, if_neg hj, zero_add]
      exact mul_le_mul_of_nonneg_right (snapDistance_le hρ s i) (norm_nonneg _)
  · have he : |s.coeff i|=1 := le_antisymm (coeff_abs_le s i) (not_lt.mp hi)
    rw [show (prepare hρ s).coeff i=s.coeff i from prepare_preserves_frozen hρ s i he]
    simp only [if_neg hi, snapDistance_frozen s i he, zero_mul, add_zero, le_refl]

theorem prepare_account_nonincreasing [Nonempty n] (hρ : 0 ≤ ρ) (v : Fin N → n → ℂ)
    {θ : ℝ} (hθ : 0 < θ) (ζ : ℝ) (s : CubeState N ρ) :
    account v θ ζ (prepare hρ s).toCubeState ≤ account v θ ζ s := by
  have hp := prepare_potential_add_cost hρ v hθ ζ s
  have hr := prepare_reserve_cost hρ v s
  unfold account
  linarith

end SeamlessKS.StatePotential
