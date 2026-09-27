import MatrixSpencer.KSDebitActualRetirement

/-!
# Debit-assisted retirement with frozen original labels

The existing actual `spinTransport` uses the support of the covariance Kraus
family at the current state. Thus nonnegative owners, including zero frozen
owners, are allowed. Optimizer, support, and transport certificates are all
discharged by the proved actual-retirement theorem.
-/

open Matrix Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSDebitFullRetirement

open KSDebitActualRetirement KSEndpointRetirement KSPotentialModels KSRankOne KSOwnerRetirement

variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n] [Nonempty n]
local instance {k : Type*} [Fintype k] [DecidableEq k] : CStarAlgebra (Matrix k k ℂ) := {}

def fullProbe (M : Matrix (n ⊕ n) (n ⊕ n) ℂ) (v : ι → n → ℂ)
    (c : ι → ℝ) (θ : ℝ) (i : ι) : ℝ :=
  realTrace (KSSpinSource.doubled (atom (v i)) * spinTransport M v c θ)

theorem fullProbe_nonneg
    (M : Matrix (n ⊕ n) (n ⊕ n) ℂ) (v : ι → n → ℂ) (c : ι → ℝ)
    {θ : ℝ} (hθ : 0 < θ) (i : ι) : 0 ≤ fullProbe M v c θ i :=
  realTrace_mul_nonneg (KSSpinSource.doubled_posSemidef (atom_posSemidef (v i)))
    (transportMatrix_posSemidef M _ _ hθ)


theorem retire
    (M : Matrix (n ⊕ n) (n ⊕ n) ℂ) (v : ι → n → ℂ)
    {c : ι → ℝ} (hc : ∀ i, 0 ≤ c i) {θ : ℝ} (hθ : 0 < θ)
    (i : ι) (t δ : ℝ) (hsafe : |t| ≤ c i * fullProbe M v c θ i + δ) :
    queriedValue M v c θ i t δ ≤ value M v c θ := by
  apply owner_retire_of_matrix_le M _ _
    (KSSpinSource.family_isHermitian _ (fun j => atom_isHermitian _))
    (KSSpinSource.coefficientCovariance_posSemidef hc)
    (KSSpinSource.coefficientCovariance_posSemidef (update_zero_nonneg hc i))
    (spin_covariance_delete_le c hc i) hθ
  have hW := transportMatrix_posSemidef M
    (KSSpinSource.family (fun j => atom (v j)))
    (KSSpinSource.coefficientCovariance c) hθ
  rw [spin_source_delete v c i hW.isHermitian]
  have hstep := spin_step_le (atom_posSemidef (v i)) hsafe
  rw [add_smul] at hstep
  have hsum := add_le_add_left (sub_nonpos.mpr hstep)
    (M + covarianceSource (KSSpinSource.family (fun j => atom (v j)))
      (KSSpinSource.coefficientCovariance c) (spinTransport M v c θ))
  simp only [add_zero] at hsum
  convert hsum using 1
  dsimp only [fullProbe, spinTransport, KSSpinLocalState.atoms]
  abel

/-- A rejected nearest-endpoint query gives the exact transport gap, even
when the complete family contains previously frozen owners. -/
theorem rejected_nearest_gap
    (M : Matrix (n ⊕ n) (n ⊕ n) ℂ) (v : ι → n → ℂ)
    {c : ι → ℝ} (hc : ∀ i, 0 ≤ c i) {θ : ℝ} (hθ : 0 < θ)
    (i : ι) {a δ : ℝ} (ha : -1 ≤ a ∧ a ≤ 1)
    (hreject : value M v c θ < queriedValue M v c θ i (nearestSign a - a) δ) :
    c i * fullProbe M v c θ i + δ < 1 - |a| := by
  apply lt_of_not_ge
  intro hs
  have hsafe := retire M v hc hθ i (nearestSign a - a) δ
    (by rwa [nearestSign_distance ha])
  exact (not_lt_of_ge hsafe) hreject

theorem rejected_nearest_margin_and_noSafe
    (M : Matrix (n ⊕ n) (n ⊕ n) ℂ) (v : ι → n → ℂ)
    {c : ι → ℝ} (hc : ∀ i, 0 ≤ c i) {θ : ℝ} (hθ : 0 < θ)
    (i : ι) {a δ : ℝ} (ha : -1 ≤ a ∧ a ≤ 1) (hδ : 0 ≤ δ)
    (hreject : value M v c θ < queriedValue M v c θ i (nearestSign a - a) δ) :
    δ < 1 - |a| ∧ c i * fullProbe M v c θ i < 1 - |a| := by
  have hgap := rejected_nearest_gap M v hc hθ i ha hreject
  have hcq := mul_nonneg (hc i) (fullProbe_nonneg M v c hθ i)
  constructor <;> linarith

/-- Two accurate value reports and a failed numerical acceptance test
imply the true boundary margin and transport no-safe inequality. -/
theorem numerical_rejection_margin_and_noSafe
    (M : Matrix (n ⊕ n) (n ⊕ n) ℂ) (v : ι → n → ℂ)
    {c : ι → ℝ} (hc : ∀ i, 0 ≤ c i) {θ : ℝ} (hθ : 0 < θ)
    (i : ι) {a δ η reportedOld reportedQuery : ℝ} (ha : -1 ≤ a ∧ a ≤ 1)
    (hδ : 0 ≤ δ) (hη : 0 ≤ η)
    (hold : |reportedOld - value M v c θ| ≤ η / 8)
    (hquery : |reportedQuery - queriedValue M v c θ i (nearestSign a - a) δ| ≤ η / 8)
    (hreject : η / 2 < reportedQuery - reportedOld) :
    δ < 1 - |a| ∧ c i * fullProbe M v c θ i < 1 - |a| := by
  apply rejected_nearest_margin_and_noSafe M v hc hθ i ha hδ
  rcases abs_le.mp hold with ⟨hol, hou⟩
  rcases abs_le.mp hquery with ⟨hql, hqu⟩
  linarith

end MatrixSpencer.KSDebitFullRetirement
