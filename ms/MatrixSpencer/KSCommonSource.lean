import MatrixSpencer.KSSignSymmetry

/-!
# Exact relation between the old signed pencil and independent sign sources

The two channels differ on off-diagonal inputs. Their optimized potentials
agree because both actual optimizing densities are block diagonal. This
module proves equality rather than identifying the distinct source maps.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix

noncomputable section
namespace MatrixSpencer.KSCommonSource

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n]

def family (A : ι → Matrix n n ℂ) (i : ι) := signedLift (A i)

def coefficientCovariance (c : ι → ℝ) : Matrix ι ι ℝ := Matrix.diagonal c

theorem coefficientCovariance_posSemidef {c : ι → ℝ} (hc : ∀ i, 0 ≤ c i) :
    (coefficientCovariance c).PosSemidef := Matrix.posSemidef_diagonal_iff.mpr hc

theorem family_isHermitian (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) (i : ι) :
    (family A i).IsHermitian := signedLift_isHermitian (hA i)

theorem source_eq_sum (A : ι → Matrix n n ℂ) (c : ι → ℝ)
    (X : Matrix (n ⊕ n) (n ⊕ n) ℂ) :
    covarianceSource (family A) (coefficientCovariance c) X =
      ∑ i, c i • (signedLift (A i) * X * signedLift (A i)) := by
  simp only [covarianceSource, coefficientCovariance, Matrix.diagonal_apply,
    ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true, family]

theorem source_eq_independent_of_blockDiagonal (A : ι → Matrix n n ℂ) (c : ι → ℝ)
    (X Y : Matrix n n ℂ) :
    covarianceSource (family A) (coefficientCovariance c) (Matrix.fromBlocks X 0 0 Y) =
      covarianceSource (KSIndependentSource.family A) (KSIndependentSource.coefficientCovariance c)
        (Matrix.fromBlocks X 0 0 Y) := by
  rw [source_eq_sum, KSIndependentSource.source_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  simp only [signedLift, leftDensity, rightDensity, Matrix.fromBlocks_multiply,
    Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
  ext a b
  cases a <;> cases b <;> simp [Matrix.fromBlocks, Matrix.add_apply]

theorem optimizer_blockDiagonal (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) {c : ι → ℝ} (hc : ∀ i, 0 ≤ c i)
    {θ : ℝ} (hθ : 0 < θ) {S : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hS : S ∈ densitySet)
    (hmax : ∀ T ∈ densitySet,
      ownerObjective (signedLift H) (family A) (coefficientCovariance c) θ T ≤
        ownerObjective (signedLift H) (family A) (coefficientCovariance c) θ S) :
    S = Matrix.fromBlocks S.toBlocks₁₁ 0 0 S.toBlocks₂₂ := by
  apply KSSignSymmetry.sign_fixed_blockDiagonal
  exact KSSignSymmetry.optimizer_conjugate_eq KSSignSymmetry.signMatrix_isHermitian
    KSSignSymmetry.signMatrix_sq (KSSignSymmetry.signMatrix_commute_signedLift H)
    (family A) (family_isHermitian A hA)
    (fun i => KSSignSymmetry.signMatrix_commute_signedLift (A i))
    (coefficientCovariance_posSemidef hc) hθ hS hmax

theorem independent_optimizer_blockDiagonal (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) {c : ι → ℝ} (hc : ∀ i, 0 ≤ c i)
    {θ : ℝ} (hθ : 0 < θ) {S : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hS : S ∈ densitySet)
    (hmax : ∀ T ∈ densitySet,
      ownerObjective (signedLift H) (KSIndependentSource.family A)
        (KSIndependentSource.coefficientCovariance c) θ T ≤
      ownerObjective (signedLift H) (KSIndependentSource.family A)
        (KSIndependentSource.coefficientCovariance c) θ S) :
    S = Matrix.fromBlocks S.toBlocks₁₁ 0 0 S.toBlocks₂₂ := by
  apply KSSignSymmetry.sign_fixed_blockDiagonal
  exact KSSignSymmetry.optimizer_conjugate_eq KSSignSymmetry.signMatrix_isHermitian
    KSSignSymmetry.signMatrix_sq (KSSignSymmetry.signMatrix_commute_signedLift H)
    (KSIndependentSource.family A) (KSIndependentSource.family_isHermitian A hA)
    (KSSignSymmetry.signMatrix_commute_independent A)
    (KSIndependentSource.coefficientCovariance_posSemidef hc) hθ hS hmax

theorem objective_eq_independent_of_blockDiagonal (H : Matrix n n ℂ)
    (A : ι → Matrix n n ℂ) (c : ι → ℝ) (θ : ℝ) (X Y : Matrix n n ℂ) :
    ownerObjective (signedLift H) (family A) (coefficientCovariance c) θ
      (Matrix.fromBlocks X 0 0 Y) =
    ownerObjective (signedLift H) (KSIndependentSource.family A)
      (KSIndependentSource.coefficientCovariance c) θ (Matrix.fromBlocks X 0 0 Y) := by
  simp only [ownerObjective, source_eq_independent_of_blockDiagonal]

theorem potential_eq_independent [Nonempty n] (H : Matrix n n ℂ)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {c : ι → ℝ} (hc : ∀ i, 0 ≤ c i) {θ : ℝ} (hθ : 0 < θ) :
    ownerPotential (signedLift H) (family A) (coefficientCovariance c) θ =
      ownerPotential (signedLift H) (KSIndependentSource.family A)
        (KSIndependentSource.coefficientCovariance c) θ := by
  obtain ⟨S, hS, _, hvalS, hmaxS⟩ := exists_ownerOptimizer (signedLift H) (family A)
    (family_isHermitian A hA) (coefficientCovariance_posSemidef hc) hθ
  obtain ⟨T, hT, _, hvalT, hmaxT⟩ := exists_ownerOptimizer (signedLift H) (KSIndependentSource.family A)
    (KSIndependentSource.family_isHermitian A hA)
    (KSIndependentSource.coefficientCovariance_posSemidef hc) hθ
  have hs := optimizer_blockDiagonal H A hA hc hθ hS hmaxS
  have ht := independent_optimizer_blockDiagonal H A hA hc hθ hT hmaxT
  have hSeq : ownerObjective (signedLift H) (family A) (coefficientCovariance c) θ S =
      ownerObjective (signedLift H) (KSIndependentSource.family A)
        (KSIndependentSource.coefficientCovariance c) θ S := by
    rw [hs]
    exact objective_eq_independent_of_blockDiagonal H A c θ _ _
  have hTeq : ownerObjective (signedLift H) (family A) (coefficientCovariance c) θ T =
      ownerObjective (signedLift H) (KSIndependentSource.family A)
        (KSIndependentSource.coefficientCovariance c) θ T := by
    rw [ht]
    exact objective_eq_independent_of_blockDiagonal H A c θ _ _
  rw [hvalS, hvalT]
  exact le_antisymm (hSeq ▸ hmaxT S hS) (hTeq ▸ hmaxS T hT)

end MatrixSpencer.KSCommonSource
