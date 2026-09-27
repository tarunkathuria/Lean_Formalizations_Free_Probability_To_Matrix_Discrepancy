import MatrixSpencer.KSSpinSymmetry

/-!
# Sign symmetry with the actual full-cube walk debit

The walk uses the center `signedLift H - doubled B`, so its two diagonal
blocks are `H - B` and `-H - B`.  The debit changes neither the spin source
nor its sign symmetry.  This module proves invariance of the actual density
objective and block diagonality of every actual optimizing density for this
center.  It does not assert a walk, an oracle, or a quantitative step bound.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix

noncomputable section
namespace MatrixSpencer.KSDebitCenter

open KSSignSymmetry

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n]

/-- The PSD physical debit is subtracted from both sign blocks. -/
def center (H B : Matrix n n ℂ) : Matrix (n ⊕ n) (n ⊕ n) ℂ :=
  signedLift H - KSSpinSource.doubled B

omit [Fintype n] [DecidableEq n] in
theorem center_eq_blocks (H B : Matrix n n ℂ) :
    center H B = Matrix.fromBlocks (H - B) 0 0 (-H - B) := by
  ext a b
  cases a <;> cases b <;> simp [center, signedLift, KSSpinSource.doubled]

omit [Fintype n] [DecidableEq n] in
@[simp] theorem center_zero_debit (H : Matrix n n ℂ) : center H 0 = signedLift H := by
  ext a b
  cases a <;> cases b <;> simp [center, signedLift, KSSpinSource.doubled]

theorem center_isHermitian {H B : Matrix n n ℂ}
    (hH : H.IsHermitian) (hB : B.IsHermitian) : (center H B).IsHermitian :=
  (signedLift_isHermitian hH).sub (KSSpinSource.doubled_isHermitian hB)

theorem center_isHermitian_of_posSemidef {H B : Matrix n n ℂ}
    (hH : H.IsHermitian) (hB : B.PosSemidef) : (center H B).IsHermitian :=
  center_isHermitian hH hB.isHermitian

theorem signMatrix_commute_center (H B : Matrix n n ℂ) :
    Commute signMatrix (center H B) :=
  (signMatrix_commute_signedLift H).sub_right (signMatrix_commute_doubled B)

@[simp] theorem conjugate_center (H B : Matrix n n ℂ) :
    conjugate signMatrix (center H B) = center H B :=
  conjugate_eq_of_commute signMatrix_sq (signMatrix_commute_center H B)

/-- Spin-source invariance works for every sign-commuting center, including
the actual debit center. Hermitian symmetry is not needed for this identity. -/
theorem objective_sign_invariant_of_commute (M : Matrix (n ⊕ n) (n ⊕ n) ℂ)
    (hM : Commute signMatrix M) (v : ι → n → ℂ)
    {c : ι → ℝ} (hc : ∀ i, 0 ≤ c i) (θ : ℝ)
    {S : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hS : S.PosSemidef) :
    ownerObjective M (KSSpinSource.family (fun i => KSRankOne.atom (v i)))
      (KSSpinSource.coefficientCovariance c) θ (conjugate signMatrix S) =
    ownerObjective M (KSSpinSource.family (fun i => KSRankOne.atom (v i)))
      (KSSpinSource.coefficientCovariance c) θ S := by
  have hp := covarianceSource_posSemidef
    (KSSpinSource.family (fun i => KSRankOne.atom (v i)))
    (KSSpinSource.family_isHermitian _ (fun _ => KSRankOne.atom_isHermitian _))
    (KSSpinSource.coefficientCovariance_posSemidef hc) hS
  have hf := fidelity_conjugate signMatrix_isHermitian signMatrix_sq hS hp
  rw [KSSpinSymmetry.source_sign_output v c hS] at hf
  simp only [ownerObjective, KSSpinSymmetry.source_sign_input v c hS, hf,
    trace_center_conjugate signMatrix_isHermitian signMatrix_sq hM,
    sqrt_conjugate signMatrix_isHermitian signMatrix_sq hS,
    realTrace_conjugate signMatrix_isHermitian signMatrix_sq]

/-- Strict concavity forces every actual optimizing density to inherit the
sign symmetry. No optimizer or symmetry hypothesis is supplied as an oracle. -/
theorem optimizer_conjugate_eq_of_commute (M : Matrix (n ⊕ n) (n ⊕ n) ℂ)
    (hM : Commute signMatrix M) (v : ι → n → ℂ)
    {c : ι → ℝ} (hc : ∀ i, 0 ≤ c i) {θ : ℝ} (hθ : 0 < θ)
    {S : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hS : S ∈ densitySet)
    (hmax : ∀ T ∈ densitySet,
      ownerObjective M (KSSpinSource.family (fun i => KSRankOne.atom (v i)))
        (KSSpinSource.coefficientCovariance c) θ T ≤
      ownerObjective M (KSSpinSource.family (fun i => KSRankOne.atom (v i)))
        (KSSpinSource.coefficientCovariance c) θ S) :
    conjugate signMatrix S = S := by
  let A := KSSpinSource.family (fun i => KSRankOne.atom (v i))
  let C := KSSpinSource.coefficientCovariance c
  have hA : ∀ i, (A i).IsHermitian :=
    KSSpinSource.family_isHermitian _ (fun _ => KSRankOne.atom_isHermitian _)
  have hC : C.PosSemidef := KSSpinSource.coefficientCovariance_posSemidef hc
  have hval := objective_sign_invariant_of_commute M hM v hc θ hS.1
  have hJS := conjugate_mem_density signMatrix_isHermitian signMatrix_sq hS
  have hmax' : ∀ T ∈ densitySet,
      densityObjective M (covarianceKraus A C) θ T ≤
        densityObjective M (covarianceKraus A C) θ S := by
    intro T hT
    have ht : ownerObjective M A C θ T ≤ ownerObjective M A C θ S := hmax T hT
    simpa only [ownerObjective_eq_densityObjective M A hA hC] using ht
  have hval' : densityObjective M (covarianceKraus A C) θ (conjugate signMatrix S) =
      densityObjective M (covarianceKraus A C) θ S := by
    change ownerObjective M A C θ (conjugate signMatrix S) =
      ownerObjective M A C θ S at hval
    simpa only [ownerObjective_eq_densityObjective M A hA hC] using hval
  exact (strictConcaveOn_densityObjective M (covarianceKraus A C) hθ).eq_of_isMaxOn
    (fun T hT => (hmax' T hT).trans_eq hval'.symm) hmax' hJS hS

theorem optimizer_blockDiagonal_of_commute (M : Matrix (n ⊕ n) (n ⊕ n) ℂ)
    (hM : Commute signMatrix M) (v : ι → n → ℂ)
    {c : ι → ℝ} (hc : ∀ i, 0 ≤ c i) {θ : ℝ} (hθ : 0 < θ)
    {S : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hS : S ∈ densitySet)
    (hmax : ∀ T ∈ densitySet,
      ownerObjective M (KSSpinSource.family (fun i => KSRankOne.atom (v i)))
        (KSSpinSource.coefficientCovariance c) θ T ≤
      ownerObjective M (KSSpinSource.family (fun i => KSRankOne.atom (v i)))
        (KSSpinSource.coefficientCovariance c) θ S) :
    S = Matrix.fromBlocks S.toBlocks₁₁ 0 0 S.toBlocks₂₂ :=
  sign_fixed_blockDiagonal (optimizer_conjugate_eq_of_commute M hM v hc hθ hS hmax)

theorem debit_objective_sign_invariant (H B : Matrix n n ℂ) (v : ι → n → ℂ)
    {c : ι → ℝ} (hc : ∀ i, 0 ≤ c i) (θ : ℝ)
    {S : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hS : S.PosSemidef) :
    ownerObjective (center H B) (KSSpinSource.family (fun i => KSRankOne.atom (v i)))
      (KSSpinSource.coefficientCovariance c) θ (conjugate signMatrix S) =
    ownerObjective (center H B) (KSSpinSource.family (fun i => KSRankOne.atom (v i)))
      (KSSpinSource.coefficientCovariance c) θ S :=
  objective_sign_invariant_of_commute (center H B) (signMatrix_commute_center H B) v hc θ hS

theorem debit_optimizer_conjugate_eq (H B : Matrix n n ℂ) (v : ι → n → ℂ)
    {c : ι → ℝ} (hc : ∀ i, 0 ≤ c i) {θ : ℝ} (hθ : 0 < θ)
    {S : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hS : S ∈ densitySet)
    (hmax : ∀ T ∈ densitySet,
      ownerObjective (center H B) (KSSpinSource.family (fun i => KSRankOne.atom (v i)))
        (KSSpinSource.coefficientCovariance c) θ T ≤
      ownerObjective (center H B) (KSSpinSource.family (fun i => KSRankOne.atom (v i)))
        (KSSpinSource.coefficientCovariance c) θ S) :
    conjugate signMatrix S = S :=
  optimizer_conjugate_eq_of_commute (center H B) (signMatrix_commute_center H B) v hc hθ hS hmax

theorem debit_optimizer_blockDiagonal (H B : Matrix n n ℂ) (v : ι → n → ℂ)
    {c : ι → ℝ} (hc : ∀ i, 0 ≤ c i) {θ : ℝ} (hθ : 0 < θ)
    {S : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hS : S ∈ densitySet)
    (hmax : ∀ T ∈ densitySet,
      ownerObjective (center H B) (KSSpinSource.family (fun i => KSRankOne.atom (v i)))
        (KSSpinSource.coefficientCovariance c) θ T ≤
      ownerObjective (center H B) (KSSpinSource.family (fun i => KSRankOne.atom (v i)))
        (KSSpinSource.coefficientCovariance c) θ S) :
    S = Matrix.fromBlocks S.toBlocks₁₁ 0 0 S.toBlocks₂₂ :=
  optimizer_blockDiagonal_of_commute (center H B) (signMatrix_commute_center H B) v hc hθ hS hmax

/-- The optimizer already selected from proved compact attainment has this
symmetry; the caller supplies no separate maximality or block assumption. -/
theorem debit_densityOptimizer_blockDiagonal [Nonempty n]
    (H B : Matrix n n ℂ) (v : ι → n → ℂ)
    {c : ι → ℝ} (hc : ∀ i, 0 ≤ c i) {θ : ℝ} (hθ : 0 < θ) :
    let A := KSSpinSource.family (fun i => KSRankOne.atom (v i))
    let C := KSSpinSource.coefficientCovariance c
    let S := densityOptimizer (center H B) (covarianceKraus A C) θ
    S = Matrix.fromBlocks S.toBlocks₁₁ 0 0 S.toBlocks₂₂ := by
  let A := KSSpinSource.family (fun i => KSRankOne.atom (v i))
  let C := KSSpinSource.coefficientCovariance c
  have hA := KSSpinSource.family_isHermitian (fun i => KSRankOne.atom (v i))
    (fun i => KSRankOne.atom_isHermitian (v i))
  have hC := KSSpinSource.coefficientCovariance_posSemidef hc
  apply debit_optimizer_blockDiagonal H B v hc hθ
    (densityOptimizer_mem (center H B) (covarianceKraus A C) θ)
  intro T hT
  change ownerObjective (center H B) A C θ T ≤ ownerObjective (center H B) A C θ _
  rw [ownerObjective_eq_densityObjective (center H B) A hA hC,
    ownerObjective_eq_densityObjective (center H B) A hA hC]
  exact densityOptimizer_isMaxOn (center H B) (covarianceKraus A C) θ T hT

end MatrixSpencer.KSDebitCenter
