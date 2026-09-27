import MatrixSpencer.KSSignSymmetry

/-! Block diagonality of the actual spin-coupled optimizer on the full density domain. -/

open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix

noncomputable section
namespace MatrixSpencer.KSSpinSymmetry

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n]

open KSSignSymmetry

theorem source_sign_input (v : ι → n → ℂ) (c : ι → ℝ)
    {S : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hS : S.PosSemidef) :
    covarianceSource (KSSpinSource.family (fun i => KSRankOne.atom (v i)))
      (KSSpinSource.coefficientCovariance c) (conjugate signMatrix S) =
    covarianceSource (KSSpinSource.family (fun i => KSRankOne.atom (v i)))
      (KSSpinSource.coefficientCovariance c) S := by
  rw [KSSpinSource.source_eq_tracePrepare_real v c
    (conjugate_posSemidef signMatrix_isHermitian hS).isHermitian,
    KSSpinSource.source_eq_tracePrepare_real v c hS.isHermitian]
  simp only [trace_center_conjugate signMatrix_isHermitian signMatrix_sq
    (signMatrix_commute_doubled _)]

theorem source_sign_output (v : ι → n → ℂ) (c : ι → ℝ)
    {S : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hS : S.PosSemidef) :
    conjugate signMatrix
      (covarianceSource (KSSpinSource.family (fun i => KSRankOne.atom (v i)))
        (KSSpinSource.coefficientCovariance c) S) =
    covarianceSource (KSSpinSource.family (fun i => KSRankOne.atom (v i)))
      (KSSpinSource.coefficientCovariance c) S := by
  rw [KSSpinSource.source_eq_tracePrepare_real v c hS.isHermitian]
  simp only [conjugate, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact conjugate_eq_of_commute signMatrix_sq (signMatrix_commute_doubled _)

theorem objective_sign_invariant (H : Matrix n n ℂ) (v : ι → n → ℂ)
    {c : ι → ℝ} (hc : ∀ i, 0 ≤ c i) (θ : ℝ)
    {S : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hS : S.PosSemidef) :
    ownerObjective (signedLift H) (KSSpinSource.family (fun i => KSRankOne.atom (v i)))
      (KSSpinSource.coefficientCovariance c) θ (conjugate signMatrix S) =
    ownerObjective (signedLift H) (KSSpinSource.family (fun i => KSRankOne.atom (v i)))
      (KSSpinSource.coefficientCovariance c) θ S := by
  have hp := covarianceSource_posSemidef
    (KSSpinSource.family (fun i => KSRankOne.atom (v i)))
    (KSSpinSource.family_isHermitian _ (fun _ => KSRankOne.atom_isHermitian _))
    (KSSpinSource.coefficientCovariance_posSemidef hc) hS
  have hf := fidelity_conjugate signMatrix_isHermitian signMatrix_sq hS hp
  rw [source_sign_output v c hS] at hf
  simp only [ownerObjective, source_sign_input v c hS, hf,
    trace_center_conjugate signMatrix_isHermitian signMatrix_sq (signMatrix_commute_signedLift H),
    sqrt_conjugate signMatrix_isHermitian signMatrix_sq hS,
    realTrace_conjugate signMatrix_isHermitian signMatrix_sq]

theorem optimizer_blockDiagonal (H : Matrix n n ℂ) (v : ι → n → ℂ)
    {c : ι → ℝ} (hc : ∀ i, 0 ≤ c i) {θ : ℝ} (hθ : 0 < θ)
    {S : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hS : S ∈ densitySet)
    (hmax : ∀ T ∈ densitySet,
      ownerObjective (signedLift H) (KSSpinSource.family (fun i => KSRankOne.atom (v i)))
        (KSSpinSource.coefficientCovariance c) θ T ≤
      ownerObjective (signedLift H) (KSSpinSource.family (fun i => KSRankOne.atom (v i)))
        (KSSpinSource.coefficientCovariance c) θ S) :
    S = Matrix.fromBlocks S.toBlocks₁₁ 0 0 S.toBlocks₂₂ := by
  let A := KSSpinSource.family (fun i => KSRankOne.atom (v i))
  let C := KSSpinSource.coefficientCovariance c
  have hA : ∀ i, (A i).IsHermitian :=
    KSSpinSource.family_isHermitian _ (fun _ => KSRankOne.atom_isHermitian _)
  have hC : C.PosSemidef := KSSpinSource.coefficientCovariance_posSemidef hc
  have hval := objective_sign_invariant H v hc θ hS.1
  have hJS := conjugate_mem_density signMatrix_isHermitian signMatrix_sq hS
  have hmax' : ∀ T ∈ densitySet,
      densityObjective (signedLift H) (covarianceKraus A C) θ T ≤
        densityObjective (signedLift H) (covarianceKraus A C) θ S := by
    intro T hT
    exact (ownerObjective_eq_densityObjective (signedLift H) A hA hC θ T).symm ▸
      (ownerObjective_eq_densityObjective (signedLift H) A hA hC θ S).symm ▸ hmax T hT
  have hval' : densityObjective (signedLift H) (covarianceKraus A C) θ (conjugate signMatrix S) =
      densityObjective (signedLift H) (covarianceKraus A C) θ S := by
    change ownerObjective (signedLift H) A C θ (conjugate signMatrix S) =
      ownerObjective (signedLift H) A C θ S at hval
    simpa only [ownerObjective_eq_densityObjective (signedLift H) A hA hC] using hval
  apply sign_fixed_blockDiagonal
  exact (strictConcaveOn_densityObjective (signedLift H) (covarianceKraus A C) hθ).eq_of_isMaxOn
    (fun T hT => (hmax' T hT).trans_eq hval'.symm) hmax' hJS hS

end MatrixSpencer.KSSpinSymmetry
