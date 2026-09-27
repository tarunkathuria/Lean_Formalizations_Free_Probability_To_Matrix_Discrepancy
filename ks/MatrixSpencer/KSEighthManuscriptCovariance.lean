import MatrixSpencer.KSEighthManuscriptComparator
import MatrixSpencer.KSEighthManuscriptMatrixProjection

/-!
# Actual high-trace numerical covariance

The covariance is the finite Jacobi and capped-simplex report for the
regularized linear objective. Its trace is exactly 25k/32. The proof uses the
nearby matrix diagonalized by that computed Jacobi basis, so all numerical
errors are controlled without eigenvalue gaps or an exact projection oracle.
-/

open Matrix Module
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSEighthManuscriptCovariance
open KSJacobiMatrixProjection
variable {d : ℕ}

abbrev energy := @KSJacobiStep.frobeniusEnergy

theorem inner_smul_left (a : ℝ) (A B : Matrix (Fin d) (Fin d) ℝ) :
    frobeniusInner (a • A) B = a * frobeniusInner A B := by
  simp [frobeniusInner, ← Finset.mul_sum, mul_assoc]

theorem energy_sub (A B : Matrix (Fin d) (Fin d) ℝ) :
    energy (A-B) = energy A - 2*frobeniusInner A B + energy B := by
  simp only [energy, KSJacobiStep.frobeniusEnergy, frobeniusInner,
    Matrix.sub_apply, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem energy_sub_comm (A B : Matrix (Fin d) (Fin d) ℝ) : energy (A-B) = energy (B-A) := by
  rw [energy_sub, energy_sub, frobeniusInner_comm A B]
  ring

/-- Uniform Frobenius error paired with a bounded contraction costs at most
error times dimension. The deliberate coarse dimension bound avoids any
spectral information about the error matrix. -/
theorem inner_error_bound (E P : Matrix (Fin d) (Fin d) ℝ) {ε : ℝ}
    (hε : 0 ≤ ε) (hd : 0 < d) (hE : energy E ≤ ε^2) (hP : energy P ≤ d) :
    |frobeniusInner E P| ≤ ε*d := by
  have hdn : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hEP := frobeniusInner_cauchy E P
  have hP0 := KSJacobiRayleigh.frobeniusEnergy_nonneg P
  have he : energy E * energy P ≤ ε^2 * d :=
    mul_le_mul hE hP hP0 (sq_nonneg ε)
  have he' : ε^2 * d ≤ (ε*d)^2 := by
    nlinarith [mul_nonneg (sq_nonneg ε) (show (0:ℝ) ≤ (d:ℝ)^2-d by nlinarith)]
  have hsq : |frobeniusInner E P|^2 ≤ (ε*d)^2 := by
    rw [sq_abs]
    exact hEP.trans (he.trans he')
  nlinarith [abs_nonneg (frobeniusInner E P), mul_nonneg hε (Nat.cast_nonneg d)]

def target (d : ℕ) : ℝ := (25/32 : ℝ)*d

def covariance (Khat : Matrix (Fin d) (Fin d) ℝ) (κ β : ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  KSEighthManuscriptMatrixProjection.report ((-κ⁻¹) • Khat) (target d) β

theorem target_nonneg (d : ℕ) : 0 ≤ target d := by unfold target; positivity
theorem target_le (d : ℕ) : target d ≤ d := by unfold target; nlinarith [show (0 : ℝ) ≤ d from Nat.cast_nonneg d]

theorem covariance_feasible (Khat : Matrix (Fin d) (Fin d) ℝ) (κ β : ℝ) :
    KSEighthManuscriptMatrixProjection.Feasible (target d) (covariance Khat κ β) :=
  KSEighthManuscriptMatrixProjection.report_feasible _ _ (target_nonneg d) (target_le d) β

theorem covariance_posSemidef (Khat : Matrix (Fin d) (Fin d) ℝ) (κ β : ℝ) :
    (covariance Khat κ β).PosSemidef :=
  KSEighthManuscriptMatrixProjection.report_posSemidef _ _ (target_nonneg d) (target_le d) β

theorem covariance_energy_le (Khat : Matrix (Fin d) (Fin d) ℝ) (κ β : ℝ) :
    energy (covariance Khat κ β) ≤ target d := by
  let A := (-κ⁻¹) • Khat
  let z := fun i => KSJacobiRayleigh.finalMatrix A β i i
  let p := KSEighthManuscriptCappedSimplex.project z (target d)
  change energy (conjugate (KSJacobiRayleigh.finalBasis A β) (Matrix.diagonal p)) ≤ _
  have hU : (KSJacobiRayleigh.finalBasis A β)ᵀ * KSJacobiRayleigh.finalBasis A β = 1 :=
    KSJacobiIteration.accumulatedBasis_transpose_mul A _
  rw [show energy (conjugate (KSJacobiRayleigh.finalBasis A β) (Matrix.diagonal p)) =
    energy (Matrix.diagonal p) from conjugate_energy _ _ hU]
  have he : energy (Matrix.diagonal p) = ∑i,p i^2 := by
    simp [energy, KSJacobiStep.frobeniusEnergy, Matrix.diagonal_apply]
  rw [he, ← KSEighthManuscriptCappedSimplex.project_sum z (target_nonneg d) (target_le d)]
  apply Finset.sum_le_sum
  intro i _
  have h0 := KSEighthManuscriptCappedSimplex.project_nonneg z (target d) i
  have h1 := KSEighthManuscriptCappedSimplex.project_le_one z (target d) i
  change p i^2 ≤ p i
  change 0 ≤ p i at h0
  change p i ≤ 1 at h1
  nlinarith


theorem covariance_spec (K Khat : Matrix (Fin d) (Fin d) ℝ)
    (hKhat : Khat.IsSymm) {κ β : ℝ} (hκ : 0 < κ) (hβ : 0 < β) (hβsmall : β ≤ 1/4)
    (hd : 0 < d) (herror : energy (K-Khat) ≤ κ^2)
    (W : Submodule ℝ (Fin d → ℝ))
    (hdim : (13/16 : ℝ)*d < (finrank ℝ W : ℝ))
    (hW : KSEighthInertia.StrictlyNegativeOn K W) :
    (covariance Khat κ β).PosSemidef ∧ covariance Khat κ β ≤ 1 ∧
      (3/4 : ℝ)*d ≤ Matrix.trace (covariance Khat κ β) ∧
      Matrix.trace (covariance Khat κ β * K) ≤ 3*κ*d := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  obtain ⟨P, hP, hP1, hPt, hPK, hPE⟩ :=
    KSEighthManuscriptComparator.exists_manuscript_comparator K W (by simpa using hdim) hW
  simp only [Fintype.card_fin] at hPt hPE
  change Matrix.trace P = target d at hPt
  change energy P ≤ target d at hPE
  have hPf : KSEighthManuscriptMatrixProjection.Feasible (target d) P :=
    ⟨by simpa only [Matrix.IsHermitian, Matrix.conjTranspose, star_trivial] using hP.isHermitian,
      hP.nonneg, hP1, hPt⟩
  let Q := covariance Khat κ β
  let A := (-κ⁻¹) • Khat
  let B := KSJacobiMatrixProjection.surrogate A β
  have hAs : A.IsSymm := by
    change ((-κ⁻¹) • Khat)ᵀ = (-κ⁻¹) • Khat
    rw [Matrix.transpose_smul, hKhat.eq]
  have hQf := covariance_feasible Khat κ β
  have hQE := (covariance_energy_le Khat κ β).trans (target_le d)
  have hPE' := hPE.trans (target_le d)
  have hmin := KSEighthManuscriptMatrixProjection.projection_distance_le
    (KSEighthManuscriptMatrixProjection.report_isProjection_surrogate A (target d)
      (target_nonneg d) (target_le d) β) P hPf
  change energy (B-Q) ≤ energy (B-P) at hmin
  rw [energy_sub, energy_sub] at hmin
  have hEQ := inner_error_bound (B-A) Q hβ.le hd
    (by rw [energy_sub_comm]; exact KSJacobiMatrixProjection.surrogate_error A hAs hβ) hQE
  have hEP := inner_error_bound (B-A) P hβ.le hd
    (by rw [energy_sub_comm]; exact KSJacobiMatrixProjection.surrogate_error A hAs hβ) hPE'
  have hKQ := inner_error_bound (K-Khat) Q hκ.le hd herror hQE
  have hKP := inner_error_bound (K-Khat) P hκ.le hd herror hPE'
  have hKPe : frobeniusInner K P ≤ 0 := by
    rw [frobeniusInner_comm, frobeniusInner_eq_trace]
    have hPt' : Pᵀ = P := by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hP.isHermitian.eq
    rw [hPt']
    exact hPK
  have hQKe : Matrix.trace (Q*K) = frobeniusInner K Q := by
    rw [frobeniusInner_comm, frobeniusInner_eq_trace, hQf.1.eq]
  simp only [frobeniusInner_sub_left] at hEQ hEP hKQ hKP
  have hAQ : frobeniusInner A Q = -κ⁻¹ * frobeniusInner Khat Q := inner_smul_left _ _ _
  have hAP : frobeniusInner A P = -κ⁻¹ * frobeniusInner Khat P := inner_smul_left _ _ _
  have hQ0 := KSJacobiRayleigh.frobeniusEnergy_nonneg Q
  have hmain : frobeniusInner K Q ≤ (5/2 : ℝ)*κ*d + 2*κ*β*d := by
    have hp := (abs_le.mp hEP).1
    have hq := (abs_le.mp hEQ).2
    have hkp := (abs_le.mp hKP).1
    have hkq := (abs_le.mp hKQ).2
    rw [hAQ] at hq
    rw [hAP] at hp
    have hh := mul_le_mul_of_nonneg_left hmin hκ.le
    have hi : κ*κ⁻¹ = 1 := mul_inv_cancel₀ hκ.ne'
    have hqe := mul_nonneg hκ.le hQ0
    have hpe := mul_le_mul_of_nonneg_left hPE' hκ.le
    have hp' := mul_le_mul_of_nonneg_left hp hκ.le
    have hq' := mul_le_mul_of_nonneg_left hq hκ.le
    simp only [neg_mul, sub_neg_eq_add, mul_add, ← mul_assoc, hi, one_mul] at hp' hq'
    change 0 ≤ κ * energy Q at hqe
    nlinarith
  refine ⟨covariance_posSemidef Khat κ β, hQf.2.2.1, ?_, ?_⟩
  · rw [hQf.2.2.2]
    unfold target
    nlinarith [show (0 : ℝ) ≤ d from Nat.cast_nonneg d]
  · change Matrix.trace (Q*K) ≤ _
    rw [hQKe]
    apply hmain.trans
    nlinarith [mul_nonneg (mul_nonneg hκ.le (Nat.cast_nonneg d)) (sub_nonneg.mpr hβsmall)]

end MatrixSpencer.KSEighthManuscriptCovariance
