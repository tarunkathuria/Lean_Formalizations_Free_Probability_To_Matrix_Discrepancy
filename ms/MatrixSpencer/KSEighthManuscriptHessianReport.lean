import MatrixSpencer.KSEighthManuscriptCovariance
import MatrixSpencer.KSEighthManuscriptPreparedInertia
import MatrixSpencer.KSEighthHessianQueries



open Matrix Set Module
open scoped BigOperators MatrixOrder ContDiff Topology
noncomputable section
namespace MatrixSpencer.KSEighthManuscriptHessianReport
open KSEighthLiveEnumeration KSEighthHessianQueries KSEighthFacePotential
variable {N d : ℕ}

def report (v : Fin N → Fin d → ℂ) (θ η : ℝ) (hd : 0 < d) (x : Fin N → ℝ) :
    Matrix (Fin (count x)) (Fin (count x)) ℝ :=
  (1/2 : ℝ) • KSMatrixEntryAccuracy.symmetrize
    (KSNumericalHessian.matrixReport (faceReport v θ η hd x) 0 (queryMesh v θ η x))

theorem report_isSymm (v : Fin N → Fin d → ℂ) (θ η : ℝ) (hd : 0 < d) (x : Fin N → ℝ) :
    (report v θ η hd x).IsSymm := by
  unfold report
  change ((1/2 : ℝ) • _)ᵀ = _
  rw [Matrix.transpose_smul, (KSMatrixEntryAccuracy.symmetrize_isSymm _).eq]

theorem report_entry_accuracy (v : Fin N → Fin d → ℂ) {θ η : ℝ}
    (hθ : 0 < θ) (hη : 0 < η) (hd : 0 < d)
    {x : Fin N → ℝ} (hx : x ∈ ksCube (1/8)) (hk : 0 < count x) :
    ∀i j, |KSEighthManuscriptPreparedInertia.hessian v θ x i j - report v θ η hd x i j| ≤ η/count x := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  have hf : ContDiffAt ℝ 2 (potential v θ x) 0 :=
    (contDiffAt_potential v hθ x).of_le
      (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have he := KSNumericalHessian.selected_entry_error (potential v θ x)
    (faceReport v θ η hd x) 0 hk (by norm_num : (0 : ℝ) < 1/32)
    (KSEighthInputTaylorBound.fourthBudget_pos v hθ).le hη hf
    (line_bounds v hθ hd hx) (query_accuracy v hθ hη hd hx hk)
  have hs := KSMatrixEntryAccuracy.symmetrize_entry_error
    (KSNumericalHessian.hessian_isSymm _ _ hf) he
  intro i j
  have hij := hs i j
  change |(1/2 : ℝ)*_ - (1/2 : ℝ)*_| ≤ _
  rw [← mul_sub, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/2)]
  have hnon : 0 ≤ η/(count x : ℝ) := div_nonneg hη.le (Nat.cast_nonneg _)
  dsimp only [queryMesh]
  nlinarith

theorem report_frobenius_accuracy (v : Fin N → Fin d → ℂ) {θ η : ℝ}
    (hθ : 0 < θ) (hη : 0 < η) (hd : 0 < d)
    {x : Fin N → ℝ} (hx : x ∈ ksCube (1/8)) (hk : 0 < count x) :
    KSJacobiStep.frobeniusEnergy
      (KSEighthManuscriptPreparedInertia.hessian v θ x - report v θ η hd x) ≤ η^2 := by
  have he := report_entry_accuracy v hθ hη hd hx hk
  have hk' : (count x : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  calc
    _ ≤ ∑_i : Fin (count x), ∑_j : Fin (count x), (η/(count x : ℝ))^2 := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      have h := he i j
      change (KSEighthManuscriptPreparedInertia.hessian v θ x i j - report v θ η hd x i j)^2 ≤ _
      nlinarith [sq_abs (KSEighthManuscriptPreparedInertia.hessian v θ x i j - report v θ η hd x i j),
        abs_nonneg (KSEighthManuscriptPreparedInertia.hessian v θ x i j - report v θ η hd x i j),
        div_nonneg hη.le (Nat.cast_nonneg (α := ℝ) (count x))]
    _ = η^2 := by simp; field_simp

def covariance (v : Fin N → Fin d → ℂ) (θ η κ β : ℝ) (hd : 0 < d) (x : Fin N → ℝ) :=
  KSEighthManuscriptCovariance.covariance (report v θ η hd x) κ β

/-- All analytic and inertia hypotheses are discharged for the actual state
and reports. Parameters η≤κ and β≤1/4 are scalar tuning conditions only. -/
theorem covariance_spec (v : Fin N → Fin d → ℂ) {ρ τ θ η κ β : ℝ}
    (hτ : 0 < τ) (hθ : 0 < θ) (hη : 0 < η) (hηκ : η ≤ κ)
    (hβ : 0 < β) (hβsmall : β ≤ 1/4) (hd : 0 < d)
    (s : KSEighthWalkRun.PreparedState N ρ τ (KSEighthNumericalValue.stateReport v θ hd (τ/8)))
    (hs : ¬KSEighthWalkRun.terminal s) :
    (covariance v θ η κ β hd s.coeff).PosSemidef ∧ covariance v θ η κ β hd s.coeff ≤ 1 ∧
      (3/4 : ℝ)*count s.coeff ≤ Matrix.trace (covariance v θ η κ β hd s.coeff) ∧
      Matrix.trace (covariance v θ η κ β hd s.coeff *
        KSEighthManuscriptPreparedInertia.hessian v θ s.coeff) ≤ 3*κ*count s.coeff := by
  have hk := count_pos_of_not_vertex s.cube hs
  obtain ⟨W, hdim, hW⟩ := KSEighthManuscriptPreparedInertia.numerical_prepared_large_inertia v hθ hτ hd s hs
  exact KSEighthManuscriptCovariance.covariance_spec _ _ (report_isSymm _ _ _ _ _)
    (hη.trans_le hηκ) hβ hβsmall hk
    ((report_frobenius_accuracy v hθ hη hd s.cube hk).trans (by nlinarith)) W hdim hW

end MatrixSpencer.KSEighthManuscriptHessianReport
