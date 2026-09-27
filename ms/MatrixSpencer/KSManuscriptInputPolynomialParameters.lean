import MatrixSpencer.KSManuscriptPolynomialParameters
import MatrixSpencer.KSManuscriptPolynomialTaylorBounds
import MatrixSpencer.KSFullManuscriptAlgorithm
import MatrixSpencer.KSEighthManuscriptExplicit



open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSManuscriptInputPolynomialParameters
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000
open KSEighthManuscriptPreprocess KSManuscriptPolynomialTaylorBounds
variable {N d : ℕ}

theorem epsilon_family_eq (v : Fin N → Fin d → ℂ) : epsilon (family v) = epsilon v := by
  apply le_antisymm
  · exact epsilon_le _ (epsilon_nonneg v) (family_size v)
  · apply epsilon_le v (epsilon_nonneg (family v))
    intro i
    by_cases hi : size v i = 0
    · rw [atom_zero_of_size v i hi,norm_zero]
      exact epsilon_nonneg _
    · have he : family v ((labelEquiv v).symm ⟨i,hi⟩) = v i := by
        simp [family]
      rw [←he,←size_eq_norm]
      exact size_le_epsilon _ _

theorem taylorCap_mono {K N d : ℕ} (h : K ≤ N) : taylorCap K d ≤ taylorCap N d := by
  apply pow_le_pow_left₀ (sizeBase_pos K d).le
  unfold sizeBase
  exact mul_le_mul_of_nonneg_left
    (add_le_add_right (add_le_add_right (Nat.cast_le.mpr h) (d : ℝ)) 1) (by norm_num)

theorem labels_pos (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑i,KSRankOne.atom (v i)) = 1) : 0 < N :=
  (count_pos v hd hp).trans_le (count_le v)

theorem full_taylorBudget_le (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑i,KSRankOne.atom (v i)) = 1) :
    KSFullManuscriptAlgorithm.taylorBudget v (epsilon v) ≤ taylorCap N d :=
  full_budget_le v hd hp

theorem retained_fourthCap_le (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑i,KSRankOne.atom (v i)) = 1) :
    KSEighthManuscriptParameters.fourthCap (family v) (ksRegularizerScale (epsilon v) (Fin d)) ≤
      taylorCap N d := by
  have h := eighth_fourthCap_le_taylorCap (family v) hd (family_parseval v hp)
  rw [epsilon_family_eq] at h
  exact h.trans (taylorCap_mono (count_le v))

theorem retained_inverse_delta_le (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑i,KSRankOne.atom (v i)) = 1) :
    (Real.sqrt (epsilon v))⁻¹ ≤ (count v : ℝ) := by
  have h := KSManuscriptScaleBounds.inverse_delta_le (family v) hd (family_parseval v hp)
  rwa [epsilon_family_eq] at h

private theorem full_positive (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑i,KSRankOne.atom (v i)) = 1) :
    0 < KSFullManuscriptAlgorithm.taylorBudget v (epsilon v) := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  exact KSFullManuscriptAlgorithm.taylorBudget_pos v (labels_pos v hd hp) (epsilon_pos v hd hp)

private theorem retained_positive (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑i,KSRankOne.atom (v i)) = 1) :
    0 < KSEighthManuscriptParameters.fourthCap (family v) (ksRegularizerScale (epsilon v) (Fin d)) := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  exact KSEighthManuscriptParameters.fourthCap_pos (family v)
    (ksRegularizerScale_pos (epsilon_pos v hd hp)) hd

def fullHorizonBound (N d : ℕ) : ℝ :=
  256*(N : ℝ)^3+100*(N : ℝ)^3*taylorCap N d+1

def eighthHorizonBound (N d : ℕ) : ℝ :=
  4000000*(N : ℝ)*((N : ℝ)^5+taylorCap N d*(N : ℝ)^4+1)+1

theorem full_horizon_le (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑i,KSRankOne.atom (v i)) = 1) :
    (KSFullManuscriptAlgorithm.horizon v (epsilon v) : ℝ) ≤ fullHorizonBound N d :=
  KSManuscriptPolynomialParameters.full_cutoff_le (labels_pos v hd hp)
    (Real.sqrt_pos.mpr (epsilon_pos v hd hp)) (KSManuscriptScaleBounds.inverse_delta_le v hd hp)
    (full_positive v hd hp) (full_taylorBudget_le v hd hp)

theorem full_query_inv_sq_le (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑i,KSRankOne.atom (v i)) = 1) :
    (KSFullManuscriptParameters.queryStep N (Real.sqrt (epsilon v))
      (KSFullManuscriptAlgorithm.taylorBudget v (epsilon v)) ^ 2)⁻¹ ≤
        32*(N : ℝ)^2+800*(N : ℝ)^3*taylorCap N d :=
  KSManuscriptPolynomialParameters.full_query_inv_sq_le (labels_pos v hd hp)
    (Real.sqrt_pos.mpr (epsilon_pos v hd hp)) (KSManuscriptScaleBounds.inverse_delta_le v hd hp)
    (full_positive v hd hp) (full_taylorBudget_le v hd hp)

theorem full_value_inv_le (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑i,KSRankOne.atom (v i)) = 1) :
    (KSFullManuscriptParameters.valueTolerance N (Real.sqrt (epsilon v))
      (KSFullManuscriptAlgorithm.taylorBudget v (epsilon v)))⁻¹ ≤
        1600*(N : ℝ)^3*(32*(N : ℝ)^2+800*(N : ℝ)^3*taylorCap N d) :=
  KSManuscriptPolynomialParameters.full_value_inv_le (labels_pos v hd hp)
    (Real.sqrt_pos.mpr (epsilon_pos v hd hp)) (KSManuscriptScaleBounds.inverse_delta_le v hd hp)
    (full_positive v hd hp) (full_taylorBudget_le v hd hp)

theorem full_movement_inv_sq_le (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑i,KSRankOne.atom (v i)) = 1) :
    (KSFullManuscriptParameters.movementStep N (Real.sqrt (epsilon v))
      (KSFullManuscriptAlgorithm.taylorBudget v (epsilon v)) ^ 2)⁻¹ ≤
        16*(N : ℝ)^2+100*(N : ℝ)^2*taylorCap N d :=
  KSManuscriptPolynomialParameters.full_movement_inv_sq_le (labels_pos v hd hp)
    (Real.sqrt_pos.mpr (epsilon_pos v hd hp)) (KSManuscriptScaleBounds.inverse_delta_le v hd hp)
    (full_positive v hd hp) (full_taylorBudget_le v hd hp)

theorem eighth_movement_inv_sq_le (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑i,KSRankOne.atom (v i)) = 1) :
    (KSEighthManuscriptParameters.movementStep (family v) (Real.sqrt (epsilon v))
      (ksRegularizerScale (epsilon v) (Fin d)) ^ 2)⁻¹ ≤
        40000*((N : ℝ)^5+taylorCap N d*(N : ℝ)^4+1) := by
  have h := KSManuscriptPolynomialParameters.eighth_movement_inv_sq_le (family v)
    (count_pos v hd hp) (Real.sqrt_pos.mpr (epsilon_pos v hd hp)) (retained_inverse_delta_le v hd hp)
    (retained_positive v hd hp) (retained_fourthCap_le v hd hp)
  apply h.trans
  have hc : (count v : ℝ) ≤ N := Nat.cast_le.mpr (count_le v)
  have hB : 0 ≤ taylorCap N d := (taylorCap_ge_one N d).trans' zero_le_one
  gcongr

theorem eighth_horizon_le (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑i,KSRankOne.atom (v i)) = 1) :
    (KSEighthManuscriptAlgorithm.cutoff (family v) (epsilon v) : ℝ) ≤ eighthHorizonBound N d := by
  have h := KSManuscriptPolynomialParameters.eighth_cutoff_le (family v)
    (count_pos v hd hp) (Real.sqrt_pos.mpr (epsilon_pos v hd hp)) (retained_inverse_delta_le v hd hp)
    (retained_positive v hd hp) (retained_fourthCap_le v hd hp)
  change (KSEighthManuscriptAlgorithm.cutoff (family v) (epsilon v) : ℝ) ≤ _ at h
  apply h.trans
  unfold eighthHorizonBound
  have hc : (count v : ℝ) ≤ N := Nat.cast_le.mpr (count_le v)
  have hB : 0 ≤ taylorCap N d := (taylorCap_ge_one N d).trans' zero_le_one
  gcongr

theorem eighth_precision_inv_le (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑i,KSRankOne.atom (v i)) = 1) :
    (KSEighthManuscriptParameters.precision (count v) (Real.sqrt (epsilon v)))⁻¹ ≤
      1000000*(N : ℝ)^4 := by
  apply (KSManuscriptPolynomialParameters.eighth_precision_inv_le (retained_inverse_delta_le v hd hp)).trans
  have hc : (count v : ℝ) ≤ N := Nat.cast_le.mpr (count_le v)
  gcongr

theorem eighth_beta_inv_le (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑i,KSRankOne.atom (v i)) = 1) :
    (KSEighthManuscriptParameters.beta (family v) (Real.sqrt (epsilon v))
      (ksRegularizerScale (epsilon v) (Fin d)))⁻¹ ≤ 1000000*(N : ℝ)^4*(taylorCap N d+1) := by
  have h := KSManuscriptPolynomialParameters.eighth_beta_inv_le (family v)
    (Real.sqrt_pos.mpr (epsilon_pos v hd hp)) (retained_inverse_delta_le v hd hp)
    (retained_positive v hd hp).le (retained_fourthCap_le v hd hp)
  apply h.trans
  have hc : (count v : ℝ) ≤ N := Nat.cast_le.mpr (count_le v)
  have hB : 0 ≤ taylorCap N d := (taylorCap_ge_one N d).trans' zero_le_one
  gcongr


theorem full_curvature_inv_le (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑i,KSRankOne.atom (v i)) = 1) :
    (KSFullManuscriptParameters.curvatureTolerance N (Real.sqrt (epsilon v)))⁻¹ ≤ 100*(N : ℝ)^2 :=
  KSManuscriptPolynomialParameters.full_curvature_inv_le (labels_pos v hd hp)
    (Real.sqrt_pos.mpr (epsilon_pos v hd hp)) (KSManuscriptScaleBounds.inverse_delta_le v hd hp)

theorem eighth_rho_inv_le (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑i,KSRankOne.atom (v i)) = 1) :
    (KSEighthManuscriptParameters.rho (count v) (Real.sqrt (epsilon v)))⁻¹ ≤ 100*(N : ℝ)^2 := by
  apply (KSManuscriptPolynomialParameters.eighth_rho_inv_le (retained_inverse_delta_le v hd hp)).trans
  have hc : (count v : ℝ) ≤ N := Nat.cast_le.mpr (count_le v)
  gcongr

theorem eighth_kappa_inv_le (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑i,KSRankOne.atom (v i)) = 1) :
    (KSEighthManuscriptParameters.kappa (count v) (Real.sqrt (epsilon v)))⁻¹ ≤ 10000*(N : ℝ)^3 := by
  apply (KSManuscriptPolynomialParameters.eighth_kappa_inv_le (retained_inverse_delta_le v hd hp)).trans
  have hc : (count v : ℝ) ≤ N := Nat.cast_le.mpr (count_le v)
  gcongr

theorem eighth_query_inv_sq_le (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑i,KSRankOne.atom (v i)) = 1) (x : Fin (count v) → ℝ)
    (hx : 0 < KSEighthLiveEnumeration.count x) :
    (KSEighthHessianQueries.queryMesh (family v) (ksRegularizerScale (epsilon v) (Fin d))
      (KSEighthManuscriptParameters.precision (count v) (Real.sqrt (epsilon v))) x^2)⁻¹ ≤
        1024+1000000*taylorCap N d*(N : ℝ)^5 := by
  have h := KSManuscriptPolynomialParameters.eighth_query_inv_sq_le (family v)
    (count_pos v hd hp) (Real.sqrt_pos.mpr (epsilon_pos v hd hp)) (retained_inverse_delta_le v hd hp)
    (retained_positive v hd hp) (retained_fourthCap_le v hd hp) x hx
  apply h.trans
  have hc : (count v : ℝ) ≤ N := Nat.cast_le.mpr (count_le v)
  have hB : 0 ≤ taylorCap N d := (taylorCap_ge_one N d).trans' zero_le_one
  gcongr

theorem eighth_query_value_inv_le (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑i,KSRankOne.atom (v i)) = 1) (x : Fin (count v) → ℝ)
    (hx : 0 < KSEighthLiveEnumeration.count x) :
    (KSEighthHessianQueries.queryTolerance (family v) (ksRegularizerScale (epsilon v) (Fin d))
      (KSEighthManuscriptParameters.precision (count v) (Real.sqrt (epsilon v))) x)⁻¹ ≤
        4000000*(N : ℝ)^5*(1024+1000000*taylorCap N d*(N : ℝ)^5) := by
  have h := KSManuscriptPolynomialParameters.eighth_query_value_inv_le (family v)
    (count_pos v hd hp) (Real.sqrt_pos.mpr (epsilon_pos v hd hp)) (retained_inverse_delta_le v hd hp)
    (retained_positive v hd hp) (retained_fourthCap_le v hd hp) x hx
  apply h.trans
  have hc : (count v : ℝ) ≤ N := Nat.cast_le.mpr (count_le v)
  have hB : 0 ≤ taylorCap N d := (taylorCap_ge_one N d).trans' zero_le_one
  gcongr

end MatrixSpencer.KSManuscriptInputPolynomialParameters
