import MatrixSpencer.RegularizedOwnerPotential
import MatrixSpencer.CovariancePreparation

/-!
# Compact preparation with a continuous density regularizer

The optimized owner potential is the actual supremum over density matrices.
Its proved continuity supplies the compact minimizer. No response estimate,
covariance derivative, or derivative cap is assumed here.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix Set
noncomputable section
namespace MatrixSpencer

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n]

theorem continuousOn_regularizedOwnerPotential_covariance (H : Matrix n n ℂ)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (R : Matrix n n ℂ → ℝ) (hR : ContinuousOn R densitySet) (C : Matrix ι ι ℝ) :
    ContinuousOn (fun K => regularizedOwnerPotential H A K R) (Icc 0 C) := by
  apply continuousOn_iff_continuous_restrict.mpr
  have hm : Continuous (fun K : Icc (0 : Matrix ι ι ℝ) C =>
      (H, (⟨K.val, K.property.1.posSemidef⟩ : {Q : Matrix ι ι ℝ // Q.PosSemidef}))) := by
    have hk : Continuous (fun K : Icc (0 : Matrix ι ι ℝ) C => K.val) := continuous_subtype_val
    exact continuous_const.prodMk (hk.subtype_mk (fun K => K.property.1.posSemidef))
  have hc := (continuous_regularizedOwnerPotential_psd A hA R hR).comp hm
  simpa only [Function.comp_def] using hc

/-- The actual compact minimizer pays for its entire covariance trace withdrawal. -/
theorem exists_regularized_owner_preparation (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) {C : Matrix ι ι ℝ} (hC : C.PosSemidef)
    (R : Matrix n n ℂ → ℝ) (hR : ContinuousOn R densitySet) (t : ℝ) :
    ∃ K ∈ Icc 0 C,
      IsMinOn (covarianceObjective C (fun Q => regularizedOwnerPotential H A Q R) t) (Icc 0 C) K ∧
      regularizedOwnerPotential H A K R + t * realTrace (C - K) ≤
        regularizedOwnerPotential H A C R := by
  exact exists_covariance_minimizer_of_continuousOn hC
    (continuousOn_regularizedOwnerPotential_covariance H A hA R hR C) t

/-- The withdrawal bound depends only on the fidelity excess, so it is independent of R. -/
theorem exists_regularized_owner_preparation_trace_budget [Nonempty n]
    (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (hN : ∀ i, ‖A i‖ ≤ 1) {C : Matrix ι ι ℝ} (hC0 : C.PosSemidef) (hC1 : C ≤ 1)
    (R : Matrix n n ℂ → ℝ) (hR : ContinuousOn R densitySet) {t : ℝ} (ht : 0 < t) :
    ∃ K ∈ Icc 0 C,
      IsMinOn (covarianceObjective C (fun Q => regularizedOwnerPotential H A Q R) t) (Icc 0 C) K ∧
      regularizedOwnerPotential H A K R + t * realTrace (C - K) ≤
        regularizedOwnerPotential H A C R ∧
      0 ≤ realTrace (C - K) ∧
      realTrace (C - K) ≤ 2 * Real.sqrt (Fintype.card ι : ℝ) / t := by
  obtain ⟨K, hK, hmin, hpaid⟩ := exists_regularized_owner_preparation H A hA hC0 R hR t
  refine ⟨K, hK, hmin, hpaid, realTrace_nonneg (sub_nonneg.mpr hK.2).posSemidef, ?_⟩
  have hbase := regularizedBasePotential_le_owner H A hA hK.1.posSemidef R hR
  have hupper := regularizedOwnerPotential_le_base_add H A hA hN hC0 hC1 R hR
  apply (le_div_iff₀ ht).mpr
  nlinarith

end MatrixSpencer
