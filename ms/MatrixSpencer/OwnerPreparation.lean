import MatrixSpencer.OwnerBounds
import MatrixSpencer.CovariancePreparation

/-!
# Compact preparation of the actual owner potential

The generic compact minimization theorem is instantiated with the actual
optimized potential. Its continuity and paid trace budget are discharged.
The actual covariance derivative and resulting observed response cap are
separate later obligations.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix Set

noncomputable section

namespace MatrixSpencer

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n]

theorem continuousOn_ownerPotential_covariance (H : Matrix n n ℂ)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) (θ : ℝ) (C : Matrix ι ι ℝ) :
    ContinuousOn (fun K => ownerPotential H A K θ) (Icc 0 C) := by
  apply continuousOn_iff_continuous_restrict.mpr
  have hm : Continuous (fun K : Icc (0 : Matrix ι ι ℝ) C =>
      (H, (⟨K.val, K.property.1.posSemidef⟩ : {Q : Matrix ι ι ℝ // Q.PosSemidef}))) := by
    have hk : Continuous (fun K : Icc (0 : Matrix ι ι ℝ) C => K.val) := continuous_subtype_val
    exact continuous_const.prodMk (hk.subtype_mk (fun K => K.property.1.posSemidef))
  have hc : Continuous ((fun p : Matrix n n ℂ × {Q : Matrix ι ι ℝ // Q.PosSemidef} =>
      ownerPotential p.1 A p.2 θ) ∘ (fun K : Icc (0 : Matrix ι ι ℝ) C =>
      (H, (⟨K.val, K.property.1.posSemidef⟩ : {Q : Matrix ι ι ℝ // Q.PosSemidef})))) :=
    Continuous.comp (continuous_ownerPotential_psd A hA θ) hm
  simpa only [Function.comp_def] using hc

/-- There is an actual minimizing owner, and its trace withdrawal is paid by potential decrease. -/
theorem exists_owner_preparation (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (θ t : ℝ) :
    ∃ K ∈ Icc 0 C,
      IsMinOn (covarianceObjective C (fun Q => ownerPotential H A Q θ) t) (Icc 0 C) K ∧
      ownerPotential H A K θ + t * realTrace (C - K) ≤ ownerPotential H A C θ := by
  exact exists_covariance_minimizer_of_continuousOn hC
    (continuousOn_ownerPotential_covariance H A hA θ C) t

/-- A positive trace price bounds the total trace that preparation can remove. -/
theorem exists_owner_preparation_trace_budget [Nonempty n]
    (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (hN : ∀ i, ‖A i‖ ≤ 1) {C : Matrix ι ι ℝ} (hC0 : C.PosSemidef) (hC1 : C ≤ 1)
    (θ : ℝ) {t : ℝ} (ht : 0 < t) :
    ∃ K ∈ Icc 0 C,
      IsMinOn (covarianceObjective C (fun Q => ownerPotential H A Q θ) t) (Icc 0 C) K ∧
      ownerPotential H A K θ + t * realTrace (C - K) ≤ ownerPotential H A C θ ∧
      0 ≤ realTrace (C - K) ∧
      realTrace (C - K) ≤ 2 * Real.sqrt (Fintype.card ι : ℝ) / t := by
  obtain ⟨K, hK, hmin, hpaid⟩ := exists_owner_preparation H A hA hC0 θ t
  refine ⟨K, hK, hmin, hpaid, realTrace_nonneg (sub_nonneg.mpr hK.2).posSemidef, ?_⟩
  have hbase := baseDensityPotential_le_owner H A hA hK.1.posSemidef θ
  have hupper := ownerPotential_le_base_add H A hA hN hC0 hC1 θ
  apply (le_div_iff₀ ht).mpr
  nlinarith

end MatrixSpencer
