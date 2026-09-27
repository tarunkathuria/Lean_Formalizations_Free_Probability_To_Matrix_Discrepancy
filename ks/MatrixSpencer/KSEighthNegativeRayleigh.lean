import MatrixSpencer.KSEighthFacePotential
import MatrixSpencer.KSEighthPreparedHessian

/-!
# Negative least Rayleigh value in the actual eighth Hessian coordinates

The known eighth transport descent is expressed in the same finite weighted
coordinates used by the numerical Hessian and Jacobi routines. Normalizing the
negative direction is only a variational proof witness; the numerical algorithm
will compute its own approximate Jacobi direction from finite value reports.
-/

open Set
open scoped BigOperators
noncomputable section
namespace MatrixSpencer.KSEighthNegativeRayleigh
open KSEighthLiveEnumeration KSEighthLiveCoordinates KSLiveCurve
variable {N : ℕ}

def inverseDirection (x : Fin N → ℝ) (h : Live (1/8) x → ℝ) : EuclideanSpace ℝ (Fin (count x)) :=
  WithLp.toLp 2 (fun j => h (liveEquiv x j) / Real.sqrt (1 - x (liveEquiv x j) ^ 2))

theorem liveWeight_pos (x : Fin N → ℝ) (i : Live (1/8) x) : 0 < Real.sqrt (1 - x i ^ 2) := by
  apply Real.sqrt_pos.mpr
  have hi := i.property
  nlinarith [sq_abs (x i), abs_nonneg (x i)]

theorem weighted_inverse (x : Fin N → ℝ) (h : Live (1/8) x → ℝ) (i : Fin N) :
    weightedMap x (inverseDirection x h) i = KSLiveCurve.extend (1/8) x h i := by
  rw [weightedMap_apply]
  by_cases hi : |x i| < (1/8 : ℝ)
  · let j : Live (1/8) x := ⟨i, hi⟩
    change Real.sqrt (1 - x j ^ 2) * KSEighthLiveEnumeration.extend x (inverseDirection x h) j = _
    rw [KSEighthLiveEnumeration.extend_live]
    change Real.sqrt (1 - x j ^ 2) *
      (h (liveEquiv x ((liveEquiv x).symm j)) /
        Real.sqrt (1 - x (liveEquiv x ((liveEquiv x).symm j)) ^ 2)) = _
    rw [(liveEquiv x).apply_symm_apply, mul_div_cancel₀ _ (liveWeight_pos x j).ne']
    exact (KSLiveCurve.extend_live (1/8) x h j).symm
  · rw [KSEighthLiveEnumeration.extend_dead x _ i hi, KSLiveCurve.extend_dead (1/8) x h i hi, mul_zero]

theorem inverseDirection_ne_zero (x : Fin N → ℝ) {h : Live (1/8) x → ℝ} (hh : h ≠ 0) :
    inverseDirection x h ≠ 0 := by
  intro hz
  apply KSLiveCurve.extend_ne_zero (1/8) x hh
  funext i
  rw [← weighted_inverse x h i, hz, map_zero]

/-- The coefficient paths agree exactly, not just through a derivative. -/
theorem face_inverse_smul (x : Fin N → ℝ) (h : Live (1/8) x → ℝ) (t : ℝ) :
    face x (t • inverseDirection x h) = path (1/8) x h t := by
  funext i
  rw [face, map_smul]
  change x i + t * weightedMap x (inverseDirection x h) i = _
  rw [weighted_inverse]
  rfl


theorem lineDirection_inverse (x : Fin N → ℝ) (h : Live (1/8) x → ℝ) :
    KSEighthFacePotential.lineDirection x (inverseDirection x h) = h := by
  funext i
  exact (weighted_inverse x h i).trans (KSLiveCurve.extend_live (1/8) x h i)

/-- Generic variational conversion, reproduced without any full-cube theorem. -/
theorem leastRayleigh_neg_of_negative_second {m : ℕ}
    (f : EuclideanSpace ℝ (Fin m) → ℝ) (w : EuclideanSpace ℝ (Fin m))
    (hf : ContDiffAt ℝ 2 f 0) (hw : w ≠ 0)
    (hnegative : iteratedDeriv 2 (fun t : ℝ => f (t • w)) 0 < 0) :
    KSRayleighAccuracy.leastRayleigh (KSNumericalHessian.hessian f 0) < 0 := by
  have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hi : 0 < ‖w‖⁻¹ := inv_pos.mpr hn
  let u : EuclideanSpace ℝ (Fin m) := ‖w‖⁻¹ • w
  have hu : ‖u‖ = 1 := by
    rw [show u = ‖w‖⁻¹ • w from rfl, norm_smul, Real.norm_eq_abs,
      abs_of_pos hi, inv_mul_cancel₀ (ne_of_gt hn)]
  have hq : fderiv ℝ (fderiv ℝ f) 0 w w < 0 := by
    have he := KSFourthDifference.line_second f 0 w hf
    simp only [zero_add] at he
    rwa [he] at hnegative
  have hscaled : KSRayleighAccuracy.realRayleigh (KSNumericalHessian.hessian f 0) u < 0 := by
    rw [KSNumericalHessian.hessian_rayleigh]
    change fderiv ℝ (fderiv ℝ f) 0 (‖w‖⁻¹ • w) (‖w‖⁻¹ • w) < 0
    simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    exact mul_neg_of_pos_of_neg hi (mul_neg_of_pos_of_neg hi hq)
  exact (KSRayleighAccuracy.leastRayleigh_le _ u hu).trans_lt hscaled

/-- Negative curvature of the actual retained-mask function at the actual
numerically prepared state; all primitive report guarantees are proved. -/
theorem numerical_prepared_leastRayleigh_neg {d : ℕ}
    (v : Fin N → Fin d → ℂ) {θ τ ρ : ℝ} (hθ : 0 < θ) (hτ : 0 < τ) (hd : 0 < d)
    (s : KSEighthWalkRun.PreparedState N ρ τ
      (KSEighthNumericalValue.stateReport v θ hd (τ/8)))
    (hactive : ¬KSEighthWalkRun.terminal s) :
    KSRayleighAccuracy.leastRayleigh (KSNumericalHessian.hessian
      (KSEighthFacePotential.potential v θ s.coeff) 0) < 0 := by
  classical
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  have hlive := count_pos_of_not_vertex s.cube hactive
  letI : Nonempty (Live (1/8) s.coeff) := ⟨liveEquiv s.coeff ⟨0,hlive⟩⟩
  obtain ⟨h, hn, _, hdd⟩ := KSEighthPreparedHessian.exists_negative_second_curve_of_exhaustion
    v hθ hτ.le _ (fun x hx => KSEighthNumericalValue.stateReport_accuracy v hθ
      (div_pos hτ (by norm_num)) hd hx) s.cube s.exhausted
  let w := inverseDirection s.coeff h
  apply leastRayleigh_neg_of_negative_second _ w
    ((KSEighthFacePotential.contDiffAt_potential v hθ s.coeff).of_le
      (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)))
    (inverseDirection_ne_zero s.coeff hn)
  have he : (fun t : ℝ => KSEighthFacePotential.potential v θ s.coeff (t • w)) =
      KSEighthLocalState.curvePotential
        (KSPotentialModels.center (fun i => KSRankOne.atom (v i)) s.coeff)
        (fun i : Live (1/8) s.coeff => v i) θ (fun i => s.coeff i) h := by
    funext t
    rw [KSEighthFacePotential.potential_line_eq, lineDirection_inverse]
  rwa [he]

end MatrixSpencer.KSEighthNegativeRayleigh
