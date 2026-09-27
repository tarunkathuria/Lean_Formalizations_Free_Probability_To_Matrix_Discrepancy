import HigherRankKSRuntime.NextEvent

/-! A unit active direction stays in the cube and keeps positive reserve
throughout the chosen local step. Inactive original owners do not move. -/
noncomputable section
open scoped BigOperators
namespace HigherRankKSRuntime.NextEvent
open AugmentedHigherRankKS ActiveEnumeration
variable {N : ℕ}

theorem clean_movement_feasible {a R ρ ζ h : ℝ} (ha : 0 < a)
    (hρ : 0 ≤ ρ) (hh : |h| ≤ ρ) (hreserve : a*h^2 ≤ ζ)
    {z : EpochState (Fin N)} (hz : z ∈ epochDomain a R) (hc : Clean z ρ ζ)
    (v : EuclideanSpace ℝ (Fin (count z))) (hv : ‖v‖ ≤ 1) :
    movement a z (extend z v) h ∈ epochDomain a R := by
  have hn : ‖extend z v‖ ≤ 1 := by rw [extend_norm]; exact hv
  have hcoord (i : Fin N) : |extend z v i| ≤ 1 := by
    have hh : |extend z v i| ≤ ‖extend z v‖ := by
      simpa only [Real.norm_eq_abs] using (PiLp.norm_apply_le (extend z v) i)
    exact hh.trans hn
  have hactive (i : Fin N) (hi : extend z v i ≠ 0) : 0 < reserve z i := by
    by_contra hh
    exact hi (extend_inactive z v i hh)
  apply movement_feasible hz ha (extend z v) h
  · intro i hi
    have he := (hc i (hactive i hi)).1
    linarith
  · intro i
    by_cases hi : 0 < reserve z i
    · have hx := (hc i hi).1
      have hb : |h*extend z v i| ≤ ρ := by
        rw [abs_mul]
        exact (mul_le_mul_of_nonneg_left (hcoord i) (abs_nonneg h)).trans (by simpa using hh)
      have ht : |position z i+h*extend z v i| ≤ 1 := by
        exact (abs_add_le _ _).trans (by linarith)
      exact abs_le.mp ht
    · rw [extend_inactive z v i hi,mul_zero,add_zero]
      exact ⟨(hz i).1,(hz i).2.1⟩
  · intro i
    by_cases hi : 0 < reserve z i
    · have hs : (extend z v i)^2 ≤ 1 := (sq_le_one_iff_abs_le_one _).mpr (hcoord i)
      have hb := mul_le_mul_of_nonneg_left hs (mul_nonneg ha.le (sq_nonneg h))
      rw [mul_pow]
      have hc0 : 0 ≤ reserve z i := hi.le
      nlinarith [(hc i hi).2]
    · rw [extend_inactive z v i hi,mul_zero,zero_pow (by omega),mul_zero]
      exact (hz i).2.2.2.2.1

end HigherRankKSRuntime.NextEvent
