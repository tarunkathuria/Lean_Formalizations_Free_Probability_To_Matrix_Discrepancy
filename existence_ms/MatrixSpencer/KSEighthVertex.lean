import MatrixSpencer.KSEighthLiveSource

/-! The old truncated-cube potential reaches a full endpoint vertex. -/

open Matrix Filter Topology Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSEighthVertex
open KSPotentialModels KSLiveCurve

variable {N : ℕ} {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

theorem maxFrozen_isVertex (v : Fin N → n → ℂ) {θ : ℝ} (hθ : 0 < θ)
    {x : Fin N → ℝ}
    (hx : MaxFrozenMinimum (1 / 8) (eighthPotential (fun i => KSRankOne.atom (v i)) θ) x) :
    ksVertex (1 / 8) x := by
  classical
  rcases isEmpty_or_nonempty (Live (1 / 8) x) with hI | hI
  · letI := hI
    intro i
    have hi : ¬ |x i| < (1 / 8 : ℝ) := fun hi => isEmptyElim (⟨i, hi⟩ : Live (1 / 8) x)
    have habs : |x i| = (1 / 8 : ℝ) := le_antisymm
      (abs_le.mpr ⟨hx.1.1 i, hx.1.2 i⟩) (not_lt.mp hi)
    rcases le_total (x i) 0 with ht | ht
    · left
      rw [abs_of_nonpos ht] at habs
      linarith
    · right
      rwa [abs_of_nonneg ht] at habs
  · letI := hI
    let vl : Live (1 / 8) x → n → ℂ := fun i => v i
    let xl : Live (1 / 8) x → ℝ := fun i => x i
    let Q := center (fun i => KSRankOne.atom (v i)) x
    have hxl : ∀ i : Live (1 / 8) x, |xl i| ≤ (1 / 8 : ℝ) := fun i => i.property.le
    have hvl : ∀ i, vl i ≠ 0 := fun i => KSFinalAssembly.eighth_live_vector_ne_zero v θ hx i i.property
    have hns₁ : ∀ i : Live (1 / 8) x,
        KSEighthBalanced.owner xl i * KSEighthBalanced.probe (KSEighthSupport.compressedVector vl)
          (KSEighthActualState.transport Q vl xl θ true) i < 1 / 8 - xl i := by
      intro i
      apply lt_of_not_ge
      intro hs
      have hother := mul_nonneg (KSEighthBalanced.owner_pos xl hxl i).le
        (KSEighthActualRetirement.actual_probe_nonneg Q vl hvl xl hxl hθ i false)
      have hret := KSEighthActualRetirement.actual_retire Q vl hvl xl hxl hθ i (1 / 8 - xl i) hs
        (by have hi := (abs_le.mp (hxl i)).2; linarith)
      apply hx.no_update (by norm_num) i i.property (Or.inr rfl)
      rw [KSEighthLiveSource.potential_endpoint v hx.1 hθ i (Or.inr rfl),
        KSEighthLiveSource.potential_state v hx.1 hθ]
      exact hret
    have hns₂ : ∀ i : Live (1 / 8) x,
        KSEighthBalanced.owner xl i * KSEighthBalanced.probe (KSEighthSupport.compressedVector vl)
          (KSEighthActualState.transport Q vl xl θ false) i < 1 / 8 + xl i := by
      intro i
      apply lt_of_not_ge
      intro hs
      have hother := mul_nonneg (KSEighthBalanced.owner_pos xl hxl i).le
        (KSEighthActualRetirement.actual_probe_nonneg Q vl hvl xl hxl hθ i true)
      have hret := KSEighthActualRetirement.actual_retire Q vl hvl xl hxl hθ i (-(1 / 8) - xl i)
        (by have hi := (abs_le.mp (hxl i)).1; linarith) (by linarith)
      apply hx.no_update (by norm_num) i i.property (Or.inl rfl)
      rw [KSEighthLiveSource.potential_endpoint v hx.1 hθ i (Or.inl rfl),
        KSEighthLiveSource.potential_state v hx.1 hθ]
      exact hret
    obtain ⟨h, _, hn⟩ := KSEighthLocalState.exists_not_isLocalMin_curve Q
      (center_isHermitian _ (fun i => KSRankOne.atom_isHermitian (v i)) x)
      vl hvl xl hxl hθ hns₁ hns₂
    exfalso
    apply hn
    have hm := isLocalMin_path hx.1 (eighthPotential (fun i => KSRankOne.atom (v i)) θ)
      (fun y hy => hx.2.1 hy) h
    exact hm.congr (KSEighthLiveSource.potential_path v hx.1 hθ h)

end MatrixSpencer.KSEighthVertex
