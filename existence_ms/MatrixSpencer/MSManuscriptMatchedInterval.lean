import MatrixSpencer.MSManuscriptMatchedFourth

/-!
# Explicit legal intervals and Taylor control for matched movement

The actual interval is derived from the base coefficient floor and 0≤Q≤I.
The final symmetric Taylor bound has only primitive input/order hypotheses;
neither interval legality nor a derivative or remainder bound is assumed.
-/
open Matrix Set Filter
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff Topology
noncomputable section
namespace MatrixSpencer.MSManuscriptMatchedInterval
open KSFrobeniusTangent MSManuscriptMatchedJointBounds
variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n] [Nonempty n]
local instance {k : Type*} [Fintype k] [DecidableEq k] : CStarAlgebra (Matrix k k ℂ) := {}
set_option maxHeartbeats 1000000

def radius (γ : ℝ) : ℝ := min (1/2) (Real.sqrt γ/2)

def fourthBudget (ι n : Type*) [Fintype ι] [Fintype n] (R b θ γ L : ℝ) : ℝ :=
  MSManuscriptMatchedFourth.fourthBudget ι n (R+b) b θ (γ/2) L

theorem radius_pos {γ : ℝ} (hγ : 0 < γ) : 0 < radius γ := by
  unfold radius
  exact lt_min (by norm_num) (div_pos (Real.sqrt_pos.mpr hγ) (by norm_num))

theorem time_bounds {γ t : ℝ} (hγ : 0 < γ) (ht : |t| ≤ radius γ) : |t| ≤ 1 ∧ t^2 ≤ γ/4 := by
  have h1 : |t| ≤ 1/2 := ht.trans (min_le_left _ _)
  have hs : |t| ≤ Real.sqrt γ/2 := ht.trans (min_le_right _ _)
  have hp := (sq_le_sq₀ (abs_nonneg t) (div_nonneg (Real.sqrt_nonneg γ) (by norm_num))).mpr hs
  rw [sq_abs] at hp
  constructor
  · linarith
  · nlinarith [Real.sq_sqrt hγ.le]

theorem covariance_bounds (C Q : selfAdjoint (Matrix ι ι ℝ))
    {γ t : ℝ} (hγ : 0 < γ) (hC : γ•(1 : Matrix ι ι ℝ) ≤ (C : Matrix ι ι ℝ))
    (hC1 : (C : Matrix ι ι ℝ) ≤ 1) (hQ : (Q : Matrix ι ι ℝ).PosSemidef)
    (hQ1 : (Q : Matrix ι ι ℝ) ≤ 1) (ht : |t| ≤ radius γ) :
    (γ/2)•(1 : Matrix ι ι ℝ) ≤ (covariance C Q t : Matrix ι ι ℝ) ∧
      (covariance C Q t : Matrix ι ι ℝ) ≤ 1 := by
  have htime := time_bounds hγ ht
  have hq := smul_le_smul_of_nonneg_left hQ1 (sq_nonneg t)
  have hl : (γ/2)•(1 : Matrix ι ι ℝ) ≤ (γ-t^2)•(1 : Matrix ι ι ℝ) :=
    smul_le_smul_of_nonneg_right (by linarith : γ/2 ≤ γ-t^2) Matrix.PosSemidef.one.nonneg
  constructor
  · exact hl.trans (by simpa only [sub_smul] using sub_le_sub hC hq)
  · exact (sub_le_self _ (hQ.smul (sq_nonneg t)).nonneg).trans hC1

theorem center_bound (H B : selfAdjoint (Matrix n n ℂ)) {R b t : ℝ}
    (hH : ‖(H : Matrix n n ℂ)‖ ≤ R) (hB : ‖(B : Matrix n n ℂ)‖ ≤ b) (ht : |t| ≤ 1) :
    ‖(center H B t : Matrix n n ℂ)‖ ≤ R+b := by
  change ‖(H : Matrix n n ℂ)+t•(B : Matrix n n ℂ)‖ ≤ _
  have hn := norm_add_le (H : Matrix n n ℂ) (t•(B : Matrix n n ℂ))
  rw [norm_smul,Real.norm_eq_abs] at hn
  have hm := mul_le_mul ht hB (norm_nonneg _) (by norm_num : (0:ℝ)≤1)
  linarith

/-- Uniform C∞ and explicit fourth-derivative control on a closed actual
query interval. Positive h is required only to give a nontrivial interval. -/
theorem smooth_and_fourth (H B : selfAdjoint (Matrix n n ℂ))
    (A : ι → Matrix n n ℂ) (hA : ∀i, (A i).IsHermitian) {L : ℝ}
    (hL : 0 ≤ L) (hAnorm : ∀i, ‖A i‖ ≤ L)
    (C Q : selfAdjoint (Matrix ι ι ℝ)) (hQ : (Q : Matrix ι ι ℝ).PosSemidef)
    (hQ1 : (Q : Matrix ι ι ℝ) ≤ 1)
    {θ R b γ h : ℝ} (hθ : 0 < θ) (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hH : ‖(H : Matrix n n ℂ)‖ ≤ R) (hB : ‖(B : Matrix n n ℂ)‖ ≤ b)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hC : γ•(1 : Matrix ι ι ℝ) ≤ (C : Matrix ι ι ℝ)) (hC1 : (C : Matrix ι ι ℝ) ≤ 1)
    (hh : 0 < h) (hstep : h ≤ radius γ/2) :
    let f := fun z => ownerPotential (center H B z) A (covariance C Q z) θ
    ContDiffOn ℝ ∞ f (Icc (-h) h) ∧
      ∀t∈Icc (-h) h, |iteratedDeriv 4 f t| ≤ fourthBudget ι n R b θ γ L := by
  have hr := radius_pos hγ
  have hsmall : h < radius γ := by linarith
  have hsubset : Icc (-h) h ⊆ Ioo (-(radius γ)) (radius γ) := by
    intro t ht
    constructor <;> linarith [ht.1,ht.2]
  have htime (t : ℝ) (ht : t∈Ioo (-(radius γ)) (radius γ)) : |t| ≤ radius γ :=
    (abs_lt.mpr ht).le
  have hc (t : ℝ) (ht : t∈Ioo (-(radius γ)) (radius γ)) := covariance_bounds C Q hγ hC hC1 hQ hQ1 (htime t ht)
  have hcenter (t : ℝ) (ht : t∈Ioo (-(radius γ)) (radius γ)) :
      ‖(center H B t : Matrix n n ℂ)‖ ≤ R+b := center_bound H B hH hB (time_bounds hγ (htime t ht)).1
  have hqnorm := MSManuscriptComplexSourceNorm.real_coefficient_norm_le_one hQ hQ1
  constructor
  · exact (MSManuscriptMatchedFourth.potential_contDiffOn H B A hA C Q hθ (by positivity : 0 < γ/2)
      (fun t ht => (hc t ht).1)).mono hsubset
  · intro t ht
    exact MSManuscriptMatchedFourth.potential_fourth_le H B A hA hL hAnorm C Q hqnorm hθ
      (add_nonneg hR hb) hb hB (by positivity : 0 < γ/2) (by linarith : γ/2 ≤ 1)
      isOpen_Ioo (fun t ht => (hc t ht).1) (fun t ht => (hc t ht).2)
      hcenter (fun t ht => (time_bounds hγ (htime t ht)).1) (hsubset ht)

/-- A scalar bundling lemma keeps the large actual objective opaque while
passing smoothness and the proved fourth bound to Lagrange Taylor. -/
theorem average_of_smooth_and_fourth (f : ℝ → ℝ) {h M : ℝ} (hh : 0 < h)
    (hf : ContDiffOn ℝ ∞ f (Icc (-h) h) ∧
      ∀t∈Icc (-h) h, |iteratedDeriv 4 f t| ≤ M) :
    |(f h+f (-h))/2-f 0-iteratedDeriv 2 f 0*h^2/2| ≤ M*h^4/24 :=
  KSFourthDifference.symmetric_average_error_zero f hh
    (hf.1.of_le (WithTop.coe_le_coe.mpr (show (4 : ℕ∞) ≤ ⊤ from le_top))) hf.2

/-- Both random signs use their actual matched ownerPotential values. -/
theorem symmetric_average_error (H B : selfAdjoint (Matrix n n ℂ))
    (A : ι → Matrix n n ℂ) (hA : ∀i, (A i).IsHermitian) {L : ℝ}
    (hL : 0 ≤ L) (hAnorm : ∀i, ‖A i‖ ≤ L)
    (C Q : selfAdjoint (Matrix ι ι ℝ)) (hQ : (Q : Matrix ι ι ℝ).PosSemidef)
    (hQ1 : (Q : Matrix ι ι ℝ) ≤ 1)
    {θ R b γ h : ℝ} (hθ : 0 < θ) (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hH : ‖(H : Matrix n n ℂ)‖ ≤ R) (hB : ‖(B : Matrix n n ℂ)‖ ≤ b)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hC : γ•(1 : Matrix ι ι ℝ) ≤ (C : Matrix ι ι ℝ)) (hC1 : (C : Matrix ι ι ℝ) ≤ 1)
    (hh : 0 < h) (hstep : h ≤ radius γ/2) :
    let f := fun z => ownerPotential (center H B z) A (covariance C Q z) θ
    |(f h+f (-h))/2-f 0-iteratedDeriv 2 f 0*h^2/2| ≤ fourthBudget ι n R b θ γ L*h^4/24 := by
  let f : ℝ → ℝ := fun z => ownerPotential (center H B z) A (covariance C Q z) θ
  let M : ℝ := fourthBudget ι n R b θ γ L
  change |(f h+f (-h))/2-f 0-iteratedDeriv 2 f 0*h^2/2| ≤ M*h^4/24
  have hf : ContDiffOn ℝ ∞ f (Icc (-h) h) ∧ ∀t∈Icc (-h) h, |iteratedDeriv 4 f t| ≤ M :=
    smooth_and_fourth (θ := θ) (R := R) (b := b) (γ := γ) (h := h) (L := L) H B A hA hL hAnorm C Q hQ hQ1 hθ hR hb hH hB hγ hγ1 hC hC1 hh hstep
  exact average_of_smooth_and_fourth f hh hf

end MatrixSpencer.MSManuscriptMatchedInterval
