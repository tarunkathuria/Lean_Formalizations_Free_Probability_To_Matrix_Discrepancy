import MatrixSpencer.KSFullManuscriptEllipsoidFactor
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Affine central-cut updates in physical coordinates

An ellipsoid is represented by its center and a linear unit-ball factor.
The physical separating vector is pulled back by the adjoint, normalized,
and used in the explicitly proved central-cut factor update. Containment
and surjectivity of the updated factor are proved. The separating vector
is input here; no SDP separation algorithm is asserted by this module.
-/

open scoped InnerProductSpace
noncomputable section
namespace MatrixSpencer.KSFullManuscriptEllipsoidAffine

open KSFullManuscriptEllipsoidFactor
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def factorCLM (ℓ : ℝ) (a : E) : E →L[ℝ] E :=
  transverse ℓ • ContinuousLinearMap.id ℝ E +
    (axial ℓ - transverse ℓ) • (innerSL ℝ a).smulRight a

omit [CompleteSpace E] in
theorem factorCLM_apply (ℓ : ℝ) (a v : E) : factorCLM ℓ a v = factor ℓ a v := by
  simp only [factorCLM, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply,
    factor, axialMap, smul_smul]

structure State (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  center : E
  factor : E →L[ℝ] E

def body (s : State E) : Set E :=
  {y | ∃ z : E, ‖z‖ ≤ 1 ∧ y = s.center + s.factor z}

def cutVector (s : State E) (g : E) : E := s.factor.adjoint g
def cutNormal (s : State E) (g : E) : E := ‖cutVector s g‖⁻¹ • cutVector s g

/-- The physical center and factor updates. `transverse ℓ` is a single
dimension-dependent square root; the cut normalization is a vector norm. -/
def update (ℓ : ℝ) (s : State E) (g : E) : State E where
  center := s.center + s.factor (KSFullManuscriptEllipsoid.center ℓ (cutNormal s g))
  factor := s.factor.comp (factorCLM ℓ (cutNormal s g))

theorem cutVector_ne_zero (s : State E) (hs : Function.Surjective s.factor)
    {g : E} (hg : g ≠ 0) : cutVector s g ≠ 0 := by
  intro hz
  obtain ⟨z, hz'⟩ := hs g
  have hi := s.factor.adjoint_inner_left z g
  rw [← cutVector, hz, inner_zero_left, hz', real_inner_self_eq_norm_sq] at hi
  have hn := norm_pos_iff.mpr hg
  nlinarith

theorem cutNormal_norm (s : State E) {g : E} (hg : cutVector s g ≠ 0) :
    ‖cutNormal s g‖ = 1 := by
  have hn : ‖cutVector s g‖ ≠ 0 := norm_ne_zero_iff.mpr hg
  rw [cutNormal, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_nonneg (norm_nonneg _), inv_mul_cancel₀ hn]

theorem cutNormal_inner (s : State E) (g z : E) :
    ⟪cutNormal s g, z⟫_ℝ = ⟪g, s.factor z⟫_ℝ / ‖cutVector s g‖ := by
  rw [cutNormal, real_inner_smul_left, cutVector, s.factor.adjoint_inner_left]
  ring

theorem update_surjective {ℓ : ℝ} (hℓ : 1 < ℓ) (s : State E)
    (hs : Function.Surjective s.factor) {g : E} (hg : g ≠ 0) :
    Function.Surjective (update ℓ s g).factor := by
  intro y
  obtain ⟨z, hz⟩ := hs y
  refine ⟨inverseFactor ℓ (cutNormal s g) z, ?_⟩
  change s.factor (factorCLM ℓ (cutNormal s g) (inverseFactor ℓ (cutNormal s g) z)) = y
  rw [factorCLM_apply, factor_inverseFactor hℓ
    (cutNormal_norm s (cutVector_ne_zero s hs hg)), hz]

/-- A central cut in the physical coordinates retains its entire old
ellipsoid intersection in the computed new ellipsoid. -/
theorem retained_subset_update {ℓ : ℝ} (hℓ : 1 < ℓ) (s : State E)
    (hs : Function.Surjective s.factor) {g : E} (hg : g ≠ 0) :
    {y | y ∈ body s ∧ ⟪g, y - s.center⟫_ℝ ≤ 0} ⊆ body (update ℓ s g) := by
  rintro y ⟨⟨z, hz, rfl⟩, hcut⟩
  have ha := cutNormal_norm s (cutVector_ne_zero s hs hg)
  have hnormcut : ⟪cutNormal s g, z⟫_ℝ ≤ 0 := by
    rw [cutNormal_inner]
    exact div_nonpos_of_nonpos_of_nonneg
      (by simpa only [add_sub_cancel_left] using hcut) (norm_nonneg _)
  have he := KSFullManuscriptEllipsoid.halfBall_subset_ellipsoid hℓ ha ⟨hz, hnormcut⟩
  obtain ⟨w, hw, hzw⟩ := (mem_ellipsoid_iff hℓ ha z).mp he
  refine ⟨w, hw, ?_⟩
  change s.center + s.factor z =
    (s.center + s.factor (KSFullManuscriptEllipsoid.center ℓ (cutNormal s g))) +
      s.factor (factorCLM ℓ (cutNormal s g) w)
  rw [factorCLM_apply, hzw, map_add]
  abel

end MatrixSpencer.KSFullManuscriptEllipsoidAffine
