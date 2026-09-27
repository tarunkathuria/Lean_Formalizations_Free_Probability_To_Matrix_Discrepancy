import MatrixSpencer.KSFisher
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Strict negative subspaces in the truncated-cube proof

The dimension estimate is obtained from the actual orthonormal diagonalization
and the trace bound. Pullbacks need no inverse: strict negativity proves
injectivity on the relevant subspace.
-/

open scoped BigOperators Matrix MatrixOrder
open Matrix Module

noncomputable section
set_option maxHeartbeats 800000

namespace MatrixSpencer.KSEighthInertia

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def StrictlyNegativeOn (K : Matrix ι ι ℝ) (U : Submodule ℝ (ι → ℝ)) : Prop :=
  ∀ x ∈ U, x ≠ 0 → x ⬝ᵥ (K *ᵥ x) < 0

theorem quadratic_congruence (L K : Matrix ι ι ℝ) (x : ι → ℝ) :
    x ⬝ᵥ ((Lᵀ * K * L) *ᵥ x) = (L *ᵥ x) ⬝ᵥ (K *ᵥ (L *ᵥ x)) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dotProduct_mulVec,
    vecMul_transpose]

/-- A negative pullback is injective on the subspace, regardless of its kernel
on the ambient space. -/
theorem negative_pullback_injective (L K : Matrix ι ι ℝ)
    (U : Submodule ℝ (ι → ℝ)) (hU : StrictlyNegativeOn (Lᵀ * K * L) U) :
    Function.Injective (L.mulVecLin.domRestrict U) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  by_contra hne
  have hne' : (x : ι → ℝ) ≠ 0 := fun h => hne (Subtype.ext h)
  have hn := hU x x.property hne'
  rw [quadratic_congruence] at hn
  change L *ᵥ (x : ι → ℝ) = 0 at hx
  simp only [hx, Matrix.mulVec_zero, dotProduct_zero] at hn
  exact (lt_irrefl 0) hn

theorem negative_pullback_image (L K : Matrix ι ι ℝ)
    (U : Submodule ℝ (ι → ℝ)) (hU : StrictlyNegativeOn (Lᵀ * K * L) U) :
    StrictlyNegativeOn K (U.map L.mulVecLin) ∧
      finrank ℝ (U.map L.mulVecLin) = finrank ℝ U := by
  constructor
  · intro y hy hne
    rcases hy with ⟨x, hx, rfl⟩
    have hxne : x ≠ 0 := by
      intro h
      apply hne
      simp [h]
    simpa only [quadratic_congruence, Matrix.mulVecLin_apply] using hU x hx hxne
  · have h := LinearMap.finrank_range_of_inj (negative_pullback_injective L K U hU)
    rwa [LinearMap.range_domRestrict] at h

def restrictCoordinates (s : Finset ι) : (ι → ℝ) →ₗ[ℝ] (s → ℝ) where
  toFun x i := x i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def lowCoordinates (s : Finset ι) : Submodule ℝ (ι → ℝ) :=
  LinearMap.ker (restrictCoordinates s)

theorem lowCoordinates_vanish {s : Finset ι} {x : ι → ℝ}
    (hx : x ∈ lowCoordinates s) {i : ι} (hi : i ∈ s) : x i = 0 := by
  change restrictCoordinates s x = 0 at hx
  exact congrFun hx ⟨i, hi⟩

theorem lowCoordinates_dimension (s : Finset ι) :
    Fintype.card ι ≤ finrank ℝ (lowCoordinates s) + s.card := by
  have hnull := (restrictCoordinates s).finrank_range_add_finrank_ker
  have hr := (LinearMap.range (restrictCoordinates s)).finrank_le
  simp only [Module.finrank_pi, Module.finrank_self, Finset.sum_const, smul_eq_mul,
    Nat.mul_one, Fintype.card_coe] at hnull hr
  change Fintype.card ι ≤ finrank ℝ (LinearMap.ker (restrictCoordinates s)) + s.card
  omega

/-- Markov's counting bound for a concrete PSD real matrix spectrum. -/
theorem high_eigenvalue_count {H : Matrix ι ι ℝ} (hH : H.PosSemidef) (t : ℝ) :
    t * ((Finset.univ.filter (fun i => t ≤ hH.isHermitian.eigenvalues i)).card : ℝ) ≤
      Matrix.trace H := by
  classical
  calc
    _ = ∑ i ∈ Finset.univ.filter (fun i => t ≤ hH.isHermitian.eigenvalues i), t := by
      simp [mul_comm]
    _ ≤ ∑ i ∈ Finset.univ.filter (fun i => t ≤ hH.isHermitian.eigenvalues i),
        hH.isHermitian.eigenvalues i := by
      apply Finset.sum_le_sum
      intro i hi
      exact (Finset.mem_filter.mp hi).2
    _ ≤ ∑ i, hH.isHermitian.eigenvalues i := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun i _ _ => hH.eigenvalues_nonneg i)
    _ = _ := by simpa only [RCLike.ofReal_real_eq_id, id_eq] using
      hH.isHermitian.trace_eq_sum_eigenvalues.symm

theorem diagonal_low_strictly_negative (eigenval : ι → ℝ) (t : ℝ) :
    StrictlyNegativeOn (Matrix.diagonal eigenval - t • (1 : Matrix ι ι ℝ))
      (lowCoordinates (Finset.univ.filter (fun i => t ≤ eigenval i))) := by
  classical
  intro x hx hne
  have hterm (i : ι) : (eigenval i - t) * x i ^ 2 ≤ 0 := by
    by_cases hi : t ≤ eigenval i
    · have hz := lowCoordinates_vanish hx (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
      simp [hz]
    · exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (le_of_not_ge hi)) (sq_nonneg _)
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    apply hne
    funext i
    simpa using not_exists.mp h i
  have hilow : eigenval i < t := by
    by_contra h
    exact hi (lowCoordinates_vanish hx
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_of_not_gt h⟩))
  have hstrict : (eigenval i - t) * x i ^ 2 < 0 :=
    mul_neg_of_neg_of_pos (sub_neg.mpr hilow) (sq_pos_of_ne_zero hi)
  have hsum := Finset.sum_lt_sum (fun j (_ : j ∈ (Finset.univ : Finset ι)) => hterm j)
    ⟨i, Finset.mem_univ _, hstrict⟩
  simp only [Finset.sum_const_zero] at hsum
  convert hsum using 1
  simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_sub, dotProduct_smul, dotProduct, Matrix.mulVec_diagonal,
    Finset.mul_sum, ← Finset.sum_sub_distrib, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Every PSD coefficient matrix has a large subspace strictly below a positive
spectral threshold. The real dimension bound is derived from its actual trace. -/
theorem exists_large_negative_subspace {H : Matrix ι ι ℝ}
    (hH : H.PosSemidef) {t : ℝ} (ht : 0 < t) :
    ∃ U : Submodule ℝ (ι → ℝ),
      (Fintype.card ι : ℝ) - Matrix.trace H / t ≤ (finrank ℝ U : ℝ) ∧
      StrictlyNegativeOn (H - t • (1 : Matrix ι ι ℝ)) U := by
  classical
  let V : Matrix ι ι ℝ := hH.isHermitian.eigenvectorUnitary
  let s := Finset.univ.filter (fun i => t ≤ hH.isHermitian.eigenvalues i)
  have hvstar : star V = Vᵀ := by
    ext i j
    change star (V j i) = V j i
    exact star_trivial _
  have hv : Vᵀ * V = 1 := by
    rw [← hvstar]
    exact unitary.coe_star_mul_self hH.isHermitian.eigenvectorUnitary
  have hd : Vᵀ * H * V = Matrix.diagonal hH.isHermitian.eigenvalues := by
    rw [← hvstar]
    simpa only [RCLike.ofReal_real_eq_id, Function.id_comp] using
      hH.isHermitian.star_mul_self_mul_eq_diagonal
  have he : Vᵀ * (H - t • (1 : Matrix ι ι ℝ)) * V =
      Matrix.diagonal hH.isHermitian.eigenvalues - t • (1 : Matrix ι ι ℝ) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, hv, hd]
  have hneg : StrictlyNegativeOn (Vᵀ * (H - t • (1 : Matrix ι ι ℝ)) * V)
      (lowCoordinates s) := by
    rw [he]
    exact diagonal_low_strictly_negative _ _
  have himage := negative_pullback_image V (H - t • (1 : Matrix ι ι ℝ))
    (lowCoordinates s) hneg
  refine ⟨(lowCoordinates s).map V.mulVecLin, ?_, himage.1⟩
  rw [himage.2]
  have hc : (s.card : ℝ) ≤ Matrix.trace H / t := by
    apply (le_div_iff₀ ht).mpr
    simpa only [s, mul_comm] using high_eigenvalue_count hH t
  have hdim : (Fintype.card ι : ℝ) ≤ (finrank ℝ (lowCoordinates s) : ℝ) + s.card := by
    exact_mod_cast lowCoordinates_dimension s
  linarith

/-- The concrete positive diagonal normalization used in the eighth-cube proof. -/
def diagonalWhitening (g : ι → ℝ) : Matrix ι ι ℝ :=
  Matrix.diagonal (fun i => (Real.sqrt (g i))⁻¹)

theorem diagonalWhitening_scalar (g : ℝ) (hg : 0 < g) :
    (Real.sqrt g)⁻¹ * g * (Real.sqrt g)⁻¹ = 1 := by
  have hs := Real.sq_sqrt hg.le
  have hsn : Real.sqrt g ≠ 0 := (Real.sqrt_pos.mpr hg).ne'
  field_simp [hsn]
  nlinarith

theorem diagonalWhitening_normalizes (g : ι → ℝ) (hg : ∀ i, 0 < g i) :
    (diagonalWhitening g)ᵀ * Matrix.diagonal g * diagonalWhitening g = 1 := by
  rw [diagonalWhitening, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  exact diagonalWhitening_scalar (g i) (hg i)

theorem diagonalWhitening_trace {Γ : Matrix ι ι ℝ} (g : ι → ℝ)
    (hg : ∀ i, 0 < g i) (hdiag : ∀ i, Γ i i = g i) :
    Matrix.trace ((diagonalWhitening g)ᵀ * Γ * diagonalWhitening g) = Fintype.card ι := by
  simp only [diagonalWhitening, Matrix.diagonal_transpose, Matrix.trace, Matrix.diag,
    Matrix.mul_diagonal, Matrix.diagonal_mul, hdiag, diagonalWhitening_scalar _ (hg _),
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

/-- The normalized trace equals the number of labels because the two actual
diagonals agree. No dimension or inertia bound is assumed. -/
theorem exists_large_negative_subspace_diagonal {Γ : Matrix ι ι ℝ}
    (hΓ : Γ.PosSemidef) (g : ι → ℝ) (hg : ∀ i, 0 < g i)
    (hdiag : ∀ i, Γ i i = g i) {t : ℝ} (ht : 0 < t) :
    ∃ U : Submodule ℝ (ι → ℝ),
      (Fintype.card ι : ℝ) - Fintype.card ι / t ≤ (finrank ℝ U : ℝ) ∧
      StrictlyNegativeOn (Γ - t • Matrix.diagonal g) U := by
  let W := diagonalWhitening g
  have hw : Wᴴ = Wᵀ := by
    ext i j
    exact star_trivial _
  have hH : (Wᵀ * Γ * W).PosSemidef := by
    rw [← hw]
    exact hΓ.conjTranspose_mul_mul_same W
  obtain ⟨U, hdim, hneg⟩ := exists_large_negative_subspace hH ht
  have he : Wᵀ * (Γ - t • Matrix.diagonal g) * W = Wᵀ * Γ * W - t • 1 := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]
    rw [diagonalWhitening_normalizes g hg]
  have hpull : StrictlyNegativeOn (Wᵀ * (Γ - t • Matrix.diagonal g) * W) U := by
    rwa [he]
  have himage := negative_pullback_image W (Γ - t • Matrix.diagonal g) U hpull
  refine ⟨U.map W.mulVecLin, ?_, himage.1⟩
  rw [himage.2]
  simpa only [W, diagonalWhitening_trace g hg hdiag] using hdim

theorem strictlyNegativeOn_smul {K : Matrix ι ι ℝ} {U : Submodule ℝ (ι → ℝ)}
    (hK : StrictlyNegativeOn K U) {a : ℝ} (ha : 0 < a) :
    StrictlyNegativeOn (a • K) U := by
  intro x hx hne
  simpa only [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] using
    mul_neg_of_pos_of_neg ha (hK x hx hne)

/-- The precise inertia estimate for A Γ − b G. -/
theorem exists_large_negative_comparison {Γ : Matrix ι ι ℝ}
    (hΓ : Γ.PosSemidef) (g : ι → ℝ) (hg : ∀ i, 0 < g i)
    (hdiag : ∀ i, Γ i i = g i) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∃ U : Submodule ℝ (ι → ℝ),
      (1 - a / b) * Fintype.card ι ≤ (finrank ℝ U : ℝ) ∧
      StrictlyNegativeOn (a • Γ - b • Matrix.diagonal g) U := by
  obtain ⟨U, hdim, hneg⟩ := exists_large_negative_subspace_diagonal
    hΓ g hg hdiag (div_pos hb ha)
  refine ⟨U, ?_, ?_⟩
  · convert hdim using 1
    field_simp [ha.ne', hb.ne']
    <;> ring
  · have he : a • (Γ - (b / a) • Matrix.diagonal g) =
        a • Γ - b • Matrix.diagonal g := by
      rw [smul_sub, smul_smul, mul_div_cancel₀ _ ha.ne']
    rw [← he]
    exact strictlyNegativeOn_smul hneg ha

/-- Intersecting two strict negative subspaces costs at most the ambient
dimension, with the actual common quadratic form dominated by their sum. -/
theorem intersect_negative_subspaces {K K₁ K₂ : Matrix ι ι ℝ}
    (hK : K ≤ K₁ + K₂) {U₁ U₂ : Submodule ℝ (ι → ℝ)}
    (h₁ : StrictlyNegativeOn K₁ U₁) (h₂ : StrictlyNegativeOn K₂ U₂) :
    StrictlyNegativeOn K (U₁ ⊓ U₂) ∧
      finrank ℝ U₁ + finrank ℝ U₂ ≤
        finrank ℝ ↥(U₁ ⊓ U₂) + Fintype.card ι := by
  constructor
  · intro x hx hne
    have hq := (Matrix.le_iff.mp hK).2 x
    simp only [star_trivial, Matrix.sub_mulVec, Matrix.add_mulVec, dotProduct_sub,
      dotProduct_add] at hq
    have hq₁ := h₁ x hx.1 hne
    have hq₂ := h₂ x hx.2 hne
    linarith
  · have he := Submodule.finrank_sup_add_finrank_inf_eq U₁ U₂
    have hs := (U₁ ⊔ U₂).finrank_le
    simp only [Module.finrank_pi] at hs
    omega

/-- Matrix order preserves strict negativity on a subspace. -/
theorem strictlyNegativeOn_of_le {K H : Matrix ι ι ℝ}
    (hKH : K ≤ H) {U : Submodule ℝ (ι → ℝ)}
    (hH : StrictlyNegativeOn H U) : StrictlyNegativeOn K U := by
  intro x hx hne
  have hq := (Matrix.le_iff.mp hKH).2 x
  simp only [star_trivial, Matrix.sub_mulVec, dotProduct_sub] at hq
  linarith [hH x hx hne]

/-- The finite-dimensional part of the 13k/16 local theorem, assembling the
two actual one-sign comparisons and proving the negative subspace dimension. -/
theorem two_sign_negative_subspace
    [Nonempty ι] (Γ₁ Γ₂ K₁ K₂ K L₁ L₂ : Matrix ι ι ℝ)
    (hΓ₁ : Γ₁.PosSemidef) (hΓ₂ : Γ₂.PosSemidef)
    (g₁ g₂ : ι → ℝ) (hg₁ : ∀ i, 0 < g₁ i) (hg₂ : ∀ i, 0 < g₂ i)
    (hdiag₁ : ∀ i, Γ₁ i i = g₁ i) (hdiag₂ : ∀ i, Γ₂ i i = g₂ i)
    {a₁ b₁ a₂ b₂ : ℝ} (ha₁ : 0 < a₁) (hb₁ : 0 < b₁)
    (ha₂ : 0 < a₂) (hb₂ : 0 < b₂)
    (hr₁ : a₁ / b₁ < 3 / 32) (hr₂ : a₂ / b₂ < 3 / 32)
    (hcomp₁ : L₁ᵀ * K₁ * L₁ ≤ a₁ • Γ₁ - b₁ • Matrix.diagonal g₁)
    (hcomp₂ : L₂ᵀ * K₂ * L₂ ≤ a₂ • Γ₂ - b₂ • Matrix.diagonal g₂)
    (hcommon : K ≤ K₁ + K₂) :
    ∃ U : Submodule ℝ (ι → ℝ),
      (13 / 16 : ℝ) * Fintype.card ι < (finrank ℝ U : ℝ) ∧
      StrictlyNegativeOn K U := by
  obtain ⟨U₁, hdim₁, hneg₁⟩ := exists_large_negative_comparison hΓ₁ g₁ hg₁ hdiag₁ ha₁ hb₁
  obtain ⟨U₂, hdim₂, hneg₂⟩ := exists_large_negative_comparison hΓ₂ g₂ hg₂ hdiag₂ ha₂ hb₂
  have him₁ := negative_pullback_image L₁ K₁ U₁ (strictlyNegativeOn_of_le hcomp₁ hneg₁)
  have him₂ := negative_pullback_image L₂ K₂ U₂ (strictlyNegativeOn_of_le hcomp₂ hneg₂)
  let V₁ := U₁.map L₁.mulVecLin
  let V₂ := U₂.map L₂.mulVecLin
  have hinter := intersect_negative_subspaces hcommon him₁.1 him₂.1
  refine ⟨V₁ ⊓ V₂, ?_, hinter.1⟩
  have hdim : (finrank ℝ U₁ : ℝ) + finrank ℝ U₂ ≤
      (finrank ℝ ↥(V₁ ⊓ V₂) : ℝ) + Fintype.card ι := by
    rw [← him₁.2, ← him₂.2]
    exact_mod_cast hinter.2
  have hk : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hrat₁ := mul_lt_mul_of_pos_right hr₁ hk
  have hrat₂ := mul_lt_mul_of_pos_right hr₂ hk
  nlinarith

end MatrixSpencer.KSEighthInertia
