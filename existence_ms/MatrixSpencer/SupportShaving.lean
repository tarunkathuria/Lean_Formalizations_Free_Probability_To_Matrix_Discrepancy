import MatrixSpencer.OwnerShort

/-!
# Rank-one shaving inside a positive matrix's support

All coefficient vectors and matrices are real. Support means the actual range
of the Euclidean linear operator, not an assumed invertible support block.
-/

open scoped BigOperators MatrixOrder
open Matrix

namespace MatrixSpencer

variable {ι : Type*} [Fintype ι]

/-- The real rank-one covariance `u uᵀ`. -/
def realRankOne (u : ι → ℝ) : Matrix ι ι ℝ := Matrix.vecMulVec u u

theorem realRankOne_posSemidef (u : ι → ℝ) : (realRankOne u).PosSemidef := by
  simpa only [realRankOne, star_trivial] using Matrix.posSemidef_vecMulVec_self_star u

theorem realRankOne_mulVec (u x : ι → ℝ) :
    realRankOne u *ᵥ x = (u ⬝ᵥ x) • u := by
  ext i
  simp only [realRankOne, Matrix.mulVec, Matrix.vecMulVec_apply, dotProduct,
    Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem realRankOne_pairing (u x : ι → ℝ) :
    x ⬝ᵥ (realRankOne u *ᵥ x) = (u ⬝ᵥ x) ^ 2 := by
  rw [realRankOne_mulVec, dotProduct_smul, smul_eq_mul, dotProduct_comm x u, pow_two]

variable [DecidableEq ι]

theorem realRankOne_le_energy (u : ι → ℝ) :
    realRankOne u ≤ (u ⬝ᵥ u) • (1 : Matrix ι ι ℝ) := by
  apply Matrix.le_iff.mpr
  have hu : 0 ≤ u ⬝ᵥ u := Finset.sum_nonneg (fun i _ => mul_self_nonneg (u i))
  refine ⟨((Matrix.PosSemidef.one).smul hu).isHermitian.sub
    (realRankOne_posSemidef u).isHermitian, fun x => ?_⟩
  simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_sub, dotProduct_smul, smul_eq_mul, realRankOne_pairing, sub_nonneg]
  simpa only [dotProduct, pow_two] using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u x

omit [DecidableEq ι] in
theorem realRankOne_congruence {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (w : ι → ℝ) :
    A * realRankOne w * A = realRankOne (A *ᵥ w) := by
  have ht : Aᵀ = A := by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hA.eq
  simp only [realRankOne, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
  rw [← ht, Matrix.vecMul_transpose]
  rw [ht]

/-- Any vector in the image of a square root has a rank-one covariance dominated
by a finite scalar multiple of the owner. -/
theorem realRankOne_sqrt_image_le {C : Matrix ι ι ℝ} (hC : C.PosSemidef)
    (w : ι → ℝ) :
    realRankOne (CFC.sqrt C *ᵥ w) ≤ (w ⬝ᵥ w) • C := by
  have hs := (CFC.sqrt_nonneg C).posSemidef.isHermitian
  have h := (Matrix.le_iff.mp (realRankOne_le_energy w)).mul_mul_conjTranspose_same
    (CFC.sqrt C)
  rw [hs.eq, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, CFC.sqrt_mul_sqrt_self C hC.nonneg,
    realRankOne_congruence hs] at h
  exact Matrix.le_iff.mpr h

omit [DecidableEq ι] in
/-- Rescaling a finite positive domination gives a strictly positive feasible shave. -/
theorem exists_pos_smul_le_of_le_smul {C R : Matrix ι ι ℝ}
    (hC : C.PosSemidef) {a : ℝ} (ha : 0 ≤ a) (hRC : R ≤ a • C) :
    ∃ δ : ℝ, 0 < δ ∧ δ • R ≤ C := by
  let δ : ℝ := 1 / (a + 1)
  have hd : 0 < δ := one_div_pos.mpr (by linarith)
  have hda : δ * a ≤ 1 := by
    dsimp [δ]
    rw [one_div_mul_eq_div]
    exact (div_le_one (by linarith)).mpr (by linarith)
  refine ⟨δ, hd, Matrix.le_iff.mpr ?_⟩
  have h := ((Matrix.le_iff.mp hRC).smul hd.le).add
    (hC.smul (sub_nonneg.mpr hda))
  have heq : δ • (a • C - R) + (1 - δ * a) • C = C - δ • R := by module
  rwa [heq] at h

theorem exists_pos_smul_rankOne_le_of_image {C : Matrix ι ι ℝ}
    (hC : C.PosSemidef) (v : ι → ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ δ • realRankOne (C *ᵥ v) ≤ C := by
  let w := CFC.sqrt C *ᵥ v
  have h := realRankOne_sqrt_image_le hC w
  have hi : CFC.sqrt C *ᵥ w = C *ᵥ v := by
    rw [show w = CFC.sqrt C *ᵥ v from rfl, Matrix.mulVec_mulVec,
      CFC.sqrt_mul_sqrt_self C hC.nonneg]
  rw [hi] at h
  exact exists_pos_smul_le_of_le_smul hC
    (Finset.sum_nonneg (fun i _ => mul_self_nonneg (w i))) h

/-- Membership in the genuine Euclidean operator range supplies the needed
domination, even when the covariance has a nontrivial kernel. -/
theorem exists_pos_smul_rankOne_le_of_mem_range {C : Matrix ι ι ℝ}
    (hC : C.PosSemidef) {u : EuclideanSpace ℝ ι}
    (hu : u ∈ LinearMap.range
      (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) C).toLinearMap) :
    ∃ δ : ℝ, 0 < δ ∧ δ • realRankOne (WithLp.ofLp u) ≤ C := by
  obtain ⟨v, hv⟩ := hu
  have hv' : C *ᵥ WithLp.ofLp v = WithLp.ofLp u :=
    congrArg WithLp.ofLp hv
  simpa only [hv'] using exists_pos_smul_rankOne_le_of_image hC (WithLp.ofLp v)

omit [DecidableEq ι] in
/-- Positive matrix order reverses kernels. -/
theorem posSemidef_mulVec_eq_zero_of_le {A B : Matrix ι ι ℝ}
    (hA : A.PosSemidef) (hAB : A ≤ B) {x : ι → ℝ} (hx : B *ᵥ x = 0) :
    A *ᵥ x = 0 := by
  have hq := (Matrix.le_iff.mp hAB).2 x
  simp only [star_trivial, Matrix.sub_mulVec, hx, zero_sub, dotProduct_neg, neg_nonneg] at hq
  have hp : 0 ≤ x ⬝ᵥ (A *ᵥ x) := by simpa only [star_trivial] using hA.2 x
  apply (hA.dotProduct_mulVec_zero_iff x).mp
  simpa only [star_trivial] using le_antisymm hq hp

/-- Positive order preserves range containment in finite Euclidean dimension. -/
theorem posSemidef_range_le_of_le {A B : Matrix ι ι ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hAB : A ≤ B) :
    LinearMap.range (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) A).toLinearMap ≤
      LinearMap.range (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) B).toLinearMap := by
  have hsA := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (IsSelfAdjoint.map (show IsSelfAdjoint A from hA.isHermitian)
      (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)))
  have hsB := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (IsSelfAdjoint.map (show IsSelfAdjoint B from hB.isHermitian)
      (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)))
  apply (ContinuousLinearMap.ker_le_ker_iff_range_le_range hsA hsB).mp
  intro x hx
  have hx' : B *ᵥ WithLp.ofLp x = 0 := congrArg WithLp.ofLp hx
  have hAx := posSemidef_mulVec_eq_zero_of_le hA hAB hx'
  apply (WithLp.equiv 2 (ι → ℝ)).injective
  exact hAx

theorem euclideanMatrix_range_smul (C : Matrix ι ι ℝ) {a : ℝ} (ha : a ≠ 0) :
    LinearMap.range (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) (a • C)).toLinearMap =
      LinearMap.range (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) C).toLinearMap := by
  rw [map_smul]
  exact LinearMap.range_smul _ a ha

/-- A positive scalar sandwich preserves the exact range, including singular cases. -/
theorem posSemidef_range_eq_of_sandwich {B C : Matrix ι ι ℝ}
    (hB : B.PosSemidef) (hC : C.PosSemidef) {a : ℝ} (ha : 0 < a)
    (hlower : a • C ≤ B) (hupper : B ≤ C) :
    LinearMap.range (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) B).toLinearMap =
      LinearMap.range (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) C).toLinearMap := by
  apply le_antisymm (posSemidef_range_le_of_le hB hC hupper)
  have h := posSemidef_range_le_of_le (hC.smul ha.le) hB hlower
  rwa [euclideanMatrix_range_smul C ha.ne'] at h

omit [DecidableEq ι] in
/-- Half of a feasible positive shave leaves at least half of the original owner. -/
theorem shaving_half_lower {C R : Matrix ι ι ℝ} (hR : R.PosSemidef)
    {δ h : ℝ} (hδ : δ • R ≤ C) (hh : h ≤ δ / 2) :
    (1 / 2 : ℝ) • C ≤ C - h • R := by
  apply Matrix.le_iff.mpr
  have hp := ((Matrix.le_iff.mp hδ).smul (show (0 : ℝ) ≤ 1 / 2 by norm_num)).add
    (hR.smul (sub_nonneg.mpr hh))
  have heq : (1 / 2 : ℝ) • (C - δ • R) + (δ / 2 - h) • R =
      (C - h • R) - (1 / 2 : ℝ) • C := by module
  rwa [heq] at hp

/-- Any sufficiently small nonnegative shave is positive and preserves support. -/
theorem shaving_posSemidef_and_range {C R : Matrix ι ι ℝ}
    (hC : C.PosSemidef) (hR : R.PosSemidef) {δ h : ℝ}
    (hδ : δ • R ≤ C) (hh0 : 0 ≤ h) (hh : h ≤ δ / 2) :
    (C - h • R).PosSemidef ∧
      LinearMap.range (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) (C - h • R)).toLinearMap =
        LinearMap.range (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) C).toLinearMap := by
  have hlower := shaving_half_lower hR hδ hh
  have hp : (C - h • R).PosSemidef :=
    ((hC.smul (show (0 : ℝ) ≤ 1 / 2 by norm_num)).nonneg.trans hlower).posSemidef
  refine ⟨hp, posSemidef_range_eq_of_sandwich hp hC (by norm_num) hlower ?_⟩
  exact sub_le_self C (hR.smul hh0).nonneg

/-- Rank-one shaving is feasible on the actual support of every positive owner. -/
theorem exists_rankOne_shaving {C : Matrix ι ι ℝ} (hC : C.PosSemidef)
    {u : EuclideanSpace ℝ ι}
    (hu : u ∈ LinearMap.range
      (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) C).toLinearMap) :
    ∃ δ : ℝ, 0 < δ ∧ δ • realRankOne (WithLp.ofLp u) ≤ C ∧
      ∀ h : ℝ, 0 ≤ h → h < δ / 2 →
        (C - h • realRankOne (WithLp.ofLp u)).PosSemidef ∧
          LinearMap.range (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)
            (C - h • realRankOne (WithLp.ofLp u))).toLinearMap =
              LinearMap.range (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) C).toLinearMap := by
  obtain ⟨δ, hd, hδ⟩ := exists_pos_smul_rankOne_le_of_mem_range hC hu
  exact ⟨δ, hd, hδ, fun h hh0 hh =>
    shaving_posSemidef_and_range hC (realRankOne_posSemidef _) hδ hh0 hh.le⟩

end MatrixSpencer
