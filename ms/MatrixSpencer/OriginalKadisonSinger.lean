import MatrixSpencer.KSSpinMain
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# The original finite Weaver KS₂ statement

This standalone audit corollary is outside the frozen library.  It proves
an explicit two-part partition with η = 4096 and θ = 1024, using the proved
rank-one signing endpoint.  It makes no operator-algebraic unique-extension
or sharp MSS quantitative claim.
-/

open scoped BigOperators Matrix Matrix.Norms.L2Operator InnerProductSpace
open Matrix
noncomputable section

namespace KadisonSingerOriginal
open MatrixSpencer

variable {N d : ℕ}

theorem two_parts_of_signing (A : Fin N → CMatrix d)
    (hA : ∑ i, A i = 1) (s : Fin N → ℝ) (hs : IsFullSigning s)
    (hbound : spectralNorm (signedSum A s) ≤ 1 / 2) :
    ∃ S : Finset (Fin N),
      spectralNorm (∑ i ∈ S, A i) ≤ 3 / 4 ∧
      spectralNorm (∑ i ∈ Sᶜ, A i) ≤ 3 / 4 := by
  classical
  let S := Finset.univ.filter (fun i => s i = 1)
  have hplus : (2 : ℝ) • (∑ i ∈ S, A i) = 1 + signedSum A s := by
    rw [← hA, signedSum, ← Finset.sum_add_distrib]
    simp only [S, Finset.sum_filter, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rcases hs i with hi | hi <;> norm_num [hi, two_smul]
  have hminus : (2 : ℝ) • (∑ i ∈ Sᶜ, A i) = 1 - signedSum A s := by
    have htotal := Finset.sum_add_sum_compl S A
    rw [hA] at htotal
    have hc : (∑ i ∈ Sᶜ, A i) = 1 - ∑ i ∈ S, A i := by
      apply eq_sub_iff_add_eq.mpr
      simpa only [add_comm] using htotal
    rw [hc, smul_sub, hplus, two_smul]
    abel
  refine ⟨S, ?_, ?_⟩
  · have hn := norm_add_le (1 : CMatrix d) (signedSum A s)
    rw [← hplus, norm_smul] at hn
    rw [spectralNorm_eq_scopedMatrixNorm] at hbound ⊢
    norm_num at hn
    have h1 : ‖(1 : CMatrix d)‖ ≤ 1 := by
      change ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) (1 : CMatrix d)‖ ≤ 1
      rw [map_one]
      exact ContinuousLinearMap.norm_id_le
    linarith
  · have hn := norm_sub_le (1 : CMatrix d) (signedSum A s)
    rw [← hminus, norm_smul] at hn
    rw [spectralNorm_eq_scopedMatrixNorm] at hbound ⊢
    norm_num at hn
    have h1 : ‖(1 : CMatrix d)‖ ≤ 1 := by
      change ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) (1 : CMatrix d)‖ ≤ 1
      rw [map_one]
      exact ContinuousLinearMap.norm_id_le
    linarith

/-- The matrix form of Weaver KS₂, with explicit universal constants. -/
theorem weaver_matrix (w : Fin N → EuclideanSpace ℂ (Fin d))
    (hw : ∀ i, ‖w i‖ ≤ 1)
    (hframe : (∑ i, KSRankOne.atom (WithLp.ofLp (w i))) =
      (4096 : ℝ) • (1 : CMatrix d)) :
    ∃ S : Finset (Fin N),
      spectralNorm (∑ i ∈ S, KSRankOne.atom (WithLp.ofLp (w i))) ≤ 4096 - 1024 ∧
      spectralNorm (∑ i ∈ Sᶜ, KSRankOne.atom (WithLp.ofLp (w i))) ≤ 4096 - 1024 := by
  let A : Fin N → CMatrix d := fun i => (1 / 4096 : ℝ) • KSRankOne.atom (WithLp.ofLp (w i))
  have hA (i : Fin N) : KSIsRankOneAtom (A i) := by
    refine ⟨fun a => (1 / 64 : ℂ) * w i a, ?_⟩
    intro a b
    change ((1 / 4096 : ℝ) : ℂ) * (w i a * star (w i b)) = _
    simp only [StarMul.star_mul, star_div₀, star_one, star_ofNat]
    norm_num
    ring
  have hsum : ∑ i, A i = 1 := by
    rw [show (∑ i, A i) = (1 / 4096 : ℝ) •
      (∑ i, KSRankOne.atom (WithLp.ofLp (w i))) by simp [A, Finset.smul_sum]]
    rw [hframe, smul_smul]
    norm_num
  have habound (i : Fin N) : spectralNorm (A i) ≤ 1 / 4096 := by
    rw [spectralNorm_eq_scopedMatrixNorm]
    dsimp only [A]
    rw [norm_smul, KSRankOne.atom_norm, KSRankOne.realTrace_atom_eq_norm_sq]
    simp only [WithLp.toLp_ofLp]
    norm_num
    nlinarith [hw i, norm_nonneg (w i)]
  obtain ⟨s, hs, hsign⟩ := kadison_singer_spin_mixed N d (1 / 4096) (by norm_num)
    A hA hsum habound
  have hroot : Real.sqrt (1 / 4096 : ℝ) = 1 / 64 := by norm_num
  have hc : 16 * Real.sqrt 2 + 2 ≤ 32 := by
    have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hpos := Real.sqrt_nonneg (2 : ℝ)
    nlinarith
  rw [hroot] at hsign
  have hhalf : spectralNorm (signedSum A s) ≤ 1 / 2 := by nlinarith
  obtain ⟨S, hS, hSc⟩ := two_parts_of_signing A hsum s hs hhalf
  have hscale (T : Finset (Fin N)) :
      spectralNorm (∑ i ∈ T, KSRankOne.atom (WithLp.ofLp (w i))) =
        4096 * spectralNorm (∑ i ∈ T, A i) := by
    have hm : (∑ i ∈ T, KSRankOne.atom (WithLp.ofLp (w i))) =
        (4096 : ℝ) • (∑ i ∈ T, A i) := by
      simp [A, Finset.smul_sum, smul_smul]
    rw [hm, spectralNorm_eq_scopedMatrixNorm, spectralNorm_eq_scopedMatrixNorm, norm_smul]
    norm_num
  refine ⟨S, ?_, ?_⟩ <;> rw [hscale] <;> nlinarith


theorem atom_apply_euclidean (w u : EuclideanSpace ℂ (Fin d)) :
    Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)
      (KSRankOne.atom (WithLp.ofLp w)) u = inner ℂ w u • w := by
  apply WithLp.ofLp_injective
  rw [Matrix.ofLp_toEuclideanCLM]
  simp [KSRankOne.atom, Matrix.vecMulVec_mulVec,
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]

theorem atom_inner_euclidean (w u : EuclideanSpace ℂ (Fin d)) :
    inner ℂ (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)
      (KSRankOne.atom (WithLp.ofLp w)) u) u = (‖inner ℂ u w‖ ^ 2 : ℝ) := by
  rw [atom_apply_euclidean, inner_smul_left]
  rw [Complex.conj_mul']
  simp only [Complex.ofReal_pow, norm_inner_symm]

theorem sum_atom_inner (w : Fin N → EuclideanSpace ℂ (Fin d))
    (T : Finset (Fin N)) (u : EuclideanSpace ℂ (Fin d)) :
    inner ℂ (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)
      (∑ i ∈ T, KSRankOne.atom (WithLp.ofLp (w i))) u) u =
        ((∑ i ∈ T, ‖inner ℂ u (w i)‖ ^ 2 : ℝ) : ℂ) := by
  simp only [map_sum, ContinuousLinearMap.sum_apply, sum_inner, atom_inner_euclidean,
    Complex.ofReal_sum]

/-- The unit-vector identity in Weaver's statement supplies the exact matrix frame identity. -/
theorem frame_identity_of_unit_energy (w : Fin N → EuclideanSpace ℂ (Fin d))
    (η : ℝ) (hunit : ∀ u : EuclideanSpace ℂ (Fin d), ‖u‖ = 1 →
      (∑ i, ‖inner ℂ u (w i)‖ ^ 2) = η) :
    (∑ i, KSRankOne.atom (WithLp.ofLp (w i))) = η • (1 : CMatrix d) := by
  let B : CMatrix d := ∑ i, KSRankOne.atom (WithLp.ofLp (w i))
  let L := Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) B
  let R := Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) (η • (1 : CMatrix d))
  apply Matrix.toEuclideanCLM.injective
  change L = R
  apply ContinuousLinearMap.coe_injective
  apply (ext_inner_map L.toLinearMap R.toLinearMap).mp
  intro u
  by_cases hu : u = 0
  · subst u
    simp
  have hn : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  let z : EuclideanSpace ℂ (Fin d) := ((‖u‖⁻¹ : ℝ) : ℂ) • u
  have hz : ‖z‖ = 1 := by
    simp [z, norm_smul, hn]
  have hLz : inner ℂ (L z) z = (η : ℂ) := by
    change inner ℂ (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)
      (∑ i, KSRankOne.atom (WithLp.ofLp (w i))) z) z = _
    rw [show (∑ i, KSRankOne.atom (WithLp.ofLp (w i))) =
      ∑ i ∈ (Finset.univ : Finset (Fin N)), KSRankOne.atom (WithLp.ofLp (w i)) by simp]
    rw [sum_atom_inner]
    simpa using congrArg Complex.ofReal (hunit z hz)
  have hRz : inner ℂ (R z) z = (η : ℂ) := by
    have hm : η • (1 : CMatrix d) = (η : ℂ) • (1 : CMatrix d) := by
      ext i j
      simp [Matrix.smul_apply, Complex.real_smul]
    dsimp only [R]
    rw [hm, map_smul (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)) (η : ℂ), map_one]
    change inner ℂ ((η : ℂ) • z) z = (η : ℂ)
    rw [inner_smul_left]
    simp [inner_self_eq_norm_sq_to_K, hz]
  have heq : u = (‖u‖ : ℂ) • z := by
    simp [z, smul_smul, hn]
  rw [heq]
  simp only [ContinuousLinearMap.coe_coe, map_smul, inner_smul_left,
    inner_smul_right, hLz, hRz]


/-- A matrix operator-norm bound gives the exact unit-vector energy bound. -/
theorem unit_energy_le_of_norm (w : Fin N → EuclideanSpace ℂ (Fin d))
    (T : Finset (Fin N)) {a : ℝ}
    (hbound : spectralNorm (∑ i ∈ T, KSRankOne.atom (WithLp.ofLp (w i))) ≤ a)
    (u : EuclideanSpace ℂ (Fin d)) (hu : ‖u‖ = 1) :
    (∑ i ∈ T, ‖inner ℂ u (w i)‖ ^ 2) ≤ a := by
  let L := Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)
    (∑ i ∈ T, KSRankOne.atom (WithLp.ofLp (w i)))
  have hnonneg : 0 ≤ ∑ i ∈ T, ‖inner ℂ u (w i)‖ ^ 2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hinner : (∑ i ∈ T, ‖inner ℂ u (w i)‖ ^ 2) ≤ ‖L u‖ := by
    have hh := norm_inner_le_norm (𝕜 := ℂ) (L u) u
    dsimp only [L] at hh
    rw [sum_atom_inner, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hnonneg, hu, mul_one] at hh
    exact hh
  have hop : ‖L u‖ ≤ ‖L‖ := by simpa [hu] using L.le_opNorm u
  exact hinner.trans (hop.trans hbound)

/-- Weaver's unit-vector formulation, with the concrete universal pair (4096,1024). -/
theorem weaver_unit_energy (w : Fin N → EuclideanSpace ℂ (Fin d))
    (hw : ∀ i, ‖w i‖ ≤ 1)
    (hframe : ∀ u : EuclideanSpace ℂ (Fin d), ‖u‖ = 1 →
      (∑ i, ‖inner ℂ u (w i)‖ ^ 2) = 4096) :
    ∃ S : Finset (Fin N), ∀ u : EuclideanSpace ℂ (Fin d), ‖u‖ = 1 →
      (∑ i ∈ S, ‖inner ℂ u (w i)‖ ^ 2) ≤ 4096 - 1024 ∧
      (∑ i ∈ Sᶜ, ‖inner ℂ u (w i)‖ ^ 2) ≤ 4096 - 1024 := by
  obtain ⟨S, hS, hSc⟩ := weaver_matrix w hw (frame_identity_of_unit_energy w 4096 hframe)
  exact ⟨S, fun u hu => ⟨unit_energy_le_of_norm w S hS u hu,
    unit_energy_le_of_norm w Sᶜ hSc u hu⟩⟩


theorem weaver_KS2 :
    ∃ η θ : ℝ, 2 ≤ η ∧ 0 < θ ∧
      ∀ (N d : ℕ) (w : Fin N → EuclideanSpace ℂ (Fin d)),
        (∀ i, ‖w i‖ ≤ 1) →
        (∀ u : EuclideanSpace ℂ (Fin d), ‖u‖ = 1 →
          (∑ i, ‖inner ℂ u (w i)‖ ^ 2) = η) →
        ∃ S : Finset (Fin N), ∀ u : EuclideanSpace ℂ (Fin d), ‖u‖ = 1 →
          (∑ i ∈ S, ‖inner ℂ u (w i)‖ ^ 2) ≤ η - θ ∧
          (∑ i ∈ Sᶜ, ‖inner ℂ u (w i)‖ ^ 2) ≤ η - θ := by
  refine ⟨4096, 1024, by norm_num, by norm_num, ?_⟩
  intro N d w hw hframe
  exact weaver_unit_energy w hw hframe

#print axioms weaver_KS2

end KadisonSingerOriginal
