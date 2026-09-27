import MatrixSpencer.KSRankOne
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-! Reproduced elementary conversion from original unit-energy data to
Parseval vectors, and from a full signing to the fixed positive partition.
This module contains no existence or walk endpoint. -/
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator InnerProductSpace
noncomputable section
namespace MatrixSpencer.KSManuscriptWeaverTools
variable {N d : ℕ}

def eta : ℝ := 1048576
def theta : ℝ := 262144
def epsilon : ℝ := 1/1048576
theorem epsilon_pos : 0 < epsilon := by norm_num [epsilon]

def scaled (w : Fin N → EuclideanSpace ℂ (Fin d)) : Fin N → Fin d → ℂ :=
  fun i j => (1/1024 : ℂ) * w i j

def positiveSet (σ : Fin N → ℝ) : Finset (Fin N) :=
  Finset.univ.filter (fun i => σ i = 1)

theorem fixed_partition_bounds (A : Fin N → CMatrix d)
    (hA : ∑ i, A i = 1) (s : Fin N → ℝ) (hs : IsFullSigning s)
    (hbound : spectralNorm (signedSum A s) ≤ 1 / 2) :
    spectralNorm (∑ i ∈ positiveSet s, A i) ≤ 3 / 4 ∧
      spectralNorm (∑ i ∈ (positiveSet s)ᶜ, A i) ≤ 3 / 4 := by
  classical
  let S := positiveSet s
  have hplus : (2 : ℝ) • (∑ i ∈ S, A i) = 1 + signedSum A s := by
    rw [← hA, signedSum, ← Finset.sum_add_distrib]
    simp only [S, positiveSet, Finset.sum_filter, Finset.smul_sum]
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
  constructor
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

theorem atom_scaled (w : Fin N → EuclideanSpace ℂ (Fin d)) (i : Fin N) :
    KSRankOne.atom (scaled w i) = (1/eta : ℝ) • KSRankOne.atom (WithLp.ofLp (w i)) := by
  ext j k
  simp only [KSRankOne.atom, Matrix.vecMulVec_apply, Pi.star_apply, scaled,
    Matrix.smul_apply, Complex.real_smul, StarMul.star_mul, star_div₀, star_one, star_ofNat]
  norm_num [eta]
  ring

theorem scaled_size (w : Fin N → EuclideanSpace ℂ (Fin d)) (hw : ∀ i, ‖w i‖ ≤ 1) :
    ∀ i, ‖(WithLp.toLp 2 (scaled w i) : EuclideanSpace ℂ (Fin d))‖^2 ≤ epsilon := by
  intro i
  have he : (WithLp.toLp 2 (scaled w i) : EuclideanSpace ℂ (Fin d)) = (1/1024 : ℂ) • w i := by
    ext j
    rfl
  rw [he, norm_smul]
  norm_num [epsilon]
  nlinarith [hw i, norm_nonneg (w i)]

theorem scaled_parseval (w : Fin N → EuclideanSpace ℂ (Fin d))
    (hframe : ∀ u : EuclideanSpace ℂ (Fin d), ‖u‖ = 1 →
      (∑ i, ‖inner ℂ u (w i)‖^2) = eta) :
    (∑ i, KSRankOne.atom (scaled w i)) = 1 := by
  simp_rw [atom_scaled]
  rw [← Finset.smul_sum, frame_identity_of_unit_energy w eta hframe, smul_smul]
  norm_num [eta]

theorem scaled_atom_size (w : Fin N → EuclideanSpace ℂ (Fin d))
    (hw : ∀i, ‖w i‖ ≤ 1) : ∀i, ‖KSRankOne.atom (scaled w i)‖ ≤ epsilon := by
  intro i
  rw [KSRankOne.atom_norm,KSRankOne.realTrace_atom_eq_norm_sq]
  exact scaled_size w hw i

/-- Both energy inequalities for the same fixed partition and its complement. -/
theorem partition_energy (w : Fin N → EuclideanSpace ℂ (Fin d))
    (hframe : ∀u : EuclideanSpace ℂ (Fin d), ‖u‖ = 1 →
      (∑i, ‖inner ℂ u (w i)‖^2) = eta)
    (σ : Fin N → ℝ) (hs : ∀i, IsSign (σ i))
    (hbound : ‖∑i, σ i • KSRankOne.atom (scaled w i)‖ ≤ 1/2) :
    ∀u : EuclideanSpace ℂ (Fin d), ‖u‖ = 1 →
      (∑i ∈ positiveSet σ, ‖inner ℂ u (w i)‖^2) ≤ eta-theta ∧
      (∑i ∈ (positiveSet σ)ᶜ, ‖inner ℂ u (w i)‖^2) ≤ eta-theta := by
  obtain ⟨hp,hm⟩ := fixed_partition_bounds (fun i => KSRankOne.atom (scaled w i))
    (scaled_parseval w hframe) σ hs hbound
  have hscale (T : Finset (Fin N)) :
      spectralNorm (∑i ∈ T, KSRankOne.atom (WithLp.ofLp (w i))) =
        eta * spectralNorm (∑i ∈ T, KSRankOne.atom (scaled w i)) := by
    have he : (∑i ∈ T, KSRankOne.atom (WithLp.ofLp (w i))) =
        eta • (∑i ∈ T, KSRankOne.atom (scaled w i)) := by
      simp [atom_scaled, Finset.smul_sum, smul_smul, eta]
    rw [he, spectralNorm_eq_scopedMatrixNorm, spectralNorm_eq_scopedMatrixNorm, norm_smul]
    norm_num [eta]
  have hp' : spectralNorm (∑i ∈ positiveSet σ, KSRankOne.atom (WithLp.ofLp (w i))) ≤ eta-theta := by
    rw [hscale]
    norm_num [eta,theta] at *
    nlinarith
  have hm' : spectralNorm (∑i ∈ (positiveSet σ)ᶜ, KSRankOne.atom (WithLp.ofLp (w i))) ≤ eta-theta := by
    rw [hscale]
    norm_num [eta,theta] at *
    nlinarith
  exact fun u hu => ⟨unit_energy_le_of_norm w (positiveSet σ) hp' u hu,
    unit_energy_le_of_norm w (positiveSet σ)ᶜ hm' u hu⟩

end MatrixSpencer.KSManuscriptWeaverTools
