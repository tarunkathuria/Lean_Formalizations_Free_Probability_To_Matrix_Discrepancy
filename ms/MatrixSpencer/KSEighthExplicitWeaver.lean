import MatrixSpencer.KSEighthExplicitAlgorithm
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# A finite randomized construction for the original Weaver KS₂ statement

This module converts the actual finite walk from `KSEighthExplicitAlgorithm` into a
fixed partition and its complement, using the original eighth-cube walk. It proves the literal unit-vector-energy
statement with universal constants `eta = 16777216` and `theta = 4194304`, and also
exports the actual finite output, its soundness, normalized nonnegative draw
weights, and success probability at least `1 - (1 / 4)^r` after `r` attempts.
The dimension-zero branch is the deterministic empty partition.

The elementary frame and partition conversion lemmas are reproduced here. The
existence proof uses the finite output probability, not the previous existential
Kadison–Singer endpoint. No running-time or bit-complexity claim is made here.
-/

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator InnerProductSpace
noncomputable section
namespace MatrixSpencer.KSEighthExplicitWeaver
variable {N d : ℕ}

def eta : ℝ := 16777216
def theta : ℝ := 4194304
def epsilon : ℝ := 1/16777216
theorem epsilon_pos : 0 < epsilon := by norm_num [epsilon]

def scaled (w : Fin N → EuclideanSpace ℂ (Fin d)) : Fin N → Fin d → ℂ :=
  fun i j => (1/4096 : ℂ) * w i j

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
  have he : (WithLp.toLp 2 (scaled w i) : EuclideanSpace ℂ (Fin d)) = (1/4096 : ℂ) • w i := by
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

abbrev PositiveDraws (w : Fin N → EuclideanSpace ℂ (Fin d)) (hd : 0 < d) (r : ℕ) :=
  KSEighthExplicitAlgorithm.Draws (scaled w) epsilon_pos hd r

def positiveOutput (w : Fin N → EuclideanSpace ℂ (Fin d)) (hd : 0 < d) (r : ℕ)
    (z : PositiveDraws w hd r) : Option (Finset (Fin N)) :=
  (KSEighthExplicitAlgorithm.output (scaled w) epsilon_pos hd r z).map positiveSet

def positiveWeight (w : Fin N → EuclideanSpace ℂ (Fin d)) (hd : 0 < d) (r : ℕ)
    (z : PositiveDraws w hd r) : ℝ :=
  KSEighthExplicitAlgorithm.drawWeight (scaled w) epsilon_pos hd r z

/-- Every partition is the fixed positive-sign filter of the returned full signing. -/
theorem positive_output_sound (w : Fin N → EuclideanSpace ℂ (Fin d)) (hd : 0 < d)
    (hframe : ∀ u : EuclideanSpace ℂ (Fin d), ‖u‖ = 1 →
      (∑ i, ‖inner ℂ u (w i)‖^2) = eta)
    (r : ℕ) (z : PositiveDraws w hd r) (S : Finset (Fin N))
    (hout : positiveOutput w hd r z = some S) :
    ∀ u : EuclideanSpace ℂ (Fin d), ‖u‖ = 1 →
      (∑ i ∈ S, ‖inner ℂ u (w i)‖^2) ≤ eta-theta ∧
      (∑ i ∈ Sᶜ, ‖inner ℂ u (w i)‖^2) ≤ eta-theta := by
  obtain ⟨σ, hσ, hS⟩ := Option.map_eq_some_iff.mp hout
  subst S
  have hs := KSEighthExplicitAlgorithm.output_sound (scaled w) epsilon_pos hd r z σ hσ
  have hbound : spectralNorm (signedSum (fun i => KSRankOne.atom (scaled w i)) σ) ≤ 1/2 := by
    rw [spectralNorm_eq_scopedMatrixNorm]
    change ‖∑ i, σ i • KSRankOne.atom (scaled w i)‖ ≤ 1/2
    have hroot : Real.sqrt epsilon = 1/4096 := by norm_num [epsilon]
    rw [hroot] at hs
    linarith [hs.2]
  obtain ⟨hp, hm⟩ := fixed_partition_bounds (fun i => KSRankOne.atom (scaled w i))
    (scaled_parseval w hframe) σ hs.1 hbound
  have hscale (T : Finset (Fin N)) :
      spectralNorm (∑ i ∈ T, KSRankOne.atom (WithLp.ofLp (w i))) =
        eta * spectralNorm (∑ i ∈ T, KSRankOne.atom (scaled w i)) := by
    have he : (∑ i ∈ T, KSRankOne.atom (WithLp.ofLp (w i))) =
        eta • (∑ i ∈ T, KSRankOne.atom (scaled w i)) := by
      simp [atom_scaled, Finset.smul_sum, smul_smul, eta]
    rw [he, spectralNorm_eq_scopedMatrixNorm, spectralNorm_eq_scopedMatrixNorm, norm_smul]
    norm_num [eta]
  have hp' : spectralNorm (∑ i ∈ positiveSet σ, KSRankOne.atom (WithLp.ofLp (w i))) ≤ eta-theta := by
    rw [hscale]
    norm_num [eta, theta] at *
    nlinarith
  have hm' : spectralNorm (∑ i ∈ (positiveSet σ)ᶜ, KSRankOne.atom (WithLp.ofLp (w i))) ≤ eta-theta := by
    rw [hscale]
    norm_num [eta, theta] at *
    nlinarith
  exact fun u hu => ⟨unit_energy_le_of_norm w (positiveSet σ) hp' u hu,
    unit_energy_le_of_norm w (positiveSet σ)ᶜ hm' u hu⟩

/-- The same finite draw distribution succeeds with geometric retry probability. -/
theorem positive_output_probability_ge (w : Fin N → EuclideanSpace ℂ (Fin d)) (hd : 0 < d)
    (hw : ∀ i, ‖w i‖ ≤ 1)
    (hframe : ∀ u : EuclideanSpace ℂ (Fin d), ‖u‖ = 1 →
      (∑ i, ‖inner ℂ u (w i)‖^2) = eta) (r : ℕ) :
    1-((1:ℝ)/4)^r ≤ ∑ z : PositiveDraws w hd r,
      positiveWeight w hd r z * (if (positiveOutput w hd r z).isSome then 1 else 0) := by
  simpa only [positiveOutput, Option.isSome_map] using
    KSEighthExplicitAlgorithm.output_event_probability_ge (scaled w) epsilon_pos hd
      (scaled_parseval w hframe) (scaled_size w hw) r

/-- The total finite sampler: the zero-dimensional case has one deterministic draw. -/
def Draws : {d : ℕ} → (Fin N → EuclideanSpace ℂ (Fin d)) → ℕ → Type
  | 0, _, _ => PUnit
  | d+1, w, r => PositiveDraws w (Nat.succ_pos d) r

instance drawsFintype : {d : ℕ} → (w : Fin N → EuclideanSpace ℂ (Fin d)) →
    (r : ℕ) → Fintype (Draws w r)
  | 0, _, _ => inferInstanceAs (Fintype PUnit)
  | d+1, w, r => inferInstanceAs (Fintype (PositiveDraws w (Nat.succ_pos d) r))

/-- Actual partition output, including the deterministic empty partition in dimension zero. -/
def output : {d : ℕ} → (w : Fin N → EuclideanSpace ℂ (Fin d)) →
    (r : ℕ) → Draws w r → Option (Finset (Fin N))
  | 0, _, _, _ => some ∅
  | d+1, w, r, z => positiveOutput w (Nat.succ_pos d) r z

def drawWeight : {d : ℕ} → (w : Fin N → EuclideanSpace ℂ (Fin d)) →
    (r : ℕ) → Draws w r → ℝ
  | 0, _, _, _ => 1
  | d+1, w, r, z => positiveWeight w (Nat.succ_pos d) r z

theorem drawWeight_nonneg (w : Fin N → EuclideanSpace ℂ (Fin d)) (r : ℕ)
    (z : Draws w r) : 0 ≤ drawWeight w r z := by
  cases d with
  | zero => exact zero_le_one
  | succ d => exact KSEighthExplicitAlgorithm.drawWeight_nonneg (scaled w) epsilon_pos (Nat.succ_pos d) r z

theorem drawWeight_sum (w : Fin N → EuclideanSpace ℂ (Fin d)) (r : ℕ) :
    (∑ z : Draws w r, drawWeight w r z) = 1 := by
  cases d with
  | zero => simp [drawWeight, Draws]
  | succ d => exact KSEighthExplicitAlgorithm.drawWeight_sum (scaled w) epsilon_pos (Nat.succ_pos d) r

/-- Both returned classes satisfy the original unit-energy conclusion. -/
theorem output_sound (w : Fin N → EuclideanSpace ℂ (Fin d))
    (hframe : ∀ u : EuclideanSpace ℂ (Fin d), ‖u‖ = 1 →
      (∑ i, ‖inner ℂ u (w i)‖^2) = eta)
    (r : ℕ) (z : Draws w r) (S : Finset (Fin N)) (hout : output w r z = some S) :
    ∀ u : EuclideanSpace ℂ (Fin d), ‖u‖ = 1 →
      (∑ i ∈ S, ‖inner ℂ u (w i)‖^2) ≤ eta-theta ∧
      (∑ i ∈ Sᶜ, ‖inner ℂ u (w i)‖^2) ≤ eta-theta := by
  cases d with
  | zero =>
    intro u hu
    have hu0 : u = 0 := Subsingleton.elim _ _
    simp [hu0] at hu
  | succ d => exact positive_output_sound w (Nat.succ_pos d) hframe r z S hout

/-- Literal finite-output success probability, uniformly over all dimensions and label counts. -/
theorem output_event_probability_ge (w : Fin N → EuclideanSpace ℂ (Fin d))
    (hw : ∀ i, ‖w i‖ ≤ 1)
    (hframe : ∀ u : EuclideanSpace ℂ (Fin d), ‖u‖ = 1 →
      (∑ i, ‖inner ℂ u (w i)‖^2) = eta) (r : ℕ) :
    1-((1:ℝ)/4)^r ≤ ∑ z : Draws w r,
      drawWeight w r z * (if (output w r z).isSome then 1 else 0) := by
  cases d with
  | zero =>
    simp only [Draws, output, drawWeight, Option.isSome_some, ↓reduceIte, mul_one]
    simp only [Finset.univ_unique, Finset.sum_singleton]
    have hp : 0 ≤ ((1:ℝ)/4)^r := by positivity
    linarith
  | succ d => exact positive_output_probability_ge w (Nat.succ_pos d) hw hframe r

/-- A successful partition is produced by an actual finite draw. -/
theorem exists_output (w : Fin N → EuclideanSpace ℂ (Fin d))
    (hw : ∀ i, ‖w i‖ ≤ 1)
    (hframe : ∀ u : EuclideanSpace ℂ (Fin d), ‖u‖ = 1 →
      (∑ i, ‖inner ℂ u (w i)‖^2) = eta) :
    ∃ (z : Draws w 1) (S : Finset (Fin N)), output w 1 z = some S := by
  classical
  have hp := output_event_probability_ge w hw hframe 1
  by_contra! hn
  have ho : ∀ z : Draws w 1, output w 1 z = none := by
    intro z
    cases he : output w 1 z with
    | none => rfl
    | some S => exact False.elim (hn z S he)
  simp [ho] at hp
  norm_num at hp

/-- The original finite Weaver conclusion is obtained from a successful run. -/
theorem weaver_unit_energy (w : Fin N → EuclideanSpace ℂ (Fin d))
    (hw : ∀ i, ‖w i‖ ≤ 1)
    (hframe : ∀ u : EuclideanSpace ℂ (Fin d), ‖u‖ = 1 →
      (∑ i, ‖inner ℂ u (w i)‖^2) = eta) :
    ∃ S : Finset (Fin N), ∀ u : EuclideanSpace ℂ (Fin d), ‖u‖ = 1 →
      (∑ i ∈ S, ‖inner ℂ u (w i)‖^2) ≤ eta-theta ∧
      (∑ i ∈ Sᶜ, ‖inner ℂ u (w i)‖^2) ≤ eta-theta := by
  obtain ⟨z, S, ho⟩ := exists_output w hw hframe
  exact ⟨S, output_sound w hframe 1 z S ho⟩

/-- The literal finite Weaver KS₂ statement, proved through the finite randomized walk.
The fixed universal constants are eta=16777216 and theta=4194304. -/
theorem weaver_KS2 :
    ∃ η θ : ℝ, 2 ≤ η ∧ 0 < θ ∧
      ∀ (N d : ℕ) (w : Fin N → EuclideanSpace ℂ (Fin d)),
        (∀ i, ‖w i‖ ≤ 1) →
        (∀ u : EuclideanSpace ℂ (Fin d), ‖u‖ = 1 →
          (∑ i, ‖inner ℂ u (w i)‖^2) = η) →
        ∃ S : Finset (Fin N), ∀ u : EuclideanSpace ℂ (Fin d), ‖u‖ = 1 →
          (∑ i ∈ S, ‖inner ℂ u (w i)‖^2) ≤ η-θ ∧
          (∑ i ∈ Sᶜ, ‖inner ℂ u (w i)‖^2) ≤ η-θ := by
  refine ⟨eta, theta, by norm_num [eta], by norm_num [theta], ?_⟩
  intro N d w hw hframe
  exact weaver_unit_energy w hw hframe

end MatrixSpencer.KSEighthExplicitWeaver
