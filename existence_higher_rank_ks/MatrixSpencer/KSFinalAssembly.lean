import MatrixSpencer.KSStateRetirement
import MatrixSpencer.KSInitialBounds

/-!
# Endpoint assembly for the two Kadison--Singer targets

These are exact final-state implications. The analytic assertion that a
maximally frozen minimum is a vertex is kept separate until proved for the
actual potentials.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix Set

noncomputable section
set_option maxHeartbeats 800000

namespace MatrixSpencer.KSFinalAssembly

open KSPotentialModels

variable {N : ℕ} {n : Type*} [Fintype n] [DecidableEq n]

theorem eighth_zero_atom_retirement [Nonempty n] (A : Fin N → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (θ : ℝ) {x : Fin N → ℝ}
    (hx : x ∈ ksCube (1 / 8)) (i : Fin N) (hi : A i = 0) :
    eighthPotential A θ (Function.update x i (1 / 8)) ≤ eighthPotential A θ x := by
  have hy := ksCube_update_endpoint (by norm_num : (0 : ℝ) ≤ 1 / 8) hx i (Or.inr rfl)
  have hc := fun j => maskedOwners_nonneg (by norm_num : (0 : ℝ) ≤ 64)
    (by norm_num : (1 / 8 : ℝ) ≤ 1) hx (live (1 / 8) x) j
  have hc' := fun j => maskedOwners_nonneg (by norm_num : (0 : ℝ) ≤ 64)
    (by norm_num : (1 / 8 : ℝ) ≤ 1) hy (live (1 / 8) (Function.update x i (1 / 8))) j
  have hle : ∀ j, truncatedOwners (1 / 8) 64 (Function.update x i (1 / 8)) j ≤
      truncatedOwners (1 / 8) 64 x j := by
    rw [truncatedOwners_update_endpoint 64 (by norm_num) x i (Or.inr rfl)]
    intro j
    by_cases hji : j = i
    · subst j
      simpa only [Function.update_self] using hc i
    · simp only [Function.update_of_ne hji, le_refl]
  have hm := commonPotential_mono A hA θ x hc' hc hle
  unfold eighthPotential commonPotential at *
  simpa only [center_update, hi, smul_zero, add_zero] using hm

theorem spin_zero_atom_retirement [Nonempty n] (A : Fin N → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (θ : ℝ) {x : Fin N → ℝ}
    (hx : x ∈ ksCube 1) (i : Fin N) (hi : A i = 0) :
    spinPotential A θ (Function.update x i 1) ≤ spinPotential A θ x := by
  have hy := ksCube_update_endpoint (by norm_num : (0 : ℝ) ≤ 1) hx i (Or.inr rfl)
  have hc : ∀ j, 0 ≤ naturalOwners 64 x j := naturalOwners_nonneg (by norm_num) le_rfl hx
  have hc' : ∀ j, 0 ≤ naturalOwners 64 (Function.update x i 1) j :=
    naturalOwners_nonneg (by norm_num) le_rfl hy
  have hle : ∀ j, naturalOwners 64 (Function.update x i 1) j ≤ naturalOwners 64 x j := by
    rw [naturalOwners_update_endpoint 64 x i (Or.inl rfl)]
    intro j
    by_cases hji : j = i
    · subst j
      simpa only [Function.update_self] using hc i
    · simp only [Function.update_of_ne hji, le_refl]
  have hcov : KSSpinSource.coefficientCovariance (naturalOwners 64 (Function.update x i 1)) ≤
      KSSpinSource.coefficientCovariance (naturalOwners 64 x) := by
    apply Matrix.le_iff.mpr
    rw [KSSpinSource.coefficientCovariance, KSSpinSource.coefficientCovariance, Matrix.diagonal_sub]
    exact Matrix.posSemidef_diagonal_iff.mpr (fun j => sub_nonneg.mpr
      (div_le_div_of_nonneg_right (hle j.1) (by norm_num)))
  have hm := ownerPotential_mono_covariance (signedLift (center A x)) (KSSpinSource.family A)
    (KSSpinSource.family_isHermitian A hA) (KSSpinSource.coefficientCovariance_posSemidef hc')
    (KSSpinSource.coefficientCovariance_posSemidef hc) hcov θ
  unfold spinPotential
  simpa only [center_update, hi, smul_zero, add_zero] using hm

/-- At a maximally frozen minimum, every original live atom is nonzero. -/
theorem eighth_live_atom_ne_zero [Nonempty n] (A : Fin N → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (θ : ℝ) {x : Fin N → ℝ}
    (hx : MaxFrozenMinimum (1 / 8) (eighthPotential A θ) x)
    (i : Fin N) (hi : |x i| < 1 / 8) : A i ≠ 0 := by
  intro hz
  exact hx.no_update (by norm_num) i hi (Or.inr rfl)
    (eighth_zero_atom_retirement A hA θ hx.1 i hz)

theorem spin_live_atom_ne_zero [Nonempty n] (A : Fin N → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (θ : ℝ) {x : Fin N → ℝ}
    (hx : MaxFrozenMinimum 1 (spinPotential A θ) x)
    (i : Fin N) (hi : |x i| < 1) : A i ≠ 0 := by
  intro hz
  exact hx.no_update (by norm_num) i hi (Or.inr rfl)
    (spin_zero_atom_retirement A hA θ hx.1 i hz)

theorem eighth_live_vector_ne_zero [Nonempty n] (v : Fin N → n → ℂ) (θ : ℝ)
    {x : Fin N → ℝ} (hx : MaxFrozenMinimum (1 / 8)
      (eighthPotential (fun i => KSRankOne.atom (v i)) θ) x)
    (i : Fin N) (hi : |x i| < 1 / 8) : v i ≠ 0 := by
  intro hz
  exact eighth_live_atom_ne_zero _ (fun _ => KSRankOne.atom_isHermitian _) θ hx i hi
    ((KSRankOne.atom_eq_zero_iff (v i)).mpr hz)

theorem spin_live_vector_ne_zero [Nonempty n] (v : Fin N → n → ℂ) (θ : ℝ)
    {x : Fin N → ℝ} (hx : MaxFrozenMinimum 1
      (spinPotential (fun i => KSRankOne.atom (v i)) θ) x)
    (i : Fin N) (hi : |x i| < 1) : v i ≠ 0 := by
  intro hz
  exact spin_live_atom_ne_zero _ (fun _ => KSRankOne.atom_isHermitian _) θ hx i hi
    ((KSRankOne.atom_eq_zero_iff (v i)).mpr hz)

theorem common_source_identity_constant (A : Fin N → Matrix n n ℂ) (u : ℝ) :
    covarianceSource (KSCommonSource.family A) (KSCommonSource.coefficientCovariance (fun _ => u)) 1 =
      u • KSSpinSource.doubled (∑ i, A i * A i) := by
  rw [KSCommonSource.source_eq_sum]
  simp only [Matrix.mul_one]
  have hsq (i : Fin N) : signedLift (A i) * signedLift (A i) = KSSpinSource.doubled (A i * A i) := by
    simp [signedLift, KSSpinSource.doubled, Matrix.fromBlocks_multiply]
  simp only [hsq]
  rw [← Finset.smul_sum, ← KSSpinSource.doubled_sum]

theorem common_initial_variance_le (v : Fin N → n → ℂ)
    (hparseval : (∑ i, KSRankOne.atom (v i)) = 1) {ε u : ℝ}
    (hε : ∀ i, ‖KSRankOne.atom (v i)‖ ≤ ε) (hu : 0 ≤ u) :
    covarianceSource (KSCommonSource.family (fun i => KSRankOne.atom (v i)))
      (KSCommonSource.coefficientCovariance (fun _ => u)) 1 ≤
      (u * ε) • (1 : Matrix (n ⊕ n) (n ⊕ n) ℂ) := by
  rw [common_source_identity_constant]
  have h := smul_le_smul_of_nonneg_left
    (KSSpinSource.doubled_mono (ks_parseval_square_sum_le v hparseval hε)) hu
  simpa only [KSSpinSource.doubled_smul, KSSpinSource.doubled_one, smul_smul] using h

theorem common_initial_bound [Nonempty n] (v : Fin N → n → ℂ)
    (hparseval : (∑ i, KSRankOne.atom (v i)) = 1) {ε : ℝ} (hεpos : 0 < ε)
    (hε : ∀ i, ‖KSRankOne.atom (v i)‖ ≤ ε) :
    ownerPotential 0 (KSCommonSource.family (fun i => KSRankOne.atom (v i)))
      (KSCommonSource.coefficientCovariance (fun _ => 64)) (ksRegularizerScale ε n) ≤
      18 * Real.sqrt ε := by
  have h := ks_ownerPotential_le_variance Matrix.isHermitian_zero
    (KSCommonSource.family (fun i => KSRankOne.atom (v i)))
    (KSCommonSource.family_isHermitian _ (fun i => KSRankOne.atom_isHermitian _))
    (KSCommonSource.coefficientCovariance_posSemidef (fun _ => by norm_num))
    (ksRegularizerScale_pos (n := n) hεpos).le
    (common_initial_variance_le v hparseval hε (by norm_num : (0 : ℝ) ≤ 64))
  rw [norm_zero, zero_add, ksRegularizerScale_budget] at h
  have hs : Real.sqrt (64 * ε) = 8 * Real.sqrt ε := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 64)]
    norm_num
  rw [hs] at h
  linarith

theorem eighth_initial_bound [Nonempty n] (v : Fin N → n → ℂ)
    (hparseval : (∑ i, KSRankOne.atom (v i)) = 1) {ε : ℝ} (hεpos : 0 < ε)
    (hε : ∀ i, ‖KSRankOne.atom (v i)‖ ≤ ε) :
    eighthPotential (fun i => KSRankOne.atom (v i)) (ksRegularizerScale ε n) 0 ≤
      18 * Real.sqrt ε := by
  have hc : center (fun i => KSRankOne.atom (v i)) 0 = 0 := by
    simp [KSPotentialModels.center]
  have ho : truncatedOwners (1 / 8) 64 (0 : Fin N → ℝ) = fun _ => 64 := by
    funext i
    norm_num [truncatedOwners, maskedOwners, live, naturalOwners]
  have hl : signedLift (0 : Matrix n n ℂ) = 0 := by
    ext a b
    cases a <;> cases b <;> simp [signedLift]
  unfold eighthPotential commonPotential
  rw [hc, ho, hl]
  exact common_initial_bound v hparseval hεpos hε

theorem spin_initial_bound [Nonempty n] (v : Fin N → n → ℂ)
    (hparseval : (∑ i, KSRankOne.atom (v i)) = 1) {ε : ℝ} (hεpos : 0 < ε)
    (hε : ∀ i, ‖KSRankOne.atom (v i)‖ ≤ ε) :
    spinPotential (fun i => KSRankOne.atom (v i)) (ksRegularizerScale ε n) 0 ≤
      (16 * Real.sqrt 2 + 2) * Real.sqrt ε := by
  have hc : center (fun i => KSRankOne.atom (v i)) 0 = 0 := by
    simp [KSPotentialModels.center]
  have ho : naturalOwners 64 (0 : Fin N → ℝ) = fun _ => 64 := by
    funext i
    norm_num [naturalOwners]
  have hl : signedLift (0 : Matrix n n ℂ) = 0 := by
    ext a b
    cases a <;> cases b <;> simp [signedLift]
  unfold spinPotential
  rw [hc, ho, hl]
  exact ks_spin_initial_bound v hparseval hεpos hε

theorem norm_le_eighthPotential [Nonempty n] (A : Fin N → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) {θ : ℝ} (hθ : 0 ≤ θ)
    {x : Fin N → ℝ} (hx : x ∈ ksCube (1 / 8)) : ‖center A x‖ ≤ eighthPotential A θ x := by
  exact ks_norm_le_signedLift_ownerPotential (center_isHermitian A hA x)
    (KSCommonSource.family A) (KSCommonSource.family_isHermitian A hA)
    (KSCommonSource.coefficientCovariance_posSemidef
      (fun i => maskedOwners_nonneg (by norm_num) (by norm_num) hx _ i)) hθ

theorem norm_le_spinPotential [Nonempty n] (A : Fin N → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) {θ : ℝ} (hθ : 0 ≤ θ)
    {x : Fin N → ℝ} (hx : x ∈ ksCube 1) : ‖center A x‖ ≤ spinPotential A θ x := by
  exact ks_norm_le_signedLift_ownerPotential (center_isHermitian A hA x)
    (KSSpinSource.family A) (KSSpinSource.family_isHermitian A hA)
    (KSSpinSource.coefficientCovariance_posSemidef (naturalOwners_nonneg (by norm_num) le_rfl hx)) hθ

theorem eighth_vertex_to_signing {d : ℕ} [Nonempty (Fin d)] (v : Fin N → Fin d → ℂ)
    (hparseval : (∑ i, KSRankOne.atom (v i)) = 1) {ε : ℝ} (hεpos : 0 < ε)
    (hε : ∀ i, spectralNorm (KSRankOne.atom (v i)) ≤ ε) {x : Fin N → ℝ}
    (hx : x ∈ ksCube (1 / 8))
    (hmin : IsMinOn (eighthPotential (fun i => KSRankOne.atom (v i)) (ksRegularizerScale ε (Fin d)))
      (ksCube (1 / 8)) x) (hvertex : ksVertex (1 / 8) x) :
    ∃ s : Fin N → ℝ, IsFullSigning s ∧
      spectralNorm (signedSum (fun i => KSRankOne.atom (v i)) s) ≤ 144 * Real.sqrt ε := by
  have hnorm := norm_le_eighthPotential (fun i => KSRankOne.atom (v i))
    (fun i => KSRankOne.atom_isHermitian _) (ksRegularizerScale_pos (n := Fin d) hεpos).le hx
  have hbound := hnorm.trans ((hmin (ksCube_zero (by norm_num))).trans
    (eighth_initial_bound v hparseval hεpos (fun i => by
      simpa only [spectralNorm_eq_scopedMatrixNorm] using hε i)))
  apply ks_vertex_signing_of_bound (fun i => KSRankOne.atom (v i)) (by norm_num) hvertex
  simpa only [spectralNorm_eq_scopedMatrixNorm, ← center_eq_signedSum] using
    (show ‖center (fun i => KSRankOne.atom (v i)) x‖ ≤ (1 / 8 : ℝ) * (144 * Real.sqrt ε) by
      nlinarith)

theorem spin_vertex_to_signing {d : ℕ} [Nonempty (Fin d)] (v : Fin N → Fin d → ℂ)
    (hparseval : (∑ i, KSRankOne.atom (v i)) = 1) {ε : ℝ} (hεpos : 0 < ε)
    (hε : ∀ i, spectralNorm (KSRankOne.atom (v i)) ≤ ε) {x : Fin N → ℝ}
    (hx : x ∈ ksCube 1)
    (hmin : IsMinOn (spinPotential (fun i => KSRankOne.atom (v i)) (ksRegularizerScale ε (Fin d)))
      (ksCube 1) x) (hvertex : ksVertex 1 x) :
    ∃ s : Fin N → ℝ, IsFullSigning s ∧
      spectralNorm (signedSum (fun i => KSRankOne.atom (v i)) s) ≤
        (16 * Real.sqrt 2 + 2) * Real.sqrt ε := by
  have hnorm := norm_le_spinPotential (fun i => KSRankOne.atom (v i))
    (fun i => KSRankOne.atom_isHermitian _) (ksRegularizerScale_pos (n := Fin d) hεpos).le hx
  have hbound := hnorm.trans ((hmin (ksCube_zero (by norm_num))).trans
    (spin_initial_bound v hparseval hεpos (fun i => by
      simpa only [spectralNorm_eq_scopedMatrixNorm] using hε i)))
  apply ks_vertex_signing_of_bound (fun i => KSRankOne.atom (v i)) (by norm_num) hvertex
  simpa only [spectralNorm_eq_scopedMatrixNorm, ← center_eq_signedSum, one_mul] using hbound

/-- This implication leaves precisely the actual-minimizer vertex assertion to
the analytic part of the radius-one-eighth proof. -/
theorem eighth_signing_of_maxFrozen_vertex {d : ℕ} [Nonempty (Fin d)]
    (v : Fin N → Fin d → ℂ) (hparseval : (∑ i, KSRankOne.atom (v i)) = 1)
    {ε : ℝ} (hεpos : 0 < ε) (hε : ∀ i, spectralNorm (KSRankOne.atom (v i)) ≤ ε)
    (hvertex : ∀ x, MaxFrozenMinimum (1 / 8)
      (eighthPotential (fun i => KSRankOne.atom (v i)) (ksRegularizerScale ε (Fin d))) x →
      ksVertex (1 / 8) x) :
    ∃ s : Fin N → ℝ, IsFullSigning s ∧
      spectralNorm (signedSum (fun i => KSRankOne.atom (v i)) s) ≤ 144 * Real.sqrt ε := by
  obtain ⟨x, hx⟩ := exists_maxFrozen_minimum (1 / 8) _
    (eighthPotential_has_minimum (fun i => KSRankOne.atom (v i))
      (fun i => KSRankOne.atom_isHermitian _) (ksRegularizerScale ε (Fin d)))
  exact eighth_vertex_to_signing v hparseval hεpos hε hx.1 hx.2.1 (hvertex x hx)

/-- This implication leaves precisely the actual-minimizer vertex assertion to
the analytic part of the spin proof. -/
theorem spin_signing_of_maxFrozen_vertex {d : ℕ} [Nonempty (Fin d)]
    (v : Fin N → Fin d → ℂ) (hparseval : (∑ i, KSRankOne.atom (v i)) = 1)
    {ε : ℝ} (hεpos : 0 < ε) (hε : ∀ i, spectralNorm (KSRankOne.atom (v i)) ≤ ε)
    (hvertex : ∀ x, MaxFrozenMinimum 1
      (spinPotential (fun i => KSRankOne.atom (v i)) (ksRegularizerScale ε (Fin d))) x →
      ksVertex 1 x) :
    ∃ s : Fin N → ℝ, IsFullSigning s ∧
      spectralNorm (signedSum (fun i => KSRankOne.atom (v i)) s) ≤
        (16 * Real.sqrt 2 + 2) * Real.sqrt ε := by
  obtain ⟨x, hx⟩ := exists_maxFrozen_minimum 1 _
    (spinPotential_has_minimum (fun i => KSRankOne.atom (v i))
      (fun i => KSRankOne.atom_isHermitian _) (ksRegularizerScale ε (Fin d)))
  exact spin_vertex_to_signing v hparseval hεpos hε hx.1 hx.2.1 (hvertex x hx)

theorem zero_dimension_signing (A : Fin N → CMatrix 0) {C ε : ℝ}
    (hC : 0 ≤ C) :
    ∃ s : Fin N → ℝ, IsFullSigning s ∧ spectralNorm (signedSum A s) ≤ C * Real.sqrt ε := by
  refine ⟨fun _ => 1, fun _ => Or.inl rfl, ?_⟩
  have hz : signedSum A (fun _ => 1) = 0 := Subsingleton.elim _ _
  rw [hz, spectralNorm_eq_scopedMatrixNorm, norm_zero]
  exact mul_nonneg hC (Real.sqrt_nonneg ε)

theorem zero_label_signing {d : ℕ} (A : Fin 0 → CMatrix d) {C ε : ℝ}
    (hC : 0 ≤ C) :
    ∃ s : Fin 0 → ℝ, IsFullSigning s ∧ spectralNorm (signedSum A s) ≤ C * Real.sqrt ε := by
  refine ⟨fun _ => 1, fun _ => Or.inl rfl, ?_⟩
  have hz : signedSum A (fun _ => 1) = 0 := by simp [signedSum]
  rw [hz, spectralNorm_eq_scopedMatrixNorm, norm_zero]
  exact mul_nonneg hC (Real.sqrt_nonneg ε)

/-- The explicit rank-one target includes zero vectors, with no choice of
normalization and no division by an atom size. -/
theorem rankOneFamily_vectors {d : ℕ} (A : Fin N → CMatrix d)
    (hA : ∀ i, KSIsRankOneAtom (A i)) :
    ∃ v : Fin N → Fin d → ℂ, ∀ i, A i = KSRankOne.atom (v i) := by
  classical
  choose v hv using hA
  refine ⟨v, fun i => ?_⟩
  ext a b
  exact hv i a b

/-- A vector proof in positive physical dimension supplies the precise matrix
target, including physical dimension zero and arbitrarily many zero atoms. -/
theorem statement_of_positive_dimension_vector_signings {C : ℝ} (hC : 0 ≤ C)
    (hvector : ∀ (N d : ℕ), 0 < d → ∀ (ε : ℝ), 0 < ε →
      ∀ v : Fin N → Fin d → ℂ,
        (∑ i, KSRankOne.atom (v i)) = 1 →
        (∀ i, spectralNorm (KSRankOne.atom (v i)) ≤ ε) →
        ∃ s : Fin N → ℝ, IsFullSigning s ∧
          spectralNorm (signedSum (fun i => KSRankOne.atom (v i)) s) ≤ C * Real.sqrt ε) :
    ksStatementWithConstant C := by
  intro N d ε hεpos A hA hparseval hε
  by_cases hd : d = 0
  · subst d
    exact zero_dimension_signing A hC
  obtain ⟨v, hv⟩ := rankOneFamily_vectors A hA
  have heq : A = fun i => KSRankOne.atom (v i) := funext hv
  subst A
  exact hvector N d (Nat.pos_of_ne_zero hd) ε hεpos v hparseval hε

/-- Reindexing the matrix statement loses no finite labels and assigns a sign
also to every zero atom. -/
theorem finiteFamily_signing_of_statement {ι : Type*} [Fintype ι] {d : ℕ}
    {C : ℝ} (hks : ksStatementWithConstant C) (A : ι → CMatrix d)
    (hA : ∀ i, KSIsRankOneAtom (A i)) {ε : ℝ} (hεpos : 0 < ε)
    (hparseval : (∑ i, A i) = 1) (hε : ∀ i, spectralNorm (A i) ≤ ε) :
    ∃ s : ι → ℝ, (∀ i, IsSign (s i)) ∧
      spectralNorm (∑ i, (s i : ℂ) • A i) ≤ C * Real.sqrt ε := by
  classical
  let e := Fintype.equivFin ι
  have hp : (∑ j, A (e.symm j)) = 1 := by
    rw [e.symm.sum_comp]
    exact hparseval
  obtain ⟨s, hs, hbound⟩ := hks (Fintype.card ι) d ε hεpos
    (fun j => A (e.symm j)) (fun j => hA _) hp (fun j => hε _)
  refine ⟨fun i => s (e i), fun i => hs (e i), ?_⟩
  have heq : (∑ i, (s (e i) : ℂ) • A i) =
      signedSum (fun j => A (e.symm j)) s := by
    exact Fintype.sum_equiv e _ _ (fun i => by simp)
  rw [heq]
  exact hbound

/-- The standard finite-vector formulation uses the squared Euclidean vector
norm, which is exactly the operator norm of its outer-product atom. -/
theorem finiteVectorFamily_signing_of_statement {ι : Type*} [Fintype ι] {d : ℕ}
    {C : ℝ} (hks : ksStatementWithConstant C) (v : ι → Fin d → ℂ)
    {ε : ℝ} (hεpos : 0 < ε)
    (hparseval : (∑ i, KSRankOne.atom (v i)) = 1)
    (hε : ∀ i, ‖(WithLp.toLp 2 (v i) : EuclideanSpace ℂ (Fin d))‖ ^ 2 ≤ ε) :
    ∃ s : ι → ℝ, (∀ i, IsSign (s i)) ∧
      spectralNorm (∑ i, (s i : ℂ) • KSRankOne.atom (v i)) ≤ C * Real.sqrt ε := by
  apply finiteFamily_signing_of_statement hks (fun i => KSRankOne.atom (v i))
    (fun i => ⟨v i, fun _ _ => rfl⟩) hεpos hparseval
  intro i
  rw [KSRankOne.atom_spectralNorm, KSRankOne.realTrace_atom_eq_norm_sq]
  exact hε i

end MatrixSpencer.KSFinalAssembly
