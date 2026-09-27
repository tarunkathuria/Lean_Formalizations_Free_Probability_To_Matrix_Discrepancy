import MatrixSpencer.CovarianceSampler
import Mathlib.Tactic

/-!
# Spectral dust deletion for a real covariance

The deletion is an actual orthogonal spectral truncation: eigenvalues strictly
below a positive threshold are replaced by zero. The accounting charges only
the positive eigenvalues that disappear, so it telescopes with support losses.
No covariance optimization or partial-coloring phase is assumed in this file.
-/

open scoped BigOperators MatrixOrder Matrix

noncomputable section
namespace MatrixSpencer
namespace CovarianceDust

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def spectralMatrix {C : Matrix ι ι ℝ} (hC : C.IsHermitian) (f : ι → ℝ) :
    Matrix ι ι ℝ :=
  (hC.eigenvectorUnitary : Matrix ι ι ℝ) * Matrix.diagonal f *
    (hC.eigenvectorUnitary : Matrix ι ι ℝ)ᴴ

lemma spectralMatrix_hermitian {C : Matrix ι ι ℝ} (hC : C.IsHermitian) (f : ι → ℝ) :
    (spectralMatrix hC f).IsHermitian := by
  unfold spectralMatrix
  apply Matrix.isHermitian_mul_mul_conjTranspose
  exact Matrix.isHermitian_diagonal_iff.mpr (fun j => show star (f j) = f j from rfl)

lemma spectralMatrix_posSemidef {C : Matrix ι ι ℝ} (hC : C.IsHermitian) {f : ι → ℝ}
    (hf : ∀ j, 0 ≤ f j) : (spectralMatrix hC f).PosSemidef := by
  exact (Matrix.posSemidef_diagonal_iff.mpr hf).mul_mul_conjTranspose_same _

lemma spectralMatrix_sub {C : Matrix ι ι ℝ} (hC : C.IsHermitian) (f g : ι → ℝ) :
    spectralMatrix hC (f - g) = spectralMatrix hC f - spectralMatrix hC g := by
  unfold spectralMatrix
  rw [show Matrix.diagonal (f - g) = Matrix.diagonal f - Matrix.diagonal g from
    (Matrix.diagonal_sub f g).symm, Matrix.mul_sub, Matrix.sub_mul]

lemma spectralMatrix_mono {C : Matrix ι ι ℝ} (hC : C.IsHermitian)
    {f g : ι → ℝ} (hfg : ∀ j, f j ≤ g j) : spectralMatrix hC f ≤ spectralMatrix hC g := by
  apply Matrix.le_iff.mpr
  rw [← spectralMatrix_sub]
  exact spectralMatrix_posSemidef hC (fun j => sub_nonneg.mpr (hfg j))

lemma spectralMatrix_mul {C : Matrix ι ι ℝ} (hC : C.IsHermitian) (f g : ι → ℝ) :
    spectralMatrix hC f * spectralMatrix hC g = spectralMatrix hC (f * g) := by
  have hu : (hC.eigenvectorUnitary : Matrix ι ι ℝ)ᴴ * hC.eigenvectorUnitary = 1 :=
    unitary.coe_star_mul_self hC.eigenvectorUnitary
  simp only [spectralMatrix, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (hC.eigenvectorUnitary : Matrix ι ι ℝ)ᴴ, hu, Matrix.one_mul,
    ← Matrix.mul_assoc (Matrix.diagonal _), Matrix.diagonal_mul_diagonal]
  rfl

lemma spectralMatrix_smul {C : Matrix ι ι ℝ} (hC : C.IsHermitian) (a : ℝ) (f : ι → ℝ) :
    spectralMatrix hC (a • f) = a • spectralMatrix hC f := by
  simp only [spectralMatrix, Matrix.diagonal_smul, Matrix.mul_smul, Matrix.smul_mul]

lemma spectralMatrix_eigenvalues {C : Matrix ι ι ℝ} (hC : C.IsHermitian) :
    spectralMatrix hC hC.eigenvalues = C := hC.spectral_theorem.symm

lemma spectralMatrix_trace {C : Matrix ι ι ℝ} (hC : C.IsHermitian) (f : ι → ℝ) :
    realTrace (spectralMatrix hC f) = ∑ j, f j := by
  have hu : (hC.eigenvectorUnitary : Matrix ι ι ℝ)ᴴ * hC.eigenvectorUnitary = 1 :=
    unitary.coe_star_mul_self hC.eigenvectorUnitary
  rw [spectralMatrix, realTrace_mul_cycle, hu, Matrix.one_mul]
  simp [realTrace, Matrix.trace_diagonal]

lemma spectralMatrix_rank {C : Matrix ι ι ℝ} (hC : C.IsHermitian) (f : ι → ℝ) :
    (spectralMatrix hC f).rank = Fintype.card {j // f j ≠ 0} := by
  change ((hC.eigenvectorUnitary : Matrix ι ι ℝ) * Matrix.diagonal f *
    star (hC.eigenvectorUnitary : Matrix ι ι ℝ)).rank = _
  rw [← unitary.coe_star]
  simp [-isUnit_iff_ne_zero, -unitary.coe_star, Matrix.rank_diagonal]

/-- Retain exactly the eigenvalues greater than or equal to the threshold. -/
def dust {C : Matrix ι ι ℝ} (hC : C.IsHermitian) (δ : ℝ) : Matrix ι ι ℝ :=
  spectralMatrix hC (fun j => if δ ≤ hC.eigenvalues j then hC.eigenvalues j else 0)

/-- The orthogonal projector onto the retained eigenspaces. -/
def retainedProjection {C : Matrix ι ι ℝ} (hC : C.IsHermitian) (δ : ℝ) : Matrix ι ι ℝ :=
  spectralMatrix hC (fun j => if δ ≤ hC.eigenvalues j then 1 else 0)

lemma dust_hermitian {C : Matrix ι ι ℝ} (hC : C.IsHermitian) (δ : ℝ) :
    (dust hC δ).IsHermitian := spectralMatrix_hermitian hC _

lemma dust_posSemidef {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (δ : ℝ) :
    (dust hC.isHermitian δ).PosSemidef :=
  spectralMatrix_posSemidef hC.isHermitian (fun j => by
    split_ifs
    · exact hC.eigenvalues_nonneg j
    · exact le_rfl)

lemma dust_le {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (δ : ℝ) :
    dust hC.isHermitian δ ≤ C := by
  conv_rhs => rw [← spectralMatrix_eigenvalues hC.isHermitian]
  exact spectralMatrix_mono hC.isHermitian (fun j => by
    split_ifs
    · exact le_rfl
    · exact hC.eigenvalues_nonneg j)

lemma dust_range_le {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (δ : ℝ) :
    LinearMap.range (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)
      (dust hC.isHermitian δ)).toLinearMap ≤
    LinearMap.range (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) C).toLinearMap :=
  posSemidef_range_le_of_le (dust_posSemidef hC δ) hC (dust_le hC δ)

lemma retainedProjection_posSemidef {C : Matrix ι ι ℝ} (hC : C.IsHermitian) (δ : ℝ) :
    (retainedProjection hC δ).PosSemidef :=
  spectralMatrix_posSemidef hC (fun _ => by split_ifs <;> norm_num)

lemma retainedProjection_idempotent {C : Matrix ι ι ℝ} (hC : C.IsHermitian) (δ : ℝ) :
    retainedProjection hC δ * retainedProjection hC δ = retainedProjection hC δ := by
  rw [retainedProjection, spectralMatrix_mul]
  congr 1
  funext j
  dsimp
  split_ifs <;> norm_num

lemma retainedProjection_mul_dust {C : Matrix ι ι ℝ} (hC : C.IsHermitian) (δ : ℝ) :
    retainedProjection hC δ * dust hC δ = dust hC δ := by
  rw [retainedProjection, dust, spectralMatrix_mul]
  congr 1
  funext j
  dsimp
  split_ifs <;> simp

lemma dust_spectral_floor {C : Matrix ι ι ℝ} (hC : C.IsHermitian) (δ : ℝ) :
    δ • retainedProjection hC δ ≤ dust hC δ := by
  rw [retainedProjection, dust, ← spectralMatrix_smul]
  apply spectralMatrix_mono
  intro j
  dsimp
  split_ifs with hj
  · simpa only [mul_one] using hj
  · simp

/-- The projector acts identically on the actual range of the retained matrix. -/
lemma retainedProjection_mulVec_of_mem_range {C : Matrix ι ι ℝ}
    (hC : C.IsHermitian) (δ : ℝ) {u : ι → ℝ}
    (hu : u ∈ LinearMap.range (dust hC δ).mulVecLin) :
    retainedProjection hC δ *ᵥ u = u := by
  obtain ⟨v, rfl⟩ := hu
  change retainedProjection hC δ *ᵥ (dust hC δ *ᵥ v) = dust hC δ *ᵥ v
  rw [Matrix.mulVec_mulVec, retainedProjection_mul_dust]

/-- A quadratic spectral floor on actual coefficient vectors in the retained range. -/
lemma dust_quadratic_floor {C : Matrix ι ι ℝ} (hC : C.IsHermitian) (δ : ℝ)
    {u : ι → ℝ} (hu : u ∈ LinearMap.range (dust hC δ).mulVecLin) :
    δ * (u ⬝ᵥ u) ≤ u ⬝ᵥ (dust hC δ *ᵥ u) := by
  have h := (Matrix.le_iff.mp (dust_spectral_floor hC δ)).2 u
  simp only [star_trivial, Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec,
    dotProduct_smul, smul_eq_mul, retainedProjection_mulVec_of_mem_range hC δ hu] at h
  exact sub_nonneg.mp h

lemma retained_eigenvalue_ne_zero {e δ : ℝ} (hδ : 0 < δ) :
    (if δ ≤ e then e else 0) ≠ 0 ↔ δ ≤ e := by
  split_ifs with h
  · simp only [h, iff_true]
    exact ne_of_gt (lt_of_lt_of_le hδ h)
  · simp only [ne_eq, not_true_eq_false, h]

lemma dust_rank {C : Matrix ι ι ℝ} (hC : C.IsHermitian) {δ : ℝ} (hδ : 0 < δ) :
    (dust hC δ).rank = Fintype.card {j // δ ≤ hC.eigenvalues j} := by
  rw [dust, spectralMatrix_rank]
  apply Fintype.card_congr
  exact Equiv.subtypeEquivRight (fun _ => retained_eigenvalue_ne_zero hδ)

lemma dust_rank_le {C : Matrix ι ι ℝ} (hC : C.IsHermitian) {δ : ℝ} (hδ : 0 < δ) :
    (dust hC δ).rank ≤ C.rank := by
  rw [dust_rank hC hδ, hC.rank_eq_card_non_zero_eigs]
  exact Fintype.card_subtype_mono _ _ (fun j hj => ne_of_gt (lt_of_lt_of_le hδ hj))

lemma dust_trace {C : Matrix ι ι ℝ} (hC : C.IsHermitian) (δ : ℝ) :
    realTrace (dust hC δ) = ∑ j, if δ ≤ hC.eigenvalues j then hC.eigenvalues j else 0 :=
  spectralMatrix_trace hC _

/-- An individual deleted eigenvalue is paid for by its lost support dimension. -/
lemma eigenvalue_loss_le {e δ : ℝ} (hδ : 0 < δ) :
    e - (if δ ≤ e then e else 0) ≤
      δ * ((if e ≠ 0 then (1 : ℝ) else 0) - (if δ ≤ e then 1 else 0)) := by
  by_cases hd : δ ≤ e
  · have hn : e ≠ 0 := ne_of_gt (lt_of_lt_of_le hδ hd)
    simp [hd, hn]
  · by_cases hn : e = 0
    · simp [hn, not_le.mpr hδ]
    · simpa [hd, hn] using (le_of_lt (lt_of_not_ge hd))

/-- Dust costs at most threshold times the number of positive directions deleted. -/
lemma dust_trace_loss_le_rank_drop {C : Matrix ι ι ℝ} (hC : C.PosSemidef)
    {δ : ℝ} (hδ : 0 < δ) :
    realTrace (C - dust hC.isHermitian δ) ≤
      δ * (C.rank - (dust hC.isHermitian δ).rank : ℕ) := by
  rw [realTrace_sub, realTrace_real_eq_sum_eigenvalues hC.isHermitian, dust_trace,
    ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j, δ * ((if hC.isHermitian.eigenvalues j ≠ 0 then (1 : ℝ) else 0) -
          (if δ ≤ hC.isHermitian.eigenvalues j then 1 else 0)) :=
      Finset.sum_le_sum (fun j _ => eigenvalue_loss_le hδ)
    _ = δ * (C.rank - (dust hC.isHermitian δ).rank : ℕ) := by
      rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_boole, Finset.sum_boole,
        Nat.cast_sub (dust_rank_le hC.isHermitian hδ), dust_rank hC.isHermitian hδ,
        hC.isHermitian.rank_eq_card_non_zero_eigs, Fintype.card_subtype, Fintype.card_subtype]

/-- Every actual positive eigenvalue deletion strictly reduces the covariance rank. -/
lemma dust_rank_lt_of_deleted_eigenvalue {C : Matrix ι ι ℝ} (hC : C.IsHermitian)
    {δ : ℝ} (hδ : 0 < δ) {j : ι}
    (hj : hC.eigenvalues j ≠ 0) (hjδ : hC.eigenvalues j < δ) :
    (dust hC δ).rank < C.rank := by
  rw [dust_rank hC hδ, hC.rank_eq_card_non_zero_eigs]
  let f : {i // δ ≤ hC.eigenvalues i} → {i // hC.eigenvalues i ≠ 0} :=
    fun i => ⟨i.1, ne_of_gt (lt_of_lt_of_le hδ i.2)⟩
  apply Fintype.card_lt_of_injective_of_notMem f
    (fun a b h => Subtype.ext (show a.1 = b.1 from
      congrArg (fun x : {i // hC.eigenvalues i ≠ 0} => x.1) h)) (b := ⟨j, hj⟩)
  rintro ⟨i, hi⟩
  have hij : i.1 = j := congrArg Subtype.val hi
  exact not_le.mpr hjδ (hij ▸ i.2)

/-- If no positive direction disappears, the truncation is exactly the original matrix. -/
lemma dust_eq_of_no_deletion {C : Matrix ι ι ℝ} (hC : C.IsHermitian) (δ : ℝ)
    (hkeep : ∀ j, hC.eigenvalues j ≠ 0 → δ ≤ hC.eigenvalues j) : dust hC δ = C := by
  conv_rhs => rw [← spectralMatrix_eigenvalues hC]
  unfold dust
  congr 1
  funext j
  by_cases hj : hC.eigenvalues j = 0
  · simp [hj]
  · simp [hkeep j hj]

/-- Thus any nontrivial dust cleanup consumes at least one support dimension. -/
lemma dust_rank_lt_of_ne {C : Matrix ι ι ℝ} (hC : C.IsHermitian)
    {δ : ℝ} (hδ : 0 < δ) (hne : dust hC δ ≠ C) : (dust hC δ).rank < C.rank := by
  have hex : ∃ j, hC.eigenvalues j ≠ 0 ∧ hC.eigenvalues j < δ := by
    by_contra h
    push_neg at h
    exact hne (dust_eq_of_no_deletion hC δ h)
  obtain ⟨j, hj, hjδ⟩ := hex
  exact dust_rank_lt_of_deleted_eigenvalue hC hδ hj hjδ

/-- The same floor in the explicitly Euclidean coefficient space. -/
lemma dust_euclidean_floor {C : Matrix ι ι ℝ} (hC : C.IsHermitian) (δ : ℝ)
    {u : EuclideanSpace ℝ ι}
    (hu : u ∈ LinearMap.range (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)
      (dust hC δ)).toLinearMap) :
    δ * ‖u‖ ^ 2 ≤ inner ℝ u (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) (dust hC δ) u) := by
  have hu' : WithLp.ofLp u ∈ LinearMap.range (dust hC δ).mulVecLin := by
    obtain ⟨v, hv⟩ := hu
    exact ⟨WithLp.ofLp v, congrArg WithLp.ofLp hv⟩
  have hnorm : ‖u‖ ^ 2 = WithLp.ofLp u ⬝ᵥ WithLp.ofLp u := by
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] using
      (real_inner_self_eq_norm_sq u).symm
  rw [hnorm, EuclideanSpace.inner_eq_star_dotProduct]
  rw [star_trivial]
  exact (dust_quadratic_floor hC δ hu').trans_eq (dotProduct_comm _ _)

/-- Every nonzero eigenvalue of the resulting covariance is at least the threshold. -/
lemma dust_nonzero_eigenvalue_ge {C : Matrix ι ι ℝ} (hC : C.IsHermitian) (δ : ℝ)
    {j : ι} (hj : (dust_hermitian hC δ).eigenvalues j ≠ 0) :
    δ ≤ (dust_hermitian hC δ).eigenvalues j := by
  let hD : (dust hC δ).IsHermitian := dust_hermitian hC δ
  have hu := covarianceEigenvector_mem_range hD hj
  have hf := dust_euclidean_floor hC δ hu
  have he : Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) (dust hC δ) (hD.eigenvectorBasis j) =
      hD.eigenvalues j • hD.eigenvectorBasis j := by
    apply (WithLp.equiv 2 (ι → ℝ)).injective
    exact hD.mulVec_eigenvectorBasis j
  rw [he, inner_smul_right, real_inner_self_eq_norm_sq,
    hD.eigenvectorBasis.orthonormal.norm_eq_one] at hf
  simpa only [one_pow, mul_one] using hf

/-- The retained projector has exactly the actual range of the truncated covariance. -/
lemma dust_range_eq_retainedProjection {C : Matrix ι ι ℝ} (hC : C.PosSemidef)
    {δ : ℝ} (hδ : 0 < δ) :
    LinearMap.range (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)
      (dust hC.isHermitian δ)).toLinearMap =
    LinearMap.range (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)
      (retainedProjection hC.isHermitian δ)).toLinearMap := by
  apply le_antisymm
  · intro u hu
    refine ⟨u, ?_⟩
    apply (WithLp.equiv 2 (ι → ℝ)).injective
    apply retainedProjection_mulVec_of_mem_range
    obtain ⟨v, hv⟩ := hu
    exact ⟨WithLp.ofLp v, congrArg WithLp.ofLp hv⟩
  · have h := posSemidef_range_le_of_le
      ((retainedProjection_posSemidef hC.isHermitian δ).smul hδ.le)
      (dust_posSemidef hC δ) (dust_spectral_floor hC.isHermitian δ)
    rwa [euclideanMatrix_range_smul _ hδ.ne'] at h

omit [DecidableEq ι] in
/-- Positive-semidefinite order also preserves matrix rank. -/
lemma rank_le_of_posSemidef_le {A B : Matrix ι ι ℝ} (hA : A.PosSemidef) (hAB : A ≤ B) :
    A.rank ≤ B.rank := by
  have hk : LinearMap.ker B.mulVecLin ≤ LinearMap.ker A.mulVecLin := by
    intro x hx
    exact posSemidef_mulVec_eq_zero_of_le hA hAB hx
  have hdim := Submodule.finrank_mono hk
  have hAker := A.mulVecLin.finrank_range_add_finrank_ker
  have hBker := B.mulVecLin.finrank_range_add_finrank_ker
  unfold Matrix.rank
  omega

omit [Fintype ι] [DecidableEq ι] in
/-- Finite accounting for losses charged to successive natural-number rank drops. -/
lemma sum_loss_le_rank_difference (r : ℕ → ℕ) (loss : ℕ → ℝ) {δ : ℝ}
    (N : ℕ) (hr : ∀ j < N, r (j + 1) ≤ r j)
    (hloss : ∀ j < N, loss j ≤ δ * (r j - r (j + 1) : ℕ)) :
    ∑ j ∈ Finset.range N, loss j ≤ δ * ((r 0 : ℝ) - r N) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hprev := ih (fun j hj => hr j (Nat.lt_succ_of_lt hj))
      (fun j hj => hloss j (Nat.lt_succ_of_lt hj))
    have hlast := hloss N (Nat.lt_succ_self N)
    rw [Nat.cast_sub (hr N (Nat.lt_succ_self N))] at hlast
    rw [Finset.sum_range_succ]
    calc
      _ ≤ δ * ((r 0 : ℝ) - r N) + δ * ((r N : ℝ) - r (N + 1)) :=
        add_le_add hprev hlast
      _ = _ := by ring

omit [Fintype ι] [DecidableEq ι] in
lemma sum_loss_le_initial_rank (r : ℕ → ℕ) (loss : ℕ → ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (N : ℕ) (hr : ∀ j < N, r (j + 1) ≤ r j)
    (hloss : ∀ j < N, loss j ≤ δ * (r j - r (j + 1) : ℕ)) :
    ∑ j ∈ Finset.range N, loss j ≤ δ * r 0 := by
  exact (sum_loss_le_rank_difference r loss N hr hloss).trans
    (mul_le_mul_of_nonneg_left (sub_le_self _ (Nat.cast_nonneg _)) hδ)

/-- Dust costs telescope even with arbitrary further positive reductions after each deletion. -/
lemma nested_dust_total_trace_le (C : ℕ → Matrix ι ι ℝ)
    (hC : ∀ j, (C j).PosSemidef) {δ : ℝ} (hδ : 0 < δ) (N : ℕ)
    (hnext : ∀ j < N, C (j + 1) ≤ dust (hC j).isHermitian δ) :
    ∑ j ∈ Finset.range N, realTrace (C j - dust (hC j).isHermitian δ) ≤
      δ * (C 0).rank := by
  apply sum_loss_le_initial_rank (fun j => (C j).rank) _ hδ.le N
  · intro j hj
    exact rank_le_of_posSemidef_le (hC (j + 1)) ((hnext j hj).trans (dust_le (hC j) δ))
  · intro j hj
    apply (dust_trace_loss_le_rank_drop (hC j) hδ).trans
    apply mul_le_mul_of_nonneg_left _ hδ.le
    exact_mod_cast Nat.sub_le_sub_left
      (rank_le_of_posSemidef_le (hC (j + 1)) (hnext j hj)) (C j).rank

omit [Fintype ι] [DecidableEq ι] in
/-- A finite run with a strict rank loss at each step has at most the initial rank many steps. -/
lemma length_le_initial_rank_of_strict_drop (r : ℕ → ℕ) (N : ℕ)
    (hr : ∀ j < N, r (j + 1) < r j) : N ≤ r 0 := by
  have hstrong : N + r N ≤ r 0 := by
    induction N with
    | zero => simp
    | succ N ih =>
      have hprev := ih (fun j hj => hr j (Nat.lt_succ_of_lt hj))
      have hlast := hr N (Nat.lt_succ_self N)
      omega
  omega

/-- Nontrivial cleanups cannot restart a finite-dimensional dust loop indefinitely. -/
lemma nested_nontrivial_dust_length_le (C : ℕ → Matrix ι ι ℝ)
    (hC : ∀ j, (C j).PosSemidef) {δ : ℝ} (hδ : 0 < δ) (N : ℕ)
    (hnext : ∀ j < N, C (j + 1) ≤ dust (hC j).isHermitian δ)
    (hne : ∀ j < N, dust (hC j).isHermitian δ ≠ C j) : N ≤ (C 0).rank := by
  apply length_le_initial_rank_of_strict_drop (fun j => (C j).rank) N
  intro j hj
  exact (rank_le_of_posSemidef_le (hC (j + 1)) (hnext j hj)).trans_lt
    (dust_rank_lt_of_ne (hC j).isHermitian hδ (hne j hj))

end CovarianceDust
end MatrixSpencer
