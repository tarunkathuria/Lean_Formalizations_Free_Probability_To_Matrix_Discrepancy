import MatrixSpencer.KSJacobiMatrixProjection
import MatrixSpencer.KSEighthManuscriptCappedSimplex



open Matrix
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSEighthManuscriptMatrixProjection
open KSJacobiMatrixProjection

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def Feasible (s : ℝ) (P : Matrix ι ι ℝ) : Prop :=
  P.IsSymm ∧ 0 ≤ P ∧ P ≤ 1 ∧ Matrix.trace P = s

omit [DecidableEq ι] in
theorem conjugate_mono (U P Q : Matrix ι ι ℝ) (h : P ≤ Q) :
    conjugate U P ≤ conjugate U Q := by
  apply Matrix.le_iff.mpr
  have hp := (Matrix.le_iff.mp h).mul_mul_conjTranspose_same U
  change (conjugate U (Q-P)).PosSemidef at hp
  rwa [conjugate_sub] at hp

theorem feasible_conjugate (U P : Matrix ι ι ℝ) (hU : Uᵀ * U = 1) (hU' : U * Uᵀ = 1)
    {s : ℝ} (hP : Feasible s P) : Feasible s (conjugate U P) := by
  refine ⟨conjugate_symmetric U P hP.1, ?_, ?_, ?_⟩
  · simpa [conjugate] using conjugate_mono U 0 P hP.2.1
  · simpa [conjugate, hU'] using conjugate_mono U P 1 hP.2.2.1
  · rw [conjugate_trace U P hU, hP.2.2.2]

def IsProjection (s : ℝ) (A P : Matrix ι ι ℝ) : Prop :=
  Feasible s P ∧ ∀ Y, Feasible s Y → frobeniusInner (A - P) (Y - P) ≤ 0

theorem projection_conjugate (U A P : Matrix ι ι ℝ)
    (hU : Uᵀ * U = 1) (hU' : U * Uᵀ = 1) {s : ℝ} (hP : IsProjection s A P) :
    IsProjection s (conjugate U A) (conjugate U P) := by
  refine ⟨feasible_conjugate U P hU hU' hP.1, ?_⟩
  intro Y hY
  have hY' := feasible_conjugate Uᵀ Y (by simpa using hU') (by simpa using hU) hY
  have h := hP.2 (conjugate Uᵀ Y) hY'
  have hback : conjugate U (conjugate Uᵀ Y) = Y := by
    simpa only [Matrix.transpose_transpose] using conjugate_inverse Uᵀ Y (by simpa using hU')
  rw [← hback, ← conjugate_sub, ← conjugate_sub, conjugate_inner U _ _ hU]
  exact h

/-- Nonexpansiveness, derived directly from the two projection inequalities. -/
theorem projection_nonexpansive {s : ℝ} {A B P Q : Matrix ι ι ℝ}
    (hP : IsProjection s A P) (hQ : IsProjection s B Q) :
    KSJacobiStep.frobeniusEnergy (P - Q) ≤ KSJacobiStep.frobeniusEnergy (A - B) := by
  have hp := hP.2 Q hQ.1
  have hq := hQ.2 P hP.1
  have hineq : KSJacobiStep.frobeniusEnergy (P - Q) ≤ frobeniusInner (A - B) (P - Q) := by
    rw [← frobeniusInner_self]
    simp only [frobeniusInner_sub_left, frobeniusInner_sub_right] at hp hq ⊢
    rw [frobeniusInner_comm Q P] at hq ⊢
    linarith
  have henergy := KSJacobiRayleigh.frobeniusEnergy_nonneg (P - Q)
  have hc := frobeniusInner_cauchy (A - B) (P - Q)
  have hdot : 0 ≤ frobeniusInner (A - B) (P - Q) := henergy.trans hineq
  have hsq : (KSJacobiStep.frobeniusEnergy (P - Q)) ^ 2 ≤
      (frobeniusInner (A - B) (P - Q)) ^ 2 := by nlinarith
  by_cases he : KSJacobiStep.frobeniusEnergy (P - Q) = 0
  · rw [he]
    exact KSJacobiRayleigh.frobeniusEnergy_nonneg _
  · have hepos := lt_of_le_of_ne henergy (Ne.symm he)
    nlinarith

theorem projection_distance_le {s : ℝ} {A P : Matrix ι ι ℝ}
    (hP : IsProjection s A P) (Y : Matrix ι ι ℝ) (hY : Feasible s Y) :
    KSJacobiStep.frobeniusEnergy (A - P) ≤ KSJacobiStep.frobeniusEnergy (A - Y) := by
  have hv := hP.2 Y hY
  have hp : KSJacobiStep.frobeniusEnergy (A - P) ≤
      KSJacobiStep.frobeniusEnergy (A - Y) + 2 * frobeniusInner (A - P) (Y - P) := by
    have hp' : (∑ i, ∑ j, (A i j - P i j) ^ 2) ≤
        ∑ i, ∑ j, ((A i j - Y i j) ^ 2 + 2 * ((A i j - P i j) * (Y i j - P i j))) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      nlinarith [sq_nonneg (Y i j - P i j)]
    simpa only [Finset.sum_add_distrib, ← Finset.mul_sum,
      KSJacobiStep.frobeniusEnergy, frobeniusInner, Matrix.sub_apply] using hp'
  linarith

theorem projection_unique {s : ℝ} {A P Q : Matrix ι ι ℝ}
    (hP : IsProjection s A P) (hQ : IsProjection s A Q) : P = Q := by
  have h := projection_nonexpansive hP hQ
  have h' : KSJacobiStep.frobeniusEnergy (P - Q) ≤ 0 := by
    simpa [KSJacobiStep.frobeniusEnergy] using h
  have hzero : KSJacobiStep.frobeniusEnergy (P - Q) = 0 :=
    le_antisymm h' (KSJacobiRayleigh.frobeniusEnergy_nonneg (P - Q))
  have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_nonneg (fun j _ => sq_nonneg ((P - Q) i j)))).mp hzero
  ext i j
  have hi := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j (_ : j ∈ Finset.univ) => sq_nonneg ((P - Q) i j))).mp (hall i (Finset.mem_univ _))
  have hij := hi j (Finset.mem_univ _)
  simp only [Matrix.sub_apply] at hij
  nlinarith

variable {d : ℕ}

theorem feasible_diagonal (p : Fin d → ℝ) {s : ℝ}
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (hs : ∑ i, p i = s) :
    Feasible s (Matrix.diagonal p) := by
  refine ⟨Matrix.isSymm_diagonal p, ?_, ?_, ?_⟩
  · exact Matrix.le_iff.mpr (by simpa using Matrix.PosSemidef.diagonal hp0)
  · apply Matrix.le_iff.mpr
    have heq : (1 : Matrix (Fin d) (Fin d) ℝ) - Matrix.diagonal p =
        Matrix.diagonal (fun i => 1-p i) := by
      ext i j
      by_cases hij : i = j <;> simp [hij]
    rw [heq]
    exact Matrix.PosSemidef.diagonal (fun i => sub_nonneg.mpr (hp1 i))
  · simpa using hs

theorem feasible_diagonal_entries {s : ℝ} {Y : Matrix (Fin d) (Fin d) ℝ}
    (hY : Feasible s Y) : (∀ i, 0 ≤ Y i i) ∧ (∀ i, Y i i ≤ 1) ∧ (∑ i, Y i i) = s := by
  refine ⟨?_, ?_, hY.2.2.2⟩
  · intro i
    have hi := (Matrix.le_iff.mp hY.2.1).2 (Pi.single i 1)
    simpa using hi
  · intro i
    have hi := (Matrix.le_iff.mp hY.2.2.1).2 (Pi.single i 1)
    have hi' : 0 ≤ 1 - Y i i := by simpa using hi
    linarith

theorem diagonal_projection (z : Fin d → ℝ) (s : ℝ) (h0 : 0 ≤ s) (hd : s ≤ d) :
    IsProjection s (Matrix.diagonal z)
      (Matrix.diagonal (KSEighthManuscriptCappedSimplex.project z s)) := by
  refine ⟨feasible_diagonal _ (KSEighthManuscriptCappedSimplex.project_nonneg z s)
    (KSEighthManuscriptCappedSimplex.project_le_one z s)
    (KSEighthManuscriptCappedSimplex.project_sum z h0 hd), ?_⟩
  intro Y hY
  have hdY := feasible_diagonal_entries hY
  have h := KSEighthManuscriptCappedSimplex.project_variational z h0 hd (fun i => Y i i)
    hdY.1 hdY.2.1 hdY.2.2
  have heq : frobeniusInner (Matrix.diagonal z - Matrix.diagonal (KSEighthManuscriptCappedSimplex.project z s))
      (Y - Matrix.diagonal (KSEighthManuscriptCappedSimplex.project z s)) =
      ∑ i, (z i - KSEighthManuscriptCappedSimplex.project z s i) *
        (Y i i - KSEighthManuscriptCappedSimplex.project z s i) := by
    unfold frobeniusInner
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [Ne.symm hji]
    · simp
  rw [heq]
  exact h

theorem exists_projection (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.IsSymm)
    (s : ℝ) (h0 : 0 ≤ s) (hd : s ≤ d) : ∃ P, IsProjection s A P := by
  have hAH : A.IsHermitian := by
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose, star_trivial] using hA
  let U : Matrix (Fin d) (Fin d) ℝ := hAH.eigenvectorUnitary
  have hU : Uᵀ * U = 1 := by
    simpa only [Matrix.conjTranspose, star_trivial] using unitary.coe_star_mul_self hAH.eigenvectorUnitary
  have hU' : U * Uᵀ = 1 := Matrix.mul_eq_one_comm.mp hU
  have hspec : conjugate U (Matrix.diagonal hAH.eigenvalues) = A := by
    simpa only [conjugate, U, Matrix.conjTranspose, star_trivial] using hAH.spectral_theorem.symm
  have hp := projection_conjugate U (Matrix.diagonal hAH.eigenvalues)
    (Matrix.diagonal (KSEighthManuscriptCappedSimplex.project hAH.eigenvalues s)) hU hU'
    (diagonal_projection hAH.eigenvalues s h0 hd)
  rw [hspec] at hp
  exact ⟨_, hp⟩

/-- Proof-only reference projection; absent from the computed report definition. -/
def exactProjection (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.IsSymm)
    (s : ℝ) (h0 : 0 ≤ s) (hd : s ≤ d) : Matrix (Fin d) (Fin d) ℝ :=
  Classical.choose (exists_projection A hA s h0 hd)

theorem exactProjection_isProjection (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.IsSymm)
    (s : ℝ) (h0 : 0 ≤ s) (hd : s ≤ d) :
    IsProjection s A (exactProjection A hA s h0 hd) :=
  Classical.choose_spec (exists_projection A hA s h0 hd)

/-- Actual finite numerical construction. -/
def report (A : Matrix (Fin d) (Fin d) ℝ) (s ν : ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  conjugate (KSJacobiRayleigh.finalBasis A ν)
    (Matrix.diagonal (KSEighthManuscriptCappedSimplex.project
      (fun i => KSJacobiRayleigh.finalMatrix A ν i i) s))

abbrev surrogate := @KSJacobiMatrixProjection.surrogate

theorem report_isProjection_surrogate (A : Matrix (Fin d) (Fin d) ℝ) (s : ℝ)
    (h0 : 0 ≤ s) (hd : s ≤ d) (ν : ℝ) :
    IsProjection s (surrogate A ν) (report A s ν) := by
  exact projection_conjugate (KSJacobiRayleigh.finalBasis A ν) _ _
    (KSJacobiIteration.accumulatedBasis_transpose_mul A _)
    (KSJacobiIteration.accumulatedBasis_mul_transpose A _)
    (diagonal_projection (fun i => KSJacobiRayleigh.finalMatrix A ν i i) s h0 hd)

theorem report_feasible (A : Matrix (Fin d) (Fin d) ℝ) (s : ℝ)
    (h0 : 0 ≤ s) (hd : s ≤ d) (ν : ℝ) : Feasible s (report A s ν) :=
  (report_isProjection_surrogate A s h0 hd ν).1

theorem report_posSemidef (A : Matrix (Fin d) (Fin d) ℝ) (s : ℝ)
    (h0 : 0 ≤ s) (hd : s ≤ d) (ν : ℝ) : (report A s ν).PosSemidef := by
  simpa using Matrix.le_iff.mp (report_feasible A s h0 hd ν).2.1

theorem report_accuracy_for_projection (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.IsSymm)
    (s : ℝ) (h0 : 0 ≤ s) (hd : s ≤ d) {ν : ℝ} (hν : 0 < ν)
    (P : Matrix (Fin d) (Fin d) ℝ) (hP : IsProjection s A P) :
    Real.sqrt (KSJacobiStep.frobeniusEnergy (report A s ν - P)) ≤ ν := by
  have h := projection_nonexpansive (report_isProjection_surrogate A s h0 hd ν) hP
  have he : KSJacobiStep.frobeniusEnergy (surrogate A ν - A) =
      KSJacobiStep.frobeniusEnergy (A - surrogate A ν) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [Matrix.sub_apply]
    ring
  rw [he] at h
  exact (Real.sqrt_le_iff).mpr ⟨hν.le, h.trans (KSJacobiMatrixProjection.surrogate_error A hA hν)⟩

theorem report_accuracy (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.IsSymm)
    (s : ℝ) (h0 : 0 ≤ s) (hd : s ≤ d) {ν : ℝ} (hν : 0 < ν) :
    Real.sqrt (KSJacobiStep.frobeniusEnergy
      (report A s ν - exactProjection A hA s h0 hd)) ≤ ν :=
  report_accuracy_for_projection A hA s h0 hd hν _
    (exactProjection_isProjection A hA s h0 hd)

end MatrixSpencer.KSEighthManuscriptMatrixProjection
