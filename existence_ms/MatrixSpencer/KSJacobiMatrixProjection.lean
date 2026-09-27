import MatrixSpencer.KSSimplexProjection
import MatrixSpencer.KSJacobiRayleigh
import Mathlib.Analysis.Matrix.Order

/-!
# Matrix simplex projection from the explicit finite Jacobi run

The report diagonalizes approximately using the already verified finite rotation
run, projects the computed diagonal by the finite scalar threshold scan, and
conjugates back by the computed basis. Spectral decomposition is used only to
prove that an exact metric projection exists as a mathematical specification;
no spectral vector is an input to, or selected by, the report.
-/

open Matrix
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSJacobiMatrixProjection

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The ordinary Euclidean inner product of all real matrix entries. -/
def frobeniusInner (A B : Matrix ι ι ℝ) : ℝ := ∑ i, ∑ j, A i j * B i j

omit [DecidableEq ι] in
theorem frobeniusInner_eq_trace (A B : Matrix ι ι ℝ) :
    frobeniusInner A B = Matrix.trace (Aᵀ * B) := by
  simp only [frobeniusInner, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
  exact Finset.sum_comm

omit [DecidableEq ι] in
theorem frobeniusInner_self (A : Matrix ι ι ℝ) :
    frobeniusInner A A = KSJacobiStep.frobeniusEnergy A := by
  simp only [frobeniusInner, KSJacobiStep.frobeniusEnergy, pow_two]

omit [DecidableEq ι] in
theorem frobeniusInner_comm (A B : Matrix ι ι ℝ) :
    frobeniusInner A B = frobeniusInner B A := by
  simp only [frobeniusInner, mul_comm]

omit [DecidableEq ι] in
theorem frobeniusInner_sub_left (A B C : Matrix ι ι ℝ) :
    frobeniusInner (A - B) C = frobeniusInner A C - frobeniusInner B C := by
  simp [frobeniusInner, sub_mul, Finset.sum_sub_distrib]

omit [DecidableEq ι] in
theorem frobeniusInner_sub_right (A B C : Matrix ι ι ℝ) :
    frobeniusInner A (B - C) = frobeniusInner A B - frobeniusInner A C := by
  simp [frobeniusInner, mul_sub, Finset.sum_sub_distrib]

omit [DecidableEq ι] in
theorem frobeniusInner_cauchy (A B : Matrix ι ι ℝ) :
    (frobeniusInner A B) ^ 2 ≤
      KSJacobiStep.frobeniusEnergy A * KSJacobiStep.frobeniusEnergy B := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (ι × ι))
    (fun p => A p.1 p.2) (fun p => B p.1 p.2)
  simpa only [← Finset.univ_product_univ, Finset.sum_product,
    frobeniusInner, KSJacobiStep.frobeniusEnergy] using h

/-- Conjugation in the original coordinate frame. -/
def conjugate (U A : Matrix ι ι ℝ) : Matrix ι ι ℝ := U * A * Uᵀ

omit [DecidableEq ι] in
theorem conjugate_sub (U A B : Matrix ι ι ℝ) :
    conjugate U (A - B) = conjugate U A - conjugate U B := by
  simp [conjugate, Matrix.mul_sub, Matrix.sub_mul]

theorem conjugate_inverse (U A : Matrix ι ι ℝ) (hU : Uᵀ * U = 1) :
    conjugate Uᵀ (conjugate U A) = A := by
  simp only [conjugate, Matrix.transpose_transpose, Matrix.mul_assoc,
    ← Matrix.mul_assoc Uᵀ U, hU, Matrix.one_mul, Matrix.mul_one]

omit [DecidableEq ι] in
theorem conjugate_symmetric (U A : Matrix ι ι ℝ) (hA : A.IsSymm) :
    (conjugate U A).IsSymm := by
  change (U * A * Uᵀ)ᵀ = U * A * Uᵀ
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hA.eq, Matrix.mul_assoc]

theorem conjugate_trace (U A : Matrix ι ι ℝ) (hU : Uᵀ * U = 1) :
    Matrix.trace (conjugate U A) = Matrix.trace A := by
  rw [conjugate, Matrix.trace_mul_cycle, hU, Matrix.one_mul]

theorem conjugate_scalar (U : Matrix ι ι ℝ) (a : ℝ) (hU : U * Uᵀ = 1) :
    conjugate U (a • (1 : Matrix ι ι ℝ)) = a • (1 : Matrix ι ι ℝ) := by
  simp only [conjugate, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hU]

theorem conjugate_inner (U A B : Matrix ι ι ℝ) (hU : Uᵀ * U = 1) :
    frobeniusInner (conjugate U A) (conjugate U B) = frobeniusInner A B := by
  rw [frobeniusInner_eq_trace, frobeniusInner_eq_trace]
  simp only [conjugate, Matrix.transpose_mul, Matrix.transpose_transpose]
  calc
    _ = Matrix.trace (U * (Aᵀ * (Uᵀ * U) * B) * Uᵀ) := by simp only [Matrix.mul_assoc]
    _ = Matrix.trace (U * (Aᵀ * B) * Uᵀ) := by rw [hU, Matrix.mul_one]
    _ = _ := by rw [Matrix.trace_mul_cycle, hU, Matrix.one_mul]

theorem conjugate_energy (U A : Matrix ι ι ℝ) (hU : Uᵀ * U = 1) :
    KSJacobiStep.frobeniusEnergy (conjugate U A) = KSJacobiStep.frobeniusEnergy A := by
  rw [← frobeniusInner_self, conjugate_inner U A A hU, frobeniusInner_self]

/-- Symmetric matrices above a scalar floor with prescribed trace. -/
def Feasible (a s : ℝ) (P : Matrix ι ι ℝ) : Prop :=
  P.IsSymm ∧ a • (1 : Matrix ι ι ℝ) ≤ P ∧ Matrix.trace P = s

theorem feasible_conjugate (U P : Matrix ι ι ℝ) (hU : Uᵀ * U = 1) (hU' : U * Uᵀ = 1)
    {a s : ℝ} (hP : Feasible a s P) : Feasible a s (conjugate U P) := by
  refine ⟨conjugate_symmetric U P hP.1, ?_, ?_⟩
  · apply Matrix.le_iff.mpr
    have h := (Matrix.le_iff.mp hP.2.1).mul_mul_conjTranspose_same U
    change (U * (P - a • 1) * Uᵀ).PosSemidef at h
    change (conjugate U (P - a • 1)).PosSemidef at h
    rw [conjugate_sub, conjugate_scalar U a hU'] at h
    exact h
  · rw [conjugate_trace U P hU, hP.2.2]

/-- Exact variational characterization of the Euclidean matrix projection. -/
def IsProjection (a s : ℝ) (A P : Matrix ι ι ℝ) : Prop :=
  Feasible a s P ∧ ∀ Y, Feasible a s Y → frobeniusInner (A - P) (Y - P) ≤ 0

theorem projection_conjugate (U A P : Matrix ι ι ℝ)
    (hU : Uᵀ * U = 1) (hU' : U * Uᵀ = 1) {a s : ℝ} (hP : IsProjection a s A P) :
    IsProjection a s (conjugate U A) (conjugate U P) := by
  refine ⟨feasible_conjugate U P hU hU' hP.1, ?_⟩
  intro Y hY
  have hY' := feasible_conjugate Uᵀ Y (by simpa using hU') (by simpa using hU) hY
  have h := hP.2 (conjugate Uᵀ Y) hY'
  have hback : conjugate U (conjugate Uᵀ Y) = Y := by
    simpa only [Matrix.transpose_transpose] using conjugate_inverse Uᵀ Y (by simpa using hU')
  rw [← hback, ← conjugate_sub, ← conjugate_sub, conjugate_inner U _ _ hU]
  exact h

/-- Nonexpansiveness, derived directly from the two projection inequalities. -/
theorem projection_nonexpansive {a s : ℝ} {A B P Q : Matrix ι ι ℝ}
    (hP : IsProjection a s A P) (hQ : IsProjection a s B Q) :
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

theorem projection_distance_le {a s : ℝ} {A P : Matrix ι ι ℝ}
    (hP : IsProjection a s A P) (Y : Matrix ι ι ℝ) (hY : Feasible a s Y) :
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

theorem projection_unique {a s : ℝ} {A P Q : Matrix ι ι ℝ}
    (hP : IsProjection a s A P) (hQ : IsProjection a s A Q) : P = Q := by
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

theorem feasible_diagonal (p : Fin d → ℝ) {a s : ℝ}
    (hp : ∀ i, a ≤ p i) (hs : ∑ i, p i = s) : Feasible a s (Matrix.diagonal p) := by
  refine ⟨Matrix.isSymm_diagonal p, ?_, ?_⟩
  · apply Matrix.le_iff.mpr
    have heq : Matrix.diagonal p - a • (1 : Matrix (Fin d) (Fin d) ℝ) =
        Matrix.diagonal (fun i => p i - a) := by
      ext i j
      by_cases hij : i = j <;> simp [hij]
    rw [heq]
    exact Matrix.PosSemidef.diagonal (fun i => sub_nonneg.mpr (hp i))
  · simpa using hs

theorem feasible_diagonal_entries {a s : ℝ} {Y : Matrix (Fin d) (Fin d) ℝ}
    (hY : Feasible a s Y) : (∀ i, a ≤ Y i i) ∧ (∑ i, Y i i) = s := by
  refine ⟨?_, hY.2.2⟩
  intro i
  have hi := (Matrix.le_iff.mp hY.2.1).2 (Pi.single i 1)
  have hi' : 0 ≤ Y i i - a := by simpa using hi
  linarith

theorem diagonal_projection (z : Fin d → ℝ) (a s : ℝ) (hd : 0 < d)
    (has : (d : ℝ) * a ≤ s) :
    IsProjection a s (Matrix.diagonal z)
      (Matrix.diagonal (KSSimplexProjection.project z a s hd)) := by
  refine ⟨feasible_diagonal _ (KSSimplexProjection.project_floor z a s hd)
    (KSSimplexProjection.project_sum z a s hd has), ?_⟩
  intro Y hY
  have hdY := feasible_diagonal_entries hY
  have h := KSSimplexProjection.project_variational z a s hd has (fun i => Y i i)
    hdY.1 hdY.2
  have heq : frobeniusInner (Matrix.diagonal z - Matrix.diagonal (KSSimplexProjection.project z a s hd))
      (Y - Matrix.diagonal (KSSimplexProjection.project z a s hd)) =
      ∑ i, (z i - KSSimplexProjection.project z a s hd i) *
        (Y i i - KSSimplexProjection.project z a s hd i) := by
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

/-- Existence of an exact projection is proved spectrally only for the specification. -/
theorem exists_projection (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.IsSymm)
    (a s : ℝ) (hd : 0 < d) (has : (d : ℝ) * a ≤ s) : ∃ P, IsProjection a s A P := by
  have hAH : A.IsHermitian := by
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose, star_trivial] using hA
  let U : Matrix (Fin d) (Fin d) ℝ := hAH.eigenvectorUnitary
  have hU : Uᵀ * U = 1 := by
    simpa only [Matrix.conjTranspose, star_trivial] using unitary.coe_star_mul_self hAH.eigenvectorUnitary
  have hU' : U * Uᵀ = 1 := Matrix.mul_eq_one_comm.mp hU
  have hspec : conjugate U (Matrix.diagonal hAH.eigenvalues) = A := by
    simpa only [conjugate, U, Matrix.conjTranspose, star_trivial] using hAH.spectral_theorem.symm
  have hp := projection_conjugate U (Matrix.diagonal hAH.eigenvalues)
    (Matrix.diagonal (KSSimplexProjection.project hAH.eigenvalues a s hd)) hU hU'
    (diagonal_projection hAH.eigenvalues a s hd has)
  rw [hspec] at hp
  exact ⟨_, hp⟩

/-- The exact projection is a specification, not the numerical implementation. -/
def exactProjection (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.IsSymm)
    (a s : ℝ) (hd : 0 < d) (has : (d : ℝ) * a ≤ s) : Matrix (Fin d) (Fin d) ℝ :=
  Classical.choose (exists_projection A hA a s hd has)

theorem exactProjection_isProjection (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.IsSymm)
    (a s : ℝ) (hd : 0 < d) (has : (d : ℝ) * a ≤ s) :
    IsProjection a s A (exactProjection A hA a s hd has) :=
  Classical.choose_spec (exists_projection A hA a s hd has)

theorem exactProjection_minimizes (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.IsSymm)
    (a s : ℝ) (hd : 0 < d) (has : (d : ℝ) * a ≤ s)
    (Y : Matrix (Fin d) (Fin d) ℝ) (hY : Feasible a s Y) :
    KSJacobiStep.frobeniusEnergy (A - exactProjection A hA a s hd has) ≤
      KSJacobiStep.frobeniusEnergy (A - Y) :=
  projection_distance_le (exactProjection_isProjection A hA a s hd has) Y hY

/-- Actual computed matrix projection: finite Jacobi rotations, finite threshold scan,
then multiplication by the computed basis and its transpose. -/
def report (A : Matrix (Fin d) (Fin d) ℝ) (a s : ℝ) (hd : 0 < d) (ν : ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  conjugate (KSJacobiRayleigh.finalBasis A ν)
    (Matrix.diagonal (KSSimplexProjection.project (fun i => KSJacobiRayleigh.finalMatrix A ν i i) a s hd))

/-- Nearby symmetric matrix for which the numerical report is an exact projection. -/
def surrogate (A : Matrix (Fin d) (Fin d) ℝ) (ν : ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  conjugate (KSJacobiRayleigh.finalBasis A ν)
    (KSJacobiRayleigh.diagonalPart (KSJacobiRayleigh.finalMatrix A ν))

theorem report_isProjection_surrogate (A : Matrix (Fin d) (Fin d) ℝ) (a s : ℝ)
    (hd : 0 < d) (has : (d : ℝ) * a ≤ s) (ν : ℝ) :
    IsProjection a s (surrogate A ν) (report A a s hd ν) := by
  exact projection_conjugate (KSJacobiRayleigh.finalBasis A ν) _ _
    (KSJacobiIteration.accumulatedBasis_transpose_mul A _)
    (KSJacobiIteration.accumulatedBasis_mul_transpose A _)
    (diagonal_projection (fun i => KSJacobiRayleigh.finalMatrix A ν i i) a s hd has)

theorem report_feasible (A : Matrix (Fin d) (Fin d) ℝ) (a s : ℝ)
    (hd : 0 < d) (has : (d : ℝ) * a ≤ s) (ν : ℝ) : Feasible a s (report A a s hd ν) :=
  (report_isProjection_surrogate A a s hd has ν).1

theorem report_posSemidef (A : Matrix (Fin d) (Fin d) ℝ) (a s : ℝ)
    (hd : 0 < d) (has : (d : ℝ) * a ≤ s) (ν : ℝ) (ha : 0 ≤ a) :
    (report A a s hd ν).PosSemidef := by
  have h := (Matrix.PosSemidef.one.smul ha).add
    (Matrix.le_iff.mp (report_feasible A a s hd has ν).2.1)
  simpa only [add_sub_cancel] using h

theorem surrogate_error (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.IsSymm)
    {ν : ℝ} (hν : 0 < ν) : KSJacobiStep.frobeniusEnergy (A - surrogate A ν) ≤ ν ^ 2 := by
  let B := KSJacobiRayleigh.finalMatrix A ν
  let U := KSJacobiRayleigh.finalBasis A ν
  have hU : Uᵀ * U = 1 := KSJacobiIteration.accumulatedBasis_transpose_mul A _
  have hU' : U * Uᵀ = 1 := KSJacobiIteration.accumulatedBasis_mul_transpose A _
  have hB : B = Uᵀ * A * U := KSJacobiIteration.run_eq_conjugation A _
  have hback : conjugate U B = A := by
    rw [hB]
    simp only [conjugate, Matrix.mul_assoc, ← Matrix.mul_assoc U Uᵀ,
      hU', Matrix.one_mul, Matrix.mul_one]
  have he : A - surrogate A ν = conjugate U (B - KSJacobiRayleigh.diagonalPart B) := by
    rw [conjugate_sub, hback]
    rfl
  rw [he, conjugate_energy U _ hU, KSJacobiRayleigh.residual_frobeniusEnergy]
  exact KSJacobiIteration.run_energy_accuracy A hA hν

/-- Accuracy against any exact projection, with its existence separately discharged above. -/
theorem report_accuracy_for_projection (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.IsSymm)
    (a s : ℝ) (hd : 0 < d) (has : (d : ℝ) * a ≤ s) {ν : ℝ} (hν : 0 < ν)
    (P : Matrix (Fin d) (Fin d) ℝ) (hP : IsProjection a s A P) :
    Real.sqrt (KSJacobiStep.frobeniusEnergy (report A a s hd ν - P)) ≤ ν := by
  have h := projection_nonexpansive (report_isProjection_surrogate A a s hd has ν) hP
  have he : KSJacobiStep.frobeniusEnergy (surrogate A ν - A) =
      KSJacobiStep.frobeniusEnergy (A - surrogate A ν) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [Matrix.sub_apply]
    ring
  rw [he] at h
  exact (Real.sqrt_le_iff).mpr ⟨hν.le, h.trans (surrogate_error A hA hν)⟩

/-- The actual finite report is within the requested Frobenius tolerance of the exact
Euclidean projection onto symmetric matrices above `a I` with trace `s`. -/
theorem report_accuracy (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.IsSymm)
    (a s : ℝ) (hd : 0 < d) (has : (d : ℝ) * a ≤ s) {ν : ℝ} (hν : 0 < ν) :
    Real.sqrt (KSJacobiStep.frobeniusEnergy
      (report A a s hd ν - exactProjection A hA a s hd has)) ≤ ν :=
  report_accuracy_for_projection A hA a s hd has hν _
    (exactProjection_isProjection A hA a s hd has)

end MatrixSpencer.KSJacobiMatrixProjection
