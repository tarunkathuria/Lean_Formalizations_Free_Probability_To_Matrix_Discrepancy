import MatrixSpencer.Sylvester

/-!
# The actual inverse-Sylvester metric

All inverse solutions in this file use the proved Sylvester linear
equivalence.  The variational formula is proved by completing a positive
quadratic square, with the actual inverse solution as its maximizing test.
The cross-Gram estimate below allows different finite output and column
dimensions.
-/

open Matrix MatrixSpencer Set
open scoped BigOperators MatrixOrder ComplexOrder

noncomputable section

namespace HigherRankKS.SylvesterMetric

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m]

/-- The actual inverse linear operator, not left or right multiplication
by the inverse of the weight matrix. -/
def inverse (W : Matrix n n ℂ) (hW : W.PosDef) (R : Matrix n n ℂ) : Matrix n n ℂ :=
  (sylvesterEquiv W hW).symm R

/-- Squared inverse-Sylvester energy in the real trace pairing. -/
def energy (W : Matrix n n ℂ) (hW : W.PosDef) (R : Matrix n n ℂ) : ℝ :=
  realTrace (R * inverse W hW R)

/-- The objective in the quadratic variational formula. -/
def variational (W R Y : Matrix n n ℂ) : ℝ :=
  2 * realTrace (R * Y) - realTrace (Y * sylvester W Y)

@[simp] theorem inverse_solve (W : Matrix n n ℂ) (hW : W.PosDef)
    (R : Matrix n n ℂ) : sylvester W (inverse W hW R) = R :=
  sylvester_inverse_solve W hW R

theorem inverse_isHermitian (W : Matrix n n ℂ) (hW : W.PosDef)
    {R : Matrix n n ℂ} (hR : R.IsHermitian) : (inverse W hW R).IsHermitian :=
  sylvester_inverse_isHermitian W hW hR

omit [DecidableEq n] in
/-- Trace self-adjointness of the Sylvester map; the bilinear trace identity
itself does not require Hermitian arguments. -/
theorem trace_sylvester_selfAdjoint (W X Y : Matrix n n ℂ) :
    realTrace (X * sylvester W Y) = realTrace (sylvester W X * Y) := by
  simp only [sylvester_apply, Matrix.mul_add, Matrix.add_mul, realTrace_add]
  have hcycle : realTrace (X * (Y * W)) = realTrace (W * X * Y) := by
    simpa only [Matrix.mul_assoc] using realTrace_mul_cycle X Y W
  rw [hcycle]
  simp only [Matrix.mul_assoc]
  ring

/-- Self-adjointness of the actual inverse in the real trace pairing. -/
theorem trace_inverse_selfAdjoint (W : Matrix n n ℂ) (hW : W.PosDef)
    (R S : Matrix n n ℂ) :
    realTrace (R * inverse W hW S) = realTrace (S * inverse W hW R) := by
  have h := trace_sylvester_selfAdjoint W (inverse W hW R) (inverse W hW S)
  rw [inverse_solve, inverse_solve] at h
  exact h.symm.trans (realTrace_mul_comm (inverse W hW R) S)

@[simp] theorem inverse_real_smul (W : Matrix n n ℂ) (hW : W.PosDef)
    (r : ℝ) (R : Matrix n n ℂ) : inverse W hW (r • R) = r • inverse W hW R :=
  (((sylvesterEquiv W hW).symm.toLinearMap).restrictScalars ℝ).map_smul r R

/-- The inverse energy is quadratic under real rescaling. -/
theorem energy_real_smul (W : Matrix n n ℂ) (hW : W.PosDef)
    (r : ℝ) (R : Matrix n n ℂ) : energy W hW (r • R) = r ^ 2 * energy W hW R := by
  simp only [energy, inverse_real_smul, smul_mul_assoc, mul_smul_comm, realTrace_smul]
  ring

theorem quadratic_nonneg {W Y : Matrix n n ℂ} (hW : W.PosDef)
    (hY : Y.IsHermitian) : 0 ≤ realTrace (Y * sylvester W Y) := by
  by_cases hz : Y = 0
  · simp [hz]
  · simpa only [hY.eq] using (sylvester_quadratic_pos hW hz).le

theorem energy_nonneg (W : Matrix n n ℂ) (hW : W.PosDef)
    {R : Matrix n n ℂ} (hR : R.IsHermitian) : 0 ≤ energy W hW R := by
  have h := quadratic_nonneg hW (inverse_isHermitian W hW hR)
  rw [inverse_solve] at h
  simpa only [energy, realTrace_mul_comm] using h

theorem energy_pos (W : Matrix n n ℂ) (hW : W.PosDef)
    {R : Matrix n n ℂ} (hR : R.IsHermitian) (hRne : R ≠ 0) :
    0 < energy W hW R := by
  have hne : inverse W hW R ≠ 0 := by
    intro hz
    have hsolve := inverse_solve W hW R
    rw [hz, map_zero] at hsolve
    exact hRne hsolve.symm
  have h := sylvester_quadratic_pos hW hne
  rw [(inverse_isHermitian W hW hR).eq, inverse_solve] at h
  simpa only [energy, realTrace_mul_comm] using h

theorem energy_eq_zero_iff (W : Matrix n n ℂ) (hW : W.PosDef)
    {R : Matrix n n ℂ} (hR : R.IsHermitian) : energy W hW R = 0 ↔ R = 0 := by
  constructor
  · intro he
    by_contra hne
    have hp := energy_pos W hW hR hne
    rw [he] at hp
    exact (lt_irrefl 0) hp
  · rintro rfl
    simp [energy]

/-- Completing the Sylvester quadratic square gives the exact gap from
the value at the inverse solution. -/
theorem energy_sub_variational (W : Matrix n n ℂ) (hW : W.PosDef)
    (R Y : Matrix n n ℂ) :
    energy W hW R - variational W R Y =
      realTrace ((Y - inverse W hW R) * sylvester W (Y - inverse W hW R)) := by
  have hcross := trace_sylvester_selfAdjoint W (inverse W hW R) Y
  rw [inverse_solve] at hcross
  simp only [map_sub, Matrix.sub_mul, Matrix.mul_sub, realTrace_sub, inverse_solve]
  rw [hcross, realTrace_mul_comm Y R, realTrace_mul_comm (inverse W hW R) R]
  unfold energy variational
  ring

/-- Every Hermitian test gives at most the actual inverse energy. -/
theorem variational_le_energy (W : Matrix n n ℂ) (hW : W.PosDef)
    {R Y : Matrix n n ℂ} (hR : R.IsHermitian) (hY : Y.IsHermitian) :
    variational W R Y ≤ energy W hW R := by
  have hn := quadratic_nonneg hW (hY.sub (inverse_isHermitian W hW hR))
  rw [← energy_sub_variational W hW R Y] at hn
  exact sub_nonneg.mp hn

/-- The unique inverse solution attains the variational value. -/
theorem variational_inverse (W : Matrix n n ℂ) (hW : W.PosDef)
    (R : Matrix n n ℂ) : variational W R (inverse W hW R) = energy W hW R := by
  rw [variational, inverse_solve, realTrace_mul_comm (inverse W hW R) R]
  unfold energy
  ring

/-- The variational supremum is an attained maximum at the actual inverse
solution; this formulation avoids any convention for unbounded suprema. -/
theorem variational_isGreatest (W : Matrix n n ℂ) (hW : W.PosDef)
    {R : Matrix n n ℂ} (hR : R.IsHermitian) :
    IsGreatest {v : ℝ | ∃ Y : Matrix n n ℂ, Y.IsHermitian ∧
      variational W R Y = v} (energy W hW R) := by
  refine ⟨⟨inverse W hW R, inverse_isHermitian W hW hR, variational_inverse W hW R⟩, ?_⟩
  rintro _ ⟨Y, hY, rfl⟩
  exact variational_le_energy W hW hR hY

/-- The literal supremum identity, with attainment supplied by the
preceding theorem. -/
theorem energy_eq_sSup_variational (W : Matrix n n ℂ) (hW : W.PosDef)
    {R : Matrix n n ℂ} (hR : R.IsHermitian) :
    energy W hW R = sSup {v : ℝ | ∃ Y : Matrix n n ℂ, Y.IsHermitian ∧
      variational W R Y = v} :=
  (variational_isGreatest W hW hR).csSup_eq.symm

omit [DecidableEq n] in
/-- Exact rectangular completed square underlying the cross-Gram bound.
The real traces on both sides are over the output space. -/
theorem crossGram_completed_square (A B : Matrix n m ℂ)
    {Y : Matrix n n ℂ} (hY : Y.IsHermitian) :
    variational (A * Aᴴ) (A * Bᴴ + B * Aᴴ) Y =
      2 * realTrace (B * Bᴴ) - 2 * realTrace ((Y * A - B) * (Y * A - B)ᴴ) := by
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hY.eq]
  simp only [variational, sylvester_apply, Matrix.add_mul, Matrix.mul_add,
    Matrix.sub_mul, Matrix.mul_sub, realTrace_add, realTrace_sub]
  have hcross := realTrace_mul_comm Y (A * Bᴴ)
  have hquad := realTrace_mul_cycle Y (A * Aᴴ) Y
  simp only [Matrix.mul_assoc] at hcross hquad ⊢
  linarith

omit [DecidableEq n] in
/-- Every Hermitian variational test for a rectangular cross-Gram pair is
bounded by twice the squared Hilbert--Schmidt size of the second factor. -/
theorem crossGram_variational_le (A B : Matrix n m ℂ)
    {Y : Matrix n n ℂ} (hY : Y.IsHermitian) :
    variational (A * Aᴴ) (A * Bᴴ + B * Aᴴ) Y ≤ 2 * realTrace (B * Bᴴ) := by
  rw [crossGram_completed_square A B hY]
  have hnonneg := realTrace_nonneg
    (Matrix.posSemidef_self_mul_conjTranspose (Y * A - B))
  linarith

/-- Finite rectangular cross-Gram inequality for the actual inverse
Sylvester operator.  Positive definiteness is on the output space only. -/
theorem crossGram_energy_le (A B : Matrix n m ℂ) (hW : (A * Aᴴ).PosDef) :
    energy (A * Aᴴ) hW (A * Bᴴ + B * Aᴴ) ≤ 2 * realTrace (B * Bᴴ) := by
  have hR : (A * Bᴴ + B * Aᴴ).IsHermitian := by
    change (A * Bᴴ + B * Aᴴ)ᴴ = A * Bᴴ + B * Aᴴ
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
    exact add_comm _ _
  rw [← variational_inverse (A * Aᴴ) hW (A * Bᴴ + B * Aᴴ)]
  exact crossGram_variational_le A B (inverse_isHermitian (A * Aᴴ) hW hR)

end HigherRankKS.SylvesterMetric
