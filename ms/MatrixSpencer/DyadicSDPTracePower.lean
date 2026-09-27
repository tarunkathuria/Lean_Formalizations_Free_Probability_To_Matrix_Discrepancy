import MatrixSpencer.DyadicRoot
import MatrixSpencer.SpectralCutoff
import MatrixSpencer.KSFullManuscriptBlockBounds
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-! Exact semidefinite representation of the dyadic trace power.  The proof
uses scalar compressions in an eigenbasis and therefore includes singular
positive semidefinite matrices. -/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.DyadicSDPTracePower
variable {n : Type*} [Fintype n] [DecidableEq n]
local instance : CStarAlgebra (Matrix n n ℂ) := {}
open SpectralCutoff

/-- The repeated geometric-mean block constraints. -/
def Chain (S : Matrix n n ℂ) (m : ℕ) (X : Fin (m+1) → Matrix n n ℂ) : Prop :=
  X 0 = 1 ∧ ∀ j : Fin m, (X j.succ).PosSemidef ∧
    (Matrix.fromBlocks S (X j.succ) (X j.succ) (X j.castSucc)).PosSemidef

/-- `S^(1-2^(-m))`, expressed using the verified positive dyadic root. -/
def power (m : ℕ) (S : Matrix n n ℂ) : Matrix n n ℂ :=
  dyadicRoot m S ^ (2^m-1)

def canonical (S : Matrix n n ℂ) (m : ℕ) : Fin (m+1) → Matrix n n ℂ :=
  fun j => power j.val S

@[simp] theorem canonical_last (S : Matrix n n ℂ) (m : ℕ) :
    canonical S m (Fin.last m) = power m S := rfl

private def scalarRoot : ℕ → ℝ → ℝ
  | 0, t => t
  | m+1, t => Real.sqrt (scalarRoot m t)
private def scalarPower (m : ℕ) (t : ℝ) : ℝ := scalarRoot m t ^ (2^m-1)

private theorem scalarRoot_nonneg (m : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ scalarRoot m t := by cases m <;> simp_all [scalarRoot, Real.sqrt_nonneg]

private theorem scalarRoot_square (m : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    scalarRoot (m+1) t ^ 2 = scalarRoot m t := by
  exact Real.sq_sqrt (scalarRoot_nonneg m ht)

private theorem scalarRoot_pow (m : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    scalarRoot m t ^ (2^m) = t := by
  induction m with
  | zero => simp [scalarRoot]
  | succ m ih =>
    rw [Nat.pow_succ, Nat.mul_comm (2^m) 2, pow_mul, scalarRoot_square m ht, ih]

private theorem scalarPower_nonneg (m : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ scalarPower m t := pow_nonneg (scalarRoot_nonneg m ht) _

private theorem scalarPower_zero (t : ℝ) : scalarPower 0 t = 1 := by
  simp [scalarPower]

private theorem scalarPower_square (m : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    scalarPower (m+1) t ^ 2 = t * scalarPower m t := by
  unfold scalarPower
  have he : (2^(m+1)-1)*2 = 2^(m+1)+2*(2^m-1) := by
    have hp : 0 < 2^m := pow_pos (by omega) m
    rw [Nat.pow_succ]
    omega
  calc
    _ = scalarRoot (m+1) t ^ ((2^(m+1)-1)*2) := (pow_mul _ _ _).symm
    _ = scalarRoot (m+1) t ^ (2^(m+1)) *
        (scalarRoot (m+1) t ^ 2) ^ (2^m-1) := by
      rw [← pow_mul, ← pow_add, he]
    _ = _ := by rw [scalarRoot_pow (m+1) ht, scalarRoot_square m ht]

private theorem spectralMatrix_pow {S : Matrix n n ℂ} (hS : S.IsHermitian)
    (f : n → ℝ) (k : ℕ) :
    spectralMatrix hS f ^ k = spectralMatrix hS (fun i => f i ^ k) := by
  induction k with
  | zero => simpa using (spectralMatrix_one hS).symm
  | succ k ih => rw [pow_succ, ih, spectralMatrix_mul]; rfl

private theorem spectralMatrix_sqrt {S : Matrix n n ℂ} (hS : S.IsHermitian)
    (f : n → ℝ) (hf : ∀ i, 0 ≤ f i) :
    CFC.sqrt (spectralMatrix hS f) = spectralMatrix hS (fun i => Real.sqrt (f i)) := by
  apply CFC.sqrt_unique
  · rw [spectralMatrix_mul]
    congr 1
    funext i
    exact Real.mul_self_sqrt (hf i)
  · exact (spectralMatrix_posSemidef hS (fun i => Real.sqrt_nonneg (f i))).nonneg

private theorem root_spectral (m : ℕ) {S : Matrix n n ℂ} (hS : S.PosSemidef) :
    dyadicRoot m S = spectralMatrix hS.isHermitian
      (fun i => scalarRoot m (hS.isHermitian.eigenvalues i)) := by
  induction m with
  | zero => exact (spectralMatrix_eigenvalues hS.isHermitian).symm
  | succ m ih =>
    rw [dyadicRoot_succ, ih, spectralMatrix_sqrt _ _
      (fun i => scalarRoot_nonneg m (hS.eigenvalues_nonneg i))]
    rfl

private theorem power_spectral (m : ℕ) {S : Matrix n n ℂ} (hS : S.PosSemidef) :
    power m S = spectralMatrix hS.isHermitian
      (fun i => scalarPower m (hS.isHermitian.eigenvalues i)) := by
  rw [power, root_spectral m hS, spectralMatrix_pow]
  rfl

@[simp] theorem power_zero (S : Matrix n n ℂ) : power 0 S = 1 := by simp [power]

theorem power_posSemidef (m : ℕ) {S : Matrix n n ℂ} (hS : S.PosSemidef) :
    (power m S).PosSemidef := (dyadicRoot_posSemidef m hS).pow _

private theorem scalarPower_factor (m : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    Real.sqrt t * Real.sqrt (scalarPower m t) = scalarPower (m+1) t := by
  have ha := Real.sqrt_nonneg t
  have hb := Real.sqrt_nonneg (scalarPower m t)
  have hc := scalarPower_nonneg (m+1) ht
  have he : (Real.sqrt t * Real.sqrt (scalarPower m t))^2 = scalarPower (m+1) t ^ 2 := by
    rw [mul_pow, Real.sq_sqrt ht, Real.sq_sqrt (scalarPower_nonneg m ht), scalarPower_square m ht]
  nlinarith [mul_nonneg ha hb]

private theorem power_block (m : ℕ) {S : Matrix n n ℂ} (hS : S.PosSemidef) :
    (Matrix.fromBlocks S (power (m+1) S) (power (m+1) S) (power m S)).PosSemidef := by
  let A := spectralMatrix hS.isHermitian (fun i => Real.sqrt (hS.isHermitian.eigenvalues i))
  let B := spectralMatrix hS.isHermitian (fun i => Real.sqrt (scalarPower m (hS.isHermitian.eigenvalues i)))
  have hA : A.IsHermitian := spectralMatrix_hermitian _ _
  have hB : B.IsHermitian := spectralMatrix_hermitian _ _
  have hAA : A*A=S := by
    dsimp [A]
    rw [spectralMatrix_mul]
    calc
      _ = spectralMatrix hS.isHermitian hS.isHermitian.eigenvalues := by
        congr 1
        funext i
        exact Real.mul_self_sqrt (hS.eigenvalues_nonneg i)
      _ = S := spectralMatrix_eigenvalues hS.isHermitian
  have hBB : B*B=power m S := by
    dsimp [B]
    rw [spectralMatrix_mul, power_spectral m hS]
    congr 1
    funext i
    exact Real.mul_self_sqrt (scalarPower_nonneg m (hS.eigenvalues_nonneg i))
  have hAB : A*B=power (m+1) S := by
    dsimp [A, B]
    rw [spectralMatrix_mul, power_spectral (m+1) hS]
    congr 1
    funext i
    exact scalarPower_factor m (hS.eigenvalues_nonneg i)
  have hBA : B*A=power (m+1) S := by
    have he := congrArg Matrix.conjTranspose hAB
    simpa [Matrix.conjTranspose_mul, hA.eq, hB.eq, (power_posSemidef (m+1) hS).isHermitian.eq] using he
  have hh := Matrix.posSemidef_self_mul_conjTranspose (Matrix.fromRows A B)
  simpa only [Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
    Matrix.fromRows_mul_fromCols, hA.eq, hB.eq, hAA, hBB, hAB, hBA] using hh

theorem canonical_chain {S : Matrix n n ℂ} (hS : S.PosSemidef) (m : ℕ) :
    Chain S m (canonical S m) := by
  refine ⟨power_zero S, fun j => ⟨power_posSemidef (j.val+1) hS, ?_⟩⟩
  exact power_block j.val hS

private theorem chain_conjugate {S : Matrix n n ℂ} {m : ℕ}
    {X : Fin (m+1) → Matrix n n ℂ} (hX : Chain S m X)
    (U : Matrix n n ℂ) (hU : Uᴴ*U=1) :
    Chain (Uᴴ*S*U) m (fun j => Uᴴ*X j*U) := by
  refine ⟨by change Uᴴ * X 0 * U = 1; rw [hX.1, Matrix.mul_one, hU], fun j => ?_⟩
  refine ⟨(hX.2 j).1.conjTranspose_mul_mul_same U, ?_⟩
  have hh := (hX.2 j).2.conjTranspose_mul_mul_same (Matrix.fromBlocks U 0 0 U)
  simpa only [Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
    Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    Matrix.mul_assoc] using hh

private theorem chain_diagonal_bound {t : n → ℝ} (ht : ∀ i, 0 ≤ t i)
    {m : ℕ} {X : Fin (m+1) → Matrix n n ℂ}
    (hX : Chain (Matrix.diagonal (fun i => (t i : ℂ))) m X) :
    ∀ k (hk : k ≤ m) (i : n), (X ⟨k, by omega⟩ i i).re ≤ scalarPower k (t i) := by
  intro k
  induction k with
  | zero =>
    intro hk i
    have he : X ⟨0, by omega⟩ = 1 := hX.1
    rw [he, scalarPower_zero]
    simp
  | succ k ih =>
    intro hk i
    have hp := ih (by omega) i
    have hb := (hX.2 ⟨k, by omega⟩).2
    have he := KSFullManuscriptBlockBounds.entry_sq_le_diagonal hb (Sum.inl i) (Sum.inr i)
    simp only [Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₂₂, Matrix.diagonal_apply_eq, Complex.ofReal_re] at he
    have hr := Complex.sq_norm_sub_sq_re (X ⟨k+1, by omega⟩ i i)
    have hm := mul_le_mul_of_nonneg_left hp (ht i)
    have hc := scalarPower_nonneg (k+1) (ht i)
    have hs := scalarPower_square k (ht i)
    change ‖X ⟨k+1, by omega⟩ i i‖^2 ≤ t i * (X ⟨k, by omega⟩ i i).re at he
    nlinarith [sq_nonneg (X ⟨k+1, by omega⟩ i i).im]

/-- Every feasible block chain is bounded by the exact dyadic trace power. -/
theorem chain_trace_le {S : Matrix n n ℂ} (hS : S.PosSemidef) {m : ℕ}
    {X : Fin (m+1) → Matrix n n ℂ} (hX : Chain S m X) :
    realTrace (X (Fin.last m)) ≤ realTrace (power m S) := by
  let U : Matrix n n ℂ := hS.isHermitian.eigenvectorUnitary
  have hU : Uᴴ*U=1 := unitary.coe_star_mul_self hS.isHermitian.eigenvectorUnitary
  have hU' : U*Uᴴ=1 := unitary.coe_mul_star_self hS.isHermitian.eigenvectorUnitary
  have hd : Uᴴ*S*U = Matrix.diagonal (fun i => (hS.isHermitian.eigenvalues i : ℂ)) := by
    exact hS.isHermitian.star_mul_self_mul_eq_diagonal
  have hY := chain_conjugate hX U hU
  rw [hd] at hY
  have hb := chain_diagonal_bound (fun i => hS.eigenvalues_nonneg i) hY m le_rfl
  have ht : realTrace (Uᴴ*X (Fin.last m)*U) = realTrace (X (Fin.last m)) := by
    rw [realTrace_mul_cycle, hU', Matrix.one_mul]
  rw [← ht, power_spectral m hS, spectralMatrix_trace]
  simp only [realTrace, Matrix.trace, Matrix.diag, map_sum]
  change (∑ i, ((Uᴴ*X (Fin.last m)*U) i i).re) ≤ _
  exact Finset.sum_le_sum (fun i _ => hb i)

end MatrixSpencer.DyadicSDPTracePower
