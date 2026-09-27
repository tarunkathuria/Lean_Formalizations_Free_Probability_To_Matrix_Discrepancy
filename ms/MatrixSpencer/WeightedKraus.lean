import MatrixSpencer.Realignment
import MatrixSpencer.ComplexGram

/-!
# Weighted Kraus realignment bound

This is the weighted realignment estimate in the p=2 two-frame lemma. The
input cap is on the actual real Gram matrix of the Kraus family, and the
conclusion controls the full four-index channel energy.
-/

open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix
open Matrix

noncomputable section

namespace MatrixSpencer

variable {ι m n : Type*} [Fintype ι] [Fintype m] [Fintype n]

/-- The actual real Gram, given a matrix type before any order instance is chosen. -/
def realKrausGram (K : ι → Matrix m n ℂ) : Matrix ι ι ℝ :=
  fun a b => (Matrix.trace ((K a)ᴴ * K b)).re

/-- The physical weighted real Gram. -/
def physicalRealGram (P : Matrix n n ℂ) (D : ι → Matrix n n ℂ) : Matrix ι ι ℝ :=
  fun a b => (Matrix.trace (P * D a * D b)).re

omit [Fintype ι] in
theorem krausGram_entry (K : ι → Matrix m n ℂ) (a b : ι) :
    ((krausSynthesis K)ᴴ * krausSynthesis K) a b = Matrix.trace ((K a)ᴴ * K b) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, krausSynthesis,
    Matrix.trace, Matrix.diag, Fintype.sum_prod_type]
  exact Finset.sum_comm

/-- A real Gram cap supplies the factor-two complex synthesis bound. -/
theorem krausSuper_energy_le_of_realGram_cap
    [DecidableEq ι] [DecidableEq m] [DecidableEq n]
    (K : ι → Matrix m n ℂ) {t : ℝ} (ht : 0 ≤ t)
    (hcap : realKrausGram K ≤ algebraMap ℝ (Matrix ι ι ℝ) t) :
    entryEnergy (krausSuper K) ≤ (2 * t) * ∑ a, entryEnergy (K a) := by
  apply krausSuper_entryEnergy_le
  rw [krausChoi_eq_synthesis_mul_adjoint]
  have hg : ((krausSynthesis K)ᴴ * krausSynthesis K).map Complex.re =
      realKrausGram K := by
    ext a b
    simp only [Matrix.map_apply, krausGram_entry, realKrausGram]
  have h := synthesis_cap_of_realGram_cap (krausSynthesis K) ht (by rw [hg]; exact hcap)
  simpa only [Algebra.algebraMap_eq_smul_one] using h

variable [DecidableEq n]

omit [Fintype ι] in
/-- The weighted complex Gram equals the physical trace Gram exactly. -/
theorem weightedKraus_gram {P : Matrix n n ℂ} (hP : P.PosSemidef)
    (D : ι → Matrix n n ℂ) (hD : ∀ a, (D a).IsHermitian) (a b : ι) :
    Matrix.trace ((D a * CFC.sqrt P)ᴴ * (D b * CFC.sqrt P)) =
      Matrix.trace (P * D a * D b) := by
  have hs : (CFC.sqrt P).IsHermitian := (CFC.sqrt_nonneg P).posSemidef.isHermitian
  rw [Matrix.conjTranspose_mul, hs.eq, (hD a).eq]
  calc
    _ = Matrix.trace (CFC.sqrt P * CFC.sqrt P * D a * D b) := by
      simpa only [Matrix.mul_assoc] using
        Matrix.trace_mul_comm (CFC.sqrt P * D a * D b) (CFC.sqrt P)
    _ = _ := by rw [CFC.sqrt_mul_sqrt_self P hP.nonneg]

/-- The weighted Kraus energies have exactly the trace budget supplied by the fixed point. -/
theorem weightedKraus_energy_sum {P : Matrix n n ℂ} (hP : P.PosSemidef)
    (D : ι → Matrix n n ℂ) (hD : ∀ a, (D a).IsHermitian)
    (hfix : (∑ a, D a * P * D a) = P) :
    (∑ a, entryEnergy (D a * CFC.sqrt P)) = realTrace P := by
  calc
    _ = ∑ a, realTrace (P * D a * D a) := by
      apply Finset.sum_congr rfl
      intro a _
      simp only [entryEnergy_eq_realTrace_adjoint_mul, realTrace, weightedKraus_gram hP D hD]
    _ = realTrace (P * ∑ a, D a * D a) := by
      simp only [Matrix.mul_sum, realTrace, Matrix.trace_sum, map_sum, Matrix.mul_assoc]
    _ = realTrace (∑ a, D a * P * D a) := (realTrace_kraus_sum D P).symm
    _ = _ := by rw [hfix]

/-- The weighted realignment inequality with all physical hypotheses discharged. -/
theorem weightedKraus_realignment_bound [DecidableEq ι]
    {P : Matrix n n ℂ} (hP : P.PosSemidef)
    (D : ι → Matrix n n ℂ) (hD : ∀ a, (D a).IsHermitian)
    (hfix : (∑ a, D a * P * D a) = P) {t : ℝ} (ht : 0 ≤ t)
    (hcap : physicalRealGram P D ≤ algebraMap ℝ (Matrix ι ι ℝ) t) :
    entryEnergy (krausSuper (fun a => D a * CFC.sqrt P)) ≤ (2 * t) * realTrace P := by
  have hg : realKrausGram (fun a => D a * CFC.sqrt P) = physicalRealGram P D := by
    ext a b
    simp only [realKrausGram, physicalRealGram, weightedKraus_gram hP D hD]
  have h := krausSuper_energy_le_of_realGram_cap (fun a => D a * CFC.sqrt P) ht
    (by rw [hg]; exact hcap)
  rwa [weightedKraus_energy_sum hP D hD hfix] at h

end MatrixSpencer
