import MatrixSpencer.KSFullManuscriptSDPCoordinateInverse
import MatrixSpencer.KSFullManuscriptBlockBounds
import MatrixSpencer.KSFullManuscriptCenterData
import MatrixSpencer.KSObjectiveValueBound

/-!
# Explicit outer bounds for the finite-entry SDP coordinates

A PSD block bounds each off-diagonal-block entry even when its diagonal blocks
are singular. Reading real and imaginary entries then bounds every actual
coordinate. The resulting radius is conservative and polynomial in the
number of coordinates and the supplied source cap.
-/

open Matrix
open scoped BigOperators InnerProductSpace MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSFullManuscriptCoordinateBounds

open KSFullManuscriptSDPCoordinates KSFullManuscriptAffineData KSFullManuscriptSDPIdentity
open KSFullManuscriptBlockBounds KSFullManuscriptCenterData
variable {n : Type*} [Fintype n] [LinearOrder n]

omit [Fintype n] in
theorem hermitian_encode_bound (A : Matrix n n ℂ) {R : ℝ}
    (hA : ∀ i j, ‖A i j‖ ≤ R) (p : n × n) :
    |KSFullManuscriptHermitianCoordinates.encode A p| ≤ R := by
  unfold KSFullManuscriptHermitianCoordinates.encode
  split
  · exact (Complex.abs_re_le_norm _).trans (hA _ _)
  · exact (Complex.abs_im_le_norm _).trans (hA _ _)

omit [Fintype n] in
theorem encode_bound (a : n) (S₀ Y₀ S Y : selfAdjoint (Matrix n n ℂ)) (Z : Matrix n n ℂ)
    {q : ℝ} (hq : 0 ≤ q)
    (hS : ∀ i j, ‖((S : Matrix n n ℂ) - S₀) i j‖ ≤ 2)
    (hY : ∀ i j, ‖((Y : Matrix n n ℂ) - Y₀) i j‖ ≤ 2)
    (hZ : ∀ i j, ‖Z i j‖ ≤ q) (p : Index a) :
    |encode a S₀ Y₀ S Y Z p| ≤ 2 + q := by
  rcases p with ((p | p) | (p | p))
  · exact (hermitian_encode_bound _ hS p.val).trans (by linarith)
  · exact (hermitian_encode_bound _ hY p).trans (by linarith)
  · exact ((Complex.abs_re_le_norm _).trans (hZ p.1 p.2)).trans (by linarith)
  · exact ((Complex.abs_im_le_norm _).trans (hZ p.1 p.2)).trans (by linarith)

theorem norm_le_card_mul {ℓ : ℕ} (x : EuclideanSpace ℝ (Fin ℓ)) {R : ℝ}
    (hR : 0 ≤ R) (hx : ∀ i, |x i| ≤ R) : ‖x‖ ≤ ((ℓ : ℝ) + 1) * R := by
  have hs : ‖x‖ ^ 2 ≤ (ℓ : ℝ) * R ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc
      ∑ i, ‖x i‖ ^ 2 ≤ ∑ _i : Fin ℓ, R ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        exact pow_le_pow_left₀ (norm_nonneg _) (by simpa only [Real.norm_eq_abs] using hx i) 2
      _ = _ := by simp
  have hsq : (ℓ : ℝ) * R ^ 2 ≤ (((ℓ : ℝ) + 1) * R) ^ 2 := by
    have hn : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg _
    nlinarith [sq_nonneg (ℓ : ℝ), sq_nonneg R, mul_nonneg (sq_nonneg (ℓ : ℝ)) (sq_nonneg R)]
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by positivity) hR)).mp (hs.trans hsq)

theorem coordinate_norm_le (a : n) (S₀ Y₀ : selfAdjoint (Matrix n n ℂ)) (x : Space a)
    {V : ℝ}
    (hS₀ : ∀ i j, ‖(S₀ : Matrix n n ℂ) i j‖ ≤ 1)
    (hY₀ : ∀ i j, ‖(Y₀ : Matrix n n ℂ) i j‖ ≤ 1)
    (hS : (density a S₀ (entries a x) : Matrix n n ℂ) ∈ densitySet)
    (hY : (Matrix.fromBlocks (density a S₀ (entries a x) : Matrix n n ℂ)
      (regularizer a Y₀ (entries a x) : Matrix n n ℂ)
      (regularizer a Y₀ (entries a x) : Matrix n n ℂ) 1).PosSemidef)
    (hZ : ∀ i j, ‖fidelityLinear a (entries a x) i j‖ ≤ Real.sqrt V) :
    ‖x‖ ≤ ((dimension a : ℝ) + 1) * (2 + Real.sqrt V) := by
  let S := density a S₀ (entries a x)
  let Y := regularizer a Y₀ (entries a x)
  let Z := fidelityLinear a (entries a x)
  have hYblock : (Matrix.fromBlocks (S : Matrix n n ℂ) (Y : Matrix n n ℂ) (Y : Matrix n n ℂ)ᴴ 1).PosSemidef := by
    have hYherm : (Y : Matrix n n ℂ).IsHermitian := Y.property
    simpa only [hYherm.eq] using hY
  have hYentry (i j : n) : ‖(Y : Matrix n n ℂ) i j‖ ≤ 1 := by
    have hh := block_entry_le hYblock hS.2 (show (1 : Matrix n n ℂ) ≤ (1 : ℝ) • 1 by simp) i j
    simpa using hh
  have hSentry (i j : n) : ‖(S : Matrix n n ℂ) i j‖ ≤ 1 :=
    (KSObjectiveValueBound.entry_norm_le _ i j).trans (density_norm_le_one hS)
  have hsDiff (i j : n) : ‖((S : Matrix n n ℂ) - S₀) i j‖ ≤ 2 := by
    exact (norm_sub_le _ _).trans (by linarith [hSentry i j, hS₀ i j])
  have hyDiff (i j : n) : ‖((Y : Matrix n n ℂ) - Y₀) i j‖ ≤ 2 := by
    exact (norm_sub_le _ _).trans (by linarith [hYentry i j, hY₀ i j])
  have he := KSFullManuscriptSDPCoordinateInverse.encode_decode a S₀ Y₀ (entries a x)
  apply norm_le_card_mul x (by positivity)
  intro i
  have hh := encode_bound a S₀ Y₀ S Y Z (Real.sqrt_nonneg V) hsDiff hyDiff hZ
    ((KSCanonicalSDPIndex.chart a).symm i)
  change |encode a S₀ Y₀ (density a S₀ (entries a x)) (regularizer a Y₀ (entries a x))
      (fidelityLinear a (entries a x)) ((KSCanonicalSDPIndex.chart a).symm i)| ≤ _ at hh
  rw [he] at hh
  change |x ((KSCanonicalSDPIndex.chart a) ((KSCanonicalSDPIndex.chart a).symm i))| ≤ _ at hh
  have hidx := (KSCanonicalSDPIndex.chart a).apply_symm_apply i
  rw [hidx] at hh
  exact hh

variable {d : ℕ}

theorem densityCenter_entry_le (hd : 0 < d) (i j : Fin d) :
    ‖(densityCenter hd : Matrix (Fin d) (Fin d) ℂ) i j‖ ≤ 1 := by
  apply (KSObjectiveValueBound.entry_norm_le _ i j).trans
  apply density_norm_le_one
  exact ⟨(KSFullManuscriptStrictFeasible.density_posDef hd).posSemidef,
    KSFullManuscriptStrictFeasible.density_trace hd⟩

theorem rootCenter_entry_le (hd : 0 < d) (i j : Fin d) :
    ‖(rootCenter hd : Matrix (Fin d) (Fin d) ℂ) i j‖ ≤ 1 := by
  have hn : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hs : 1 ≤ Real.sqrt (d : ℝ) := (Real.le_sqrt (by norm_num) (by positivity)).mpr (by simpa using hn)
  have hq : 1 / (2 * Real.sqrt (d : ℝ)) ≤ (1 : ℝ) := by
    apply (div_le_one (by positivity : 0 < 2 * Real.sqrt (d : ℝ))).mpr
    linarith
  by_cases hij : i = j
  · subst j
    change ‖((1 / (2 * Real.sqrt (d : ℝ))) • (1 : Matrix (Fin d) (Fin d) ℂ)) i i‖ ≤ 1
    rw [Matrix.smul_apply, Matrix.one_apply_eq]
    simpa only [norm_smul, norm_one, mul_one, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ 1 / (2 * Real.sqrt (d : ℝ)))] using hq
  · simp [rootCenter, KSFullManuscriptStrictFeasible.rootCenter, hij]

def outerRadius (a : Fin d) (V : ℝ) : ℝ := ((dimension a : ℝ) + 1) * (2 + Real.sqrt V)

theorem outerRadius_pos (a : Fin d) (V : ℝ) : 0 < outerRadius a V := by
  unfold outerRadius
  positivity

end MatrixSpencer.KSFullManuscriptCoordinateBounds
