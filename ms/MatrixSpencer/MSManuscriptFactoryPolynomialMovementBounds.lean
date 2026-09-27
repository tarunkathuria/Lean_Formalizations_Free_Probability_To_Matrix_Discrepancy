import MatrixSpencer.MSManuscriptOriginalOffsetBounds
import MatrixSpencer.MSManuscriptPolynomialMovementBounds

/-! Input-only polynomial movement bounds for every actual nested square-MS
numerical epoch. The global rounding margin and original frozen-label offset
are substituted, rather than supplied as analytic budget hypotheses.
This does not count numerical preparation, cleanup, or a complete execution.
-/
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.MSManuscriptFactoryPolynomialMovementBounds
open PhaseRestriction MSManuscriptMatrixReindex MSManuscriptPolynomialMovementBounds
local instance {m : Type*} [Fintype m] [DecidableEq m] :
    CStarAlgebra (Matrix m m ℂ) := {}
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

lemma uniform_mono_inputs {N M d : ℕ} (hNM : N ≤ M) {R S : ℝ}
    (hR : 0 ≤ R) (hRS : R ≤ S) : uniform N d R ≤ uniform M d S := by
  have hN : (N : ℝ) ≤ M := Nat.cast_le.mpr hNM
  have hS : 0 ≤ S := hR.trans hRS
  unfold uniform fourth joint value inverseFloor denominator direction
  gcongr <;> positivity

lemma meshCap_mono_labels {N L M d : ℕ} (hNL : N ≤ L) {B : ℝ}
    (hB : 0 ≤ B) : meshCap N d M B ≤ meshCap L d M B := by
  have hN : (N : ℝ) ≤ L := Nat.cast_le.mpr hNL
  have hu := uniform_mono_inputs (d := d) hNL
    (by positivity : 0 ≤ 1 + ((d : ℝ) + 1) * B + (N : ℝ))
    (show 1 + ((d : ℝ) + 1) * B + (N : ℝ) ≤
      1 + ((d : ℝ) + 1) * B + (L : ℝ) by linarith)
  unfold meshCap
  gcongr

variable {ι n : Type*} [Fintype ι] [LinearOrder ι]
  [Fintype n] [DecidableEq n] {d : ℕ} [Nonempty (Fin d)]

/-- Exact config passed to the numerical epoch by the nested provider and
factory, with the signing algorithm's original global margin. -/
def cfg (e : Fin d ≃ n) (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (hN : ∀ i, ‖A i‖ ≤ 1)
    (x : EuclideanSpace ℝ ι)
    (y : MSManuscriptPhase.Point (ι := Live x) (signingEpsilon ι))
    (hl : 32 ≤ Fintype.card (Live y.val)) :=
  MSManuscriptNumericalEpochFactory.cfg
    (selfAdjointReindex e (restrictedOffset 0 A hA x))
    (fun i : Live x => (A i).submatrix e e) (fun i => (hA i).submatrix e)
    (fun i => reindex_contraction e (hN i)) (signingEpsilon ι) signingEpsilon_pos
    ((mul_le_mul_of_nonneg_right
      (show (Fintype.card (Live x) : ℝ) ≤ Fintype.card ι by
        exact_mod_cast Fintype.card_subtype_le (fun i => i ∉ frozenCoordinates x))
      signingEpsilon_pos.le).trans signingEpsilon_count_small) y hl

variable (e : Fin d ≃ n) (A : ι → Matrix n n ℂ)
  (hA : ∀ i, (A i).IsHermitian) (hN : ∀ i, ‖A i‖ ≤ 1)
  (x : EuclideanSpace ℝ ι)
  (y : MSManuscriptPhase.Point (ι := Live x) (signingEpsilon ι))
  (hl : 32 ≤ Fintype.card (Live y.val))

theorem offset_norm_le :
    ‖((cfg e A hA hN x y hl).offset : Matrix (Fin d) (Fin d) ℂ)‖ ≤
      Fintype.card ι :=
  MSManuscriptOriginalOffsetBounds.factory_cfg_offset_norm_le e A hA hN x
    (signingEpsilon ι) signingEpsilon_pos _ y hl

theorem live_le_original : Fintype.card (Live y.val) ≤ Fintype.card ι :=
  (Fintype.card_subtype_le _).trans (Fintype.card_subtype_le _)

/-- Fixed-degree polynomial in the original label count and physical
dimension, valid for every actual nested numerical epoch. -/
theorem fourthBudget_le (hd : 0 < d) :
    MSManuscriptNumericalWalkBudget.fourthBudget
      (MSManuscriptNumericalConfig.ofEpochConfig (cfg e A hA hN x y hl) hd) ≤
    uniform (Fintype.card ι) d
      (1 + ((d : ℝ) + 1) * Fintype.card ι + Fintype.card ι) := by
  have hb := ofEpochConfig_fourthBudget_le (cfg e A hA hN x y hl) hd
    (Nat.cast_nonneg (Fintype.card ι)) (offset_norm_le e A hA hN x y hl)
  exact hb.trans (uniform_mono_inputs (live_le_original x y) (by positivity)
    (by exact add_le_add_left (Nat.cast_le.mpr (live_le_original x y)) _))

/-- Polynomial bound for the original floor-based epoch iteration count,
with no offset or derivative-budget premise. -/
theorem count_le (hd : 0 < d) :
    (MSManuscriptNumericalEpochRun.count
      (MSManuscriptNumericalConfig.ofEpochConfig (cfg e A hA hN x y hl) hd) : ℝ) ≤
    meshCap (Fintype.card ι) d (Fintype.card ι) (Fintype.card ι) + 1 := by
  have hm : (cfg e A hA hN x y hl).epsilon = signingEpsilon (Fin (Fintype.card ι)) := by
    simp only [cfg, MSManuscriptNumericalEpochFactory.cfg,
      MSManuscriptNumericalEpochFactory.reindexConfig, epochConfig,
      signingEpsilon, Fintype.card_fin]
  have hb := ofEpochConfig_count_le (cfg e A hA hN x y hl) hd (Fintype.card ι) hm
    (Nat.cast_nonneg (Fintype.card ι)) (offset_norm_le e A hA hN x y hl)
  exact hb.trans (add_le_add_right (meshCap_mono_labels (live_le_original x y)
    (Nat.cast_nonneg (Fintype.card ι))) 1)

end MatrixSpencer.MSManuscriptFactoryPolynomialMovementBounds
