import MatrixSpencer.MSManuscriptFactoryPolynomialMovementBounds

/-! Direct polynomial reciprocal-square bound for the actual square-MS
numerical mesh at every nested factory config, using the original input
label count and the original signing margin. This is a movement-parameter
bound, not a bound on the full algorithm's operation count.
-/
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.MSManuscriptFactoryPolynomialMesh
open PhaseRestriction MSManuscriptPolynomialMovementBounds
  MSManuscriptFactoryPolynomialMovementBounds
local instance {m : Type*} [Fintype m] [DecidableEq m] :
    CStarAlgebra (Matrix m m ℂ) := {}
set_option maxHeartbeats 800000

variable {ι n : Type*} [Fintype ι] [LinearOrder ι]
  [Fintype n] [DecidableEq n] {d : ℕ} [Nonempty (Fin d)]

/-- The actual mesh is bounded away from zero by an inverse polynomial in
the original label count and physical dimension, with no supplied offset,
derivative budget, or stage-dependent condition-number hypothesis. -/
theorem mesh_inverse_square_le (e : Fin d ≃ n) (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (hN : ∀ i, ‖A i‖ ≤ 1)
    (x : EuclideanSpace ℝ ι)
    (y : MSManuscriptPhase.Point (ι := Live x) (signingEpsilon ι))
    (hl : 32 ≤ Fintype.card (Live y.val)) (hd : 0 < d) :
    1 / (MSManuscriptNumericalEpochRun.mesh
      (MSManuscriptNumericalConfig.ofEpochConfig (cfg e A hA hN x y hl) hd)) ^ 2 ≤
    meshCap (Fintype.card ι) d (Fintype.card ι) (Fintype.card ι) := by
  have hm : (MSManuscriptNumericalConfig.ofEpochConfig (cfg e A hA hN x y hl) hd).margin =
      1 / (1000 * ((Fintype.card ι : ℝ) + 1)) := rfl
  have hb := MSManuscriptPolynomialMovementBounds.mesh_inverse_square_le
    (MSManuscriptNumericalConfig.ofEpochConfig (cfg e A hA hN x y hl) hd)
    rfl rfl rfl (Fintype.card ι) hm
    (Nat.cast_nonneg (Fintype.card ι)) (offset_norm_le e A hA hN x y hl)
  exact hb.trans (meshCap_mono_labels (live_le_original x y)
    (Nat.cast_nonneg (Fintype.card ι)))

end MatrixSpencer.MSManuscriptFactoryPolynomialMesh
