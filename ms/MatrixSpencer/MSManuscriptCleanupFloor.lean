import MatrixSpencer.MSManuscriptSchurCleanup
import MatrixSpencer.MSManuscriptEntryFloor

/-! The retained block of the finite Schur scan has a certified positive floor.
All retained coordinates are selected by comparison with the original diagonal. -/
open Matrix
open scoped BigOperators MatrixOrder
noncomputable section
namespace MatrixSpencer.MSManuscriptCleanupFloor
open MSManuscriptSchurCleanup MSManuscriptCleanupParameters
variable {d : ℕ}

abbrev High (G : Matrix (Fin d) (Fin d) ℝ) (δ : ℝ) := {a : Fin d // 3*δ ≤ G a a}

def reduced (G : Matrix (Fin d) (Fin d) ℝ) (δ : ℝ) : Matrix (High G δ) (High G δ) ℝ :=
  (runScan G δ d).submatrix Subtype.val Subtype.val

theorem reduced_posSemidef (G : Matrix (Fin d) (Fin d) ℝ) (hG : G.PosSemidef) (δ : ℝ) :
    (reduced G δ).PosSemidef := (runScan_posSemidef G hG δ d).submatrix _

theorem reduced_floor (G : Matrix (Fin d) (Fin d) ℝ) (hG : G.PosSemidef)
    {δ : ℝ} (hδ : 0 < δ) (hdiag : ∀ a, δ ≤ G a a)
    (hoff : ∀ a b, a ≠ b → |G a b| ≤ tolerance d δ) :
    (2*δ) • (1 : Matrix (High G δ) (High G δ) ℝ) ≤ reduced G δ := by
  classical
  have hb := runScan_bounds G hG hδ hdiag hoff d le_rfl
  have htol := tolerance_pos d hδ
  have hloss := total_entryLoss_le d hδ
  have hr := row_bound d hδ
  have hsym : (reduced G δ).IsSymm := by
    ext i j
    simpa using congrFun (congrFun (reduced_posSemidef G hG δ).isHermitian.eq i) j
  have hfloor := MSManuscriptEntryFloor.floor_of_entries (reduced G δ) hsym
    (a := 3*δ-(d:ℝ)*entryLoss d δ) (e := 2*tolerance d δ) (by positivity)
    (fun a => by
      have ha : ¬Removed G δ d a.val := fun h => (not_lt_of_ge a.property) h.2
      have hh := hb.diagonal a.val ha
      change 3*δ-(d:ℝ)*entryLoss d δ ≤ runScan G δ d a.val a.val
      linarith [a.property])
    (fun a b hab => by
      have hab' : a.val ≠ b.val := fun h => hab (Subtype.ext h)
      have hh := hb.offDiagonal a.val b.val hab'
      change |runScan G δ d a.val b.val| ≤ 2*tolerance d δ
      linarith)
  have hc : (Fintype.card (High G δ):ℝ) ≤ d := by
    have h : Fintype.card (High G δ) ≤ d := by
      simpa using (Fintype.card_subtype_le (fun a : Fin d => 3*δ ≤ G a a))
    exact_mod_cast h
  have hcoef : 2*δ ≤ 3*δ-(d:ℝ)*entryLoss d δ-(Fintype.card (High G δ):ℝ)*(2*tolerance d δ) := by
    have hm := mul_le_mul_of_nonneg_right hc (show 0≤2*tolerance d δ by positivity)
    nlinarith
  apply le_trans ?_ hfloor
  apply Matrix.le_iff.mpr
  have hp := (Matrix.PosSemidef.one : (1 : Matrix (High G δ) (High G δ) ℝ).PosSemidef).smul (sub_nonneg.mpr hcoef)
  convert hp using 1
  module

theorem final_zero_of_low (G : Matrix (Fin d) (Fin d) ℝ) (hG : G.PosSemidef)
    (δ : ℝ) (a : Fin d) (ha : G a a < 3*δ) (b : Fin d) :
    runScan G δ d b a = 0 := by
  have h := congrFun (runScan_zero_column G hG δ d a ⟨a.isLt,ha⟩) b
  exact h

end MatrixSpencer.MSManuscriptCleanupFloor
