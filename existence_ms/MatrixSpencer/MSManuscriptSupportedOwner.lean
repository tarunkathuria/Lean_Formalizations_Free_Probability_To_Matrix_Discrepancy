import MatrixSpencer.MSManuscriptCleanupCoordinates

/-!
# Stored finite support frames for numerical covariance preparation

The owner data retain a real rectangular frame and its reduced matrix. Cleanup
updates both using the finite Jacobi/Schur computation and ordered label scan.
A paid cut keeps that frame. The invariant supplies no spectral choice.
-/
open Matrix
open scoped BigOperators MatrixOrder
noncomputable section
namespace MatrixSpencer.MSManuscriptSupportedOwner
open MSManuscriptPaidStep
variable {N : ℕ}

structure Owner (N : ℕ) where
  dim : ℕ
  frame : Matrix (Fin N) (Fin dim) ℝ
  matrix : Matrix (Fin dim) (Fin dim) ℝ

def Owner.physical (O : Owner N) : Matrix (Fin N) (Fin N) ℝ := O.frame*O.matrix*O.frameᵀ

def Owner.Valid (O : Owner N) (δ : ℝ) : Prop :=
  O.frameᵀ*O.frame=1 ∧ δ • (1 : Matrix (Fin O.dim) (Fin O.dim) ℝ) ≤ O.matrix

/-- Actual finite cleanup: only the computed retained frame and matrix are stored. -/
def clean (O : Owner N) (δ : ℝ) : Owner N where
  dim := MSManuscriptCleanupCoordinates.count O.matrix δ
  frame := O.frame*MSManuscriptCleanupCoordinates.frame O.matrix δ
  matrix := MSManuscriptCleanupCoordinates.matrix O.matrix δ

/-- The local paid cut is exact scalar arithmetic; its direction is supplied by
an actual response routine, whose accuracy is proved separately. -/
def paid (O : Owner N) (α : ℝ) (u : Fin O.dim → ℝ) : Owner N where
  dim := O.dim
  frame := O.frame
  matrix := cut O.matrix α u

private theorem real_conjTranspose {m n : ℕ} (U : Matrix (Fin m) (Fin n) ℝ) :
    U.conjTranspose=Uᵀ := by ext i j; simp

theorem Owner.Valid.matrix_posSemidef (O : Owner N) {δ : ℝ} (hO : O.Valid δ) (hδ : 0≤δ) :
    O.matrix.PosSemidef := by
  have h := (Matrix.PosSemidef.one.smul hδ).add (Matrix.le_iff.mp hO.2)
  simpa only [add_sub_cancel] using h

theorem Owner.Valid.physical_posSemidef (O : Owner N) {δ : ℝ} (hO : O.Valid δ) (hδ : 0≤δ) :
    O.physical.PosSemidef := by
  simpa only [Owner.physical,real_conjTranspose] using
    (hO.matrix_posSemidef O hδ).mul_mul_conjTranspose_same O.frame

theorem trace_physical (O : Owner N) (hO : O.frameᵀ*O.frame=1) : realTrace O.physical=realTrace O.matrix := by
  change Matrix.trace (O.frame*O.matrix*O.frameᵀ)=Matrix.trace O.matrix
  rw [Matrix.trace_mul_cycle,hO,Matrix.one_mul]

theorem clean_valid (O : Owner N) {δ : ℝ} (hδ : 0<δ) (hO : O.Valid δ) :
    (clean O δ).Valid (2*δ) := by
  have hG := hO.matrix_posSemidef O hδ.le
  refine ⟨?_,MSManuscriptCleanupCoordinates.matrix_floor O.matrix hG hδ hO.2⟩
  change (O.frame*MSManuscriptCleanupCoordinates.frame O.matrix δ)ᵀ*
    (O.frame*MSManuscriptCleanupCoordinates.frame O.matrix δ)=1
  rw [Matrix.transpose_mul]
  calc
    _ = (MSManuscriptCleanupCoordinates.frame O.matrix δ)ᵀ*(O.frameᵀ*O.frame)*
        MSManuscriptCleanupCoordinates.frame O.matrix δ := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hO.1,Matrix.mul_one,MSManuscriptCleanupCoordinates.frame_isometry]

theorem clean_physical (O : Owner N) {δ : ℝ} (hδ : 0≤δ) (hO : O.Valid δ) :
    (clean O δ).physical=O.frame*MSManuscriptJacobiCleanup.output O.matrix δ*O.frameᵀ := by
  rw [MSManuscriptCleanupCoordinates.output_factorization O.matrix (hO.matrix_posSemidef O hδ) δ]
  simp only [Owner.physical,clean,Matrix.transpose_mul,Matrix.mul_assoc]

theorem clean_le (O : Owner N) {δ : ℝ} (hδ : 0≤δ) (hO : O.Valid δ) :
    (clean O δ).physical≤O.physical := by
  have h := (Matrix.le_iff.mp (MSManuscriptJacobiCleanup.output_le O.matrix (hO.matrix_posSemidef O hδ) δ)).mul_mul_conjTranspose_same O.frame
  apply Matrix.le_iff.mpr
  simpa only [Matrix.mul_sub,Matrix.sub_mul,real_conjTranspose,←clean_physical O hδ hO,Owner.physical] using h

theorem clean_dim_le (O : Owner N) (δ : ℝ) : (clean O δ).dim≤O.dim :=
  MSManuscriptCleanupCoordinates.count_le O.matrix δ

theorem clean_trace_loss (O : Owner N) {δ : ℝ} (hδ : 0<δ) (hO : O.Valid δ) :
    realTrace O.physical-realTrace (clean O δ).physical ≤
      4*δ*(O.dim-(clean O δ).dim:ℕ) := by
  have htr : realTrace (clean O δ).physical=realTrace (MSManuscriptJacobiCleanup.output O.matrix δ) := by
    rw [clean_physical O hδ.le hO]
    change Matrix.trace (O.frame*MSManuscriptJacobiCleanup.output O.matrix δ*O.frameᵀ)=_
    rw [Matrix.trace_mul_cycle,hO.1,Matrix.one_mul]
    rfl
  rw [trace_physical O hO.1,htr]
  exact MSManuscriptCleanupCoordinates.output_trace_loss_count O.matrix (hO.matrix_posSemidef O hδ.le) hδ hO.2

theorem paid_valid (O : Owner N) {δ α : ℝ} (_hδ : 0<δ) (hO : O.Valid (2*δ))
    (hα : 0≤α) (hαδ : α≤δ) (u : EuclideanSpace ℝ (Fin O.dim)) (hu : ‖u‖=1) :
    (paid O α (WithLp.ofLp u)).Valid δ := by
  have hne : WithLp.ofLp u≠0 := by
    intro hz
    have hu0 : u=0 := (WithLp.equiv 2 _).injective hz
    rw [hu0,norm_zero] at hu
    norm_num at hu
  have hr : unitRank (WithLp.ofLp u) ≤ (1 : Matrix (Fin O.dim) (Fin O.dim) ℝ) :=
    unitRank_le_projection Matrix.isHermitian_one (by simp) hne (by simp)
  have hf := cut_floor hO.2 hα hr
  refine ⟨hO.1,?_⟩
  change δ • (1 : Matrix (Fin O.dim) (Fin O.dim) ℝ) ≤ cut O.matrix α (WithLp.ofLp u)
  apply le_trans ?_ hf
  apply Matrix.le_iff.mpr
  have hp := (Matrix.PosSemidef.one : (1 : Matrix (Fin O.dim) (Fin O.dim) ℝ).PosSemidef).smul
    (show 0≤(2*δ-α)-δ by linarith)
  convert hp using 1
  module

theorem paid_trace (O : Owner N) (hO : O.frameᵀ*O.frame=1) (α : ℝ)
    (u : Fin O.dim → ℝ) (hu : u≠0) :
    realTrace (paid O α u).physical=realTrace O.physical-α := by
  rw [trace_physical (paid O α u) hO,trace_physical O hO]
  exact cut_trace O.matrix α hu

theorem paid_le (O : Owner N) {α : ℝ} (hα : 0≤α) (u : Fin O.dim → ℝ) :
    (paid O α u).physical≤O.physical := by
  have h := (Matrix.le_iff.mp (cut_le O.matrix hα u)).mul_mul_conjTranspose_same O.frame
  apply Matrix.le_iff.mpr
  simpa only [Matrix.mul_sub,Matrix.sub_mul,real_conjTranspose,Owner.physical,paid] using h

end MatrixSpencer.MSManuscriptSupportedOwner
