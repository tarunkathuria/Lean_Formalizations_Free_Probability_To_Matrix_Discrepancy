import MatrixSpencer.MSManuscriptPreparedMovement
import MatrixSpencer.EpochState

/-! Primitive input parameters uniform throughout a numerical epoch. Only
the actual center depends on x; numerical curvature caps, paid-cut budgets
and the fixed movement mesh remain unchanged across cube states. -/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.MSManuscriptEpochInput
open MSManuscriptSupportedGamma MSManuscriptSupportedPaid MSManuscriptSupportedPreparation
variable {N d : ℕ}
local instance : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
set_option maxHeartbeats 1200000

variable (H : selfAdjoint (Matrix (Fin d) (Fin d) ℂ))
    (A : Fin N → Matrix (Fin d) (Fin d) ℂ) (hA : ∀i,(A i).IsHermitian)
    (θ δ t : ℝ) (hd : 0 < d)

/-- The matrix bound uses only entry arithmetic and a scalar square root. -/
def centerCap : ℝ := KSOwnerInputBounds.matrixBound (H : Matrix (Fin d) (Fin d) ℂ)+(N : ℝ)

def params (x : EuclideanSpace ℝ (Fin N)) : Parameters N d := by
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  exact {
    center := epochCenter H A hA x
    atoms := A
    regularizer := θ
    centerCap := centerCap H (N := N)
    floor := δ
    threshold := t
    physicalDimension_pos := hd }

theorem centerCap_pos : 0 < centerCap H (N := N) := by
  have h := KSOwnerInputBounds.matrixBound_pos (H : Matrix (Fin d) (Fin d) ℂ)
  unfold centerCap
  positivity

theorem params_valid (hAn : ∀i,‖A i‖≤1) (hθ : 0 < θ) (hδ : 0 < δ)
    (hδ1 : δ≤1) (ht : 0 < t) (x : EuclideanSpace ℝ (Fin N)) (hx : ∀i,|x i|≤1) :
    (params H A hA θ δ t hd x).Valid := by
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  refine ⟨hA,hAn,hθ,hδ,hδ1,ht,?_⟩
  have hc := epochCenter_norm_le H A hA hAn x hx
  have hH := KSOwnerInputBounds.norm_le_matrixBound (H : Matrix (Fin d) (Fin d) ℂ) H.property
  change ‖epochCenter H A hA x‖ ≤ centerCap H (N := N)
  simp only [Fintype.card_fin] at hc
  exact hc.trans (add_le_add_right hH (N : ℝ))

theorem curvatureBudget_independent (x y : EuclideanSpace ℝ (Fin N)) :
    curvatureBudget (params H A hA θ δ t hd x) = curvatureBudget (params H A hA θ δ t hd y) := rfl

theorem paidSize_independent (x y : EuclideanSpace ℝ (Fin N)) :
    paidSize (params H A hA θ δ t hd x) = paidSize (params H A hA θ δ t hd y) := rfl

theorem paidGain_independent (x y : EuclideanSpace ℝ (Fin N)) :
    paidGain (params H A hA θ δ t hd x) = paidGain (params H A hA θ δ t hd y) := rfl

theorem preparationBudget_independent (x y : EuclideanSpace ℝ (Fin N)) :
    budget (params H A hA θ δ t hd x) = budget (params H A hA θ δ t hd y) := rfl

theorem stepSize_independent (ε : ℝ) (x y : EuclideanSpace ℝ (Fin N)) :
    MSManuscriptPreparedMovement.stepSize (params H A hA θ δ t hd x) ε =
      MSManuscriptPreparedMovement.stepSize (params H A hA θ δ t hd y) ε := rfl

/-- One explicit epoch mesh meeting both the cube margin and matched Taylor constraints. -/
def mesh (ε εDrift : ℝ) : ℝ :=
  min (ε/Real.sqrt ((N:ℝ)+1))
    (min (1/2) (MSManuscriptPreparedMovement.stepSize (params H A hA θ δ t hd 0) εDrift))

theorem mesh_le_step (ε εDrift : ℝ) (x : EuclideanSpace ℝ (Fin N)) :
    mesh H A hA θ δ t hd ε εDrift ≤
      MSManuscriptPreparedMovement.stepSize (params H A hA θ δ t hd x) εDrift :=
  (min_le_right _ _).trans (min_le_right _ _)

theorem mesh_pos (hAn : ∀i,‖A i‖≤1) (hθ : 0 < θ) (hδ : 0 < δ)
    (hδ1 : δ≤1) (ht : 0 < t) {ε εDrift : ℝ} (hε : 0 < ε) (he : 0 < εDrift) :
    0 < mesh H A hA θ δ t hd ε εDrift := by
  have hp := params_valid H A hA θ δ t hd hAn hθ hδ hδ1 ht 0 (by simp)
  have hs := MSManuscriptPreparedMovement.stepSize_pos _ hp he
  unfold mesh
  positivity

theorem mesh_cube (hAn : ∀i,‖A i‖≤1) (hθ : 0 < θ) (hδ : 0 < δ)
    (hδ1 : δ≤1) (ht : 0 < t) {ε εDrift : ℝ} (hε : 0 < ε) (he : 0 < εDrift) :
    mesh H A hA θ δ t hd ε εDrift*Real.sqrt (N:ℝ) ≤ ε := by
  have hm := (mesh_pos H A hA θ δ t hd hAn hθ hδ hδ1 ht hε he).le
  have hr : 0 < Real.sqrt ((N:ℝ)+1) := Real.sqrt_pos.mpr (by positivity)
  have hb : mesh H A hA θ δ t hd ε εDrift ≤ ε/Real.sqrt ((N:ℝ)+1) := min_le_left _ _
  calc
    _ ≤ mesh H A hA θ δ t hd ε εDrift*Real.sqrt ((N:ℝ)+1) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith)) hm
    _ ≤ ε := (le_div_iff₀ hr).mp hb

theorem mesh_radius (ε εDrift : ℝ) :
    mesh H A hA θ δ t hd ε εDrift ≤ MSManuscriptMatchedInterval.radius δ/2 :=
  (mesh_le_step H A hA θ δ t hd ε εDrift 0).trans
    (MSManuscriptPreparedMovement.stepSize_le _ _)

theorem mesh_sq_le_half (hAn : ∀i,‖A i‖≤1) (hθ : 0 < θ) (hδ : 0 < δ)
    (hδ1 : δ≤1) (ht : 0 < t) {ε εDrift : ℝ} (hε : 0 < ε) (he : 0 < εDrift) :
    (mesh H A hA θ δ t hd ε εDrift)^2≤1/2 := by
  have hm := mesh_pos H A hA θ δ t hd hAn hθ hδ hδ1 ht hε he
  have hq := (mesh_le_step H A hA θ δ t hd ε εDrift 0).trans
    (MSManuscriptPreparedMovement.stepSize_le_quarter _ _)
  nlinarith

theorem mesh_budget (hAn : ∀i,‖A i‖≤1) (hθ : 0 < θ) (hδ : 0 < δ)
    (hδ1 : δ≤1) (ht : 0 < t) {ε εDrift : ℝ} (hε : 0 < ε) (he : 0 < εDrift) :
    MSManuscriptMovementDrift.uniformBudget N d (centerCap H (N := N)) θ δ*
      (mesh H A hA θ δ t hd ε εDrift)^2/24≤εDrift := by
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  have hp := params_valid H A hA θ δ t hd hAn hθ hδ hδ1 ht 0 (by simp)
  have hb := MSManuscriptPreparedMovement.stepSize_budget _ hp he
  have hm := (mesh_pos H A hA θ δ t hd hAn hθ hδ hδ1 ht hε he).le
  have hs := MSManuscriptPreparedMovement.stepSize_pos _ hp he
  have hsq := (sq_le_sq₀ hm hs.le).mpr (mesh_le_step H A hA θ δ t hd ε εDrift 0)
  have hM := MSManuscriptMovementDrift.uniformBudget_pos (N := N) (d := d) (γ := δ)
    (centerCap_pos H (N := N)).le hθ
  exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hM.le) (by norm_num)).trans hb

/-- Primitive epoch data, with original Hermitian atoms and a fixed offset. -/
structure Input (N d : ℕ) where
  offset : selfAdjoint (Matrix (Fin d) (Fin d) ℂ)
  atoms : Fin N → Matrix (Fin d) (Fin d) ℂ
  hermitian : ∀i,(atoms i).IsHermitian
  regularizer : ℝ
  floor : ℝ
  threshold : ℝ
  dimension_pos : 0 < d

def Input.Valid (I : Input N d) : Prop :=
  (∀i,‖I.atoms i‖≤1) ∧ 0 < I.regularizer ∧ 0 < I.floor ∧ I.floor≤1 ∧ 0 < I.threshold

def Input.params (I : Input N d) (x : EuclideanSpace ℝ (Fin N)) : Parameters N d :=
  MSManuscriptEpochInput.params I.offset I.atoms I.hermitian I.regularizer I.floor I.threshold I.dimension_pos x

theorem Input.params_valid (I : Input N d) (hI : I.Valid)
    (x : EuclideanSpace ℝ (Fin N)) (hx : ∀i,|x i|≤1) : (I.params x).Valid :=
  MSManuscriptEpochInput.params_valid I.offset I.atoms I.hermitian I.regularizer I.floor I.threshold I.dimension_pos
    hI.1 hI.2.1 hI.2.2.1 hI.2.2.2.1 hI.2.2.2.2 x hx

def Input.mesh (I : Input N d) (ε εDrift : ℝ) : ℝ :=
  MSManuscriptEpochInput.mesh I.offset I.atoms I.hermitian I.regularizer I.floor I.threshold I.dimension_pos ε εDrift

theorem Input.mesh_pos (I : Input N d) (hI : I.Valid) {ε εDrift : ℝ}
    (hε : 0 < ε) (he : 0 < εDrift) : 0 < I.mesh ε εDrift :=
  MSManuscriptEpochInput.mesh_pos I.offset I.atoms I.hermitian I.regularizer I.floor I.threshold I.dimension_pos
    hI.1 hI.2.1 hI.2.2.1 hI.2.2.2.1 hI.2.2.2.2 hε he

theorem Input.mesh_cube (I : Input N d) (hI : I.Valid) {ε εDrift : ℝ}
    (hε : 0 < ε) (he : 0 < εDrift) : I.mesh ε εDrift*Real.sqrt (N:ℝ) ≤ ε :=
  MSManuscriptEpochInput.mesh_cube I.offset I.atoms I.hermitian I.regularizer I.floor I.threshold I.dimension_pos
    hI.1 hI.2.1 hI.2.2.1 hI.2.2.2.1 hI.2.2.2.2 hε he

theorem Input.mesh_le_step (I : Input N d) (ε εDrift : ℝ) (x : EuclideanSpace ℝ (Fin N)) :
    I.mesh ε εDrift≤MSManuscriptPreparedMovement.stepSize (I.params x) εDrift :=
  MSManuscriptEpochInput.mesh_le_step I.offset I.atoms I.hermitian I.regularizer I.floor I.threshold I.dimension_pos ε εDrift x

theorem Input.mesh_sq_le_half (I : Input N d) (hI : I.Valid) {ε εDrift : ℝ}
    (hε : 0 < ε) (he : 0 < εDrift) : (I.mesh ε εDrift)^2≤1/2 :=
  MSManuscriptEpochInput.mesh_sq_le_half I.offset I.atoms I.hermitian I.regularizer I.floor I.threshold I.dimension_pos
    hI.1 hI.2.1 hI.2.2.1 hI.2.2.2.1 hI.2.2.2.2 hε he

theorem Input.paidSize_independent (I : Input N d) (x y : EuclideanSpace ℝ (Fin N)) :
    paidSize (I.params x) = paidSize (I.params y) := rfl

theorem Input.paidGain_independent (I : Input N d) (x y : EuclideanSpace ℝ (Fin N)) :
    paidGain (I.params x) = paidGain (I.params y) := rfl

theorem Input.preparationBudget_independent (I : Input N d) (x y : EuclideanSpace ℝ (Fin N)) :
    budget (I.params x) = budget (I.params y) := rfl

end MatrixSpencer.MSManuscriptEpochInput
