import MatrixSpencer.PhasePotential
import Mathlib.Data.Finset.Sort

/-! Finite ordered coefficient enumeration and exact transports used by the
numerical epoch adapter. Enumeration sorts existing labels; it does not
choose coefficients or a favorable numerical endpoint. -/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.MSManuscriptCoefficientReindex
variable {ι κ n : Type*} [Fintype ι] [Fintype κ] [Fintype n]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq n]
local instance : CStarAlgebra (Matrix n n ℂ) := {}
set_option linter.unusedSectionVars false

/-- Ordered finite enumeration, with no spectral or optimizing choice. -/
def enumeration (ι : Type*) [Fintype ι] [LinearOrder ι] : Fin (Fintype.card ι) ≃ ι :=
  (Fintype.orderIsoFinOfCardEq ι rfl).toEquiv

def point (e : κ≃ι) (x : EuclideanSpace ℝ ι) : EuclideanSpace ℝ κ :=
  WithLp.toLp 2 (fun i => x (e i))

@[simp] theorem point_apply (e : κ≃ι) (x : EuclideanSpace ℝ ι) (i : κ) : point e x i=x (e i) := rfl

@[simp] theorem point_inverse (e : κ≃ι) (x : EuclideanSpace ℝ ι) : point e.symm (point e x)=x := by
  ext i
  exact congrArg (fun j=>x j) (e.apply_symm_apply i)

theorem point_regular (e : κ≃ι) {ε : ℝ} {x : EuclideanSpace ℝ ι} (hx : CubeRegular ε x) :
    CubeRegular ε (point e x) := ⟨fun i => hx.1 (e i),fun i=>hx.2 (e i)⟩

theorem point_norm_sq (e : κ≃ι) (x : EuclideanSpace ℝ ι) : ‖point e x‖^2=‖x‖^2 := by
  simp only [EuclideanSpace.norm_sq_eq,point_apply]
  exact e.sum_comp (fun i=>‖x i‖^2)

theorem point_norm (e : κ≃ι) (x : EuclideanSpace ℝ ι) : ‖point e x‖=‖x‖ := by
  nlinarith [point_norm_sq e x,norm_nonneg (point e x),norm_nonneg x]

theorem frozen_eq (e : κ≃ι) (x : EuclideanSpace ℝ ι) :
    frozenCoordinates (point e x)=(frozenCoordinates x).map e.symm.toEmbedding := by
  ext i
  simp only [mem_frozenCoordinates,point_apply,Finset.mem_map,Equiv.toEmbedding_apply]
  constructor
  · intro hi
    exact ⟨e i,hi,e.symm_apply_apply i⟩
  · rintro ⟨j,hj,hji⟩
    subst i
    exact (congrArg (fun k=>IsSign (x k)) (e.apply_symm_apply j)).mpr hj

theorem frozen_card (e : κ≃ι) (x : EuclideanSpace ℝ ι) :
    (frozenCoordinates (point e x)).card=(frozenCoordinates x).card := by
  rw [frozen_eq,Finset.card_map]

theorem center (H : selfAdjoint (Matrix n n ℂ)) (A : ι→Matrix n n ℂ)
    (hA : ∀i,(A i).IsHermitian) (e : κ≃ι) (x : EuclideanSpace ℝ ι) :
    epochCenter H (fun i=>A (e i)) (fun i=>hA (e i)) (point e x)=epochCenter H A hA x := by
  unfold epochCenter
  congr 1
  exact e.sum_comp (fun i=>x i • hermitianMatrixFamily A hA i)

theorem source_one (A : ι→Matrix n n ℂ) (e : κ≃ι) (S : Matrix n n ℂ) :
    covarianceSource (fun i=>A (e i)) 1 S=covarianceSource A 1 S := by
  rw [covarianceSource_one,covarianceSource_one]
  exact e.sum_comp (fun i=>A i*S*A i)

theorem potential_one (H : Matrix n n ℂ) (A : ι→Matrix n n ℂ) (e : κ≃ι) (θ : ℝ) :
    ownerPotential H (fun i=>A (e i)) 1 θ=ownerPotential H A 1 θ := by
  unfold ownerPotential
  congr 2
  funext S
  simp only [ownerObjective,source_one]

theorem centered_potential_one (H : selfAdjoint (Matrix n n ℂ)) (A : ι→Matrix n n ℂ)
    (hA : ∀i,(A i).IsHermitian) (e : κ≃ι) (x : EuclideanSpace ℝ ι) (θ : ℝ) :
    ownerPotential (epochCenter H (fun i=>A (e i)) (fun i=>hA (e i)) (point e x))
      (fun i=>A (e i)) 1 θ=ownerPotential (epochCenter H A hA x) A 1 θ := by
  rw [center,potential_one]

end MatrixSpencer.MSManuscriptCoefficientReindex
