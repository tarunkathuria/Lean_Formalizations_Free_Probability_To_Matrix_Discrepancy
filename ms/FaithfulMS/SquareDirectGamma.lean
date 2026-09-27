import FaithfulMS.SquareDirectOracle
import FaithfulMS.SquareDirectEVD
import MatrixSpencer.MSManuscriptSupportedGamma

/-! Compute the covariance derivative from the primal optimizer and select a
large-response direction by exact EVD. There are no value differences. -/
open Matrix Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace FaithfulMS.SquareDirectGamma
open MatrixSpencer MSManuscriptSupportedGamma MSManuscriptSupportedOwner
open SquareDirectOracle
variable [Oracle]
variable {N d : ℕ}
local instance : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1800000

/-- The guard only totalizes the mathematical function off its certified
input domain. Counted callers supply these proved properties directly. -/
def response (P : Parameters N d) (O : Owner N) : Matrix (Fin O.dim) (Fin O.dim) ℝ :=
  if h : P.Valid ∧ O.Valid P.floor then
    let p := Oracle.service.squareSolution P.center (family P O)
      (family_isHermitian P h.1 O) O.matrix
      (h.2.matrix_posSemidef O h.1.2.2.2.1.le) P.physicalDimension_pos
      P.regularizer h.1.2.2.1
    DirectDensity.gamma (family P O) O.matrix p.density
  else 0

theorem response_eq (P : Parameters N d) (hP : P.Valid) (O : Owner N)
    (hO : O.Valid P.floor) : response P O = gram P O := by
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp P.physicalDimension_pos
  simp only [response, dif_pos (And.intro hP hO)]
  exact DirectDensity.SquareSolution.gamma_eq P.center _ hP.2.2.1

def vector (G : Matrix (Fin N) (Fin N) ℝ) (hN : 0<N) : EuclideanSpace ℝ (Fin N) :=
  SquareDirectEVD.output (-G) hN

def value (G : Matrix (Fin N) (Fin N) ℝ) (hN : 0<N) : ℝ :=
  KSRayleighAccuracy.realRayleigh G (vector G hN)

def direction (P : Parameters N d) (O : Owner N) : Option (EuclideanSpace ℝ (Fin O.dim)) :=
  if hk : 0<O.dim then
    if value (response P O) hk ≤ P.threshold then none
    else some (vector (response P O) hk)
  else none

theorem vector_norm (G : Matrix (Fin N) (Fin N) ℝ) (hN : 0<N) :
    ‖vector G hN‖ = 1 := SquareDirectEVD.output_norm _ _

theorem competitor (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.IsSymm)
    (hN : 0<N) (v : EuclideanSpace ℝ (Fin N)) (hv : ‖v‖=1) :
    KSRayleighAccuracy.realRayleigh G v ≤ value G hN := by
  have h := SquareDirectEVD.output_minimal (-G) hG.neg hN v hv
  simp only [MSManuscriptGammaTop.rayleigh_neg] at h
  exact neg_le_neg_iff.mp h

theorem direction_none (P : Parameters N d) (hP : P.Valid) (O : Owner N)
    (hO : O.Valid P.floor) (_hO1 : O.physical≤1) (ho : direction P O=none) : Cap P O := by
  unfold direction at ho
  split at ho
  · rename_i hk
    split_ifs at ho with hs
    · apply MSManuscriptGammaTop.le_scalar_of_unitRayleigh _ (gram_isSymm P hP O)
      intro v hv
      rw [response_eq P hP O hO] at hs
      exact (competitor (gram P O) (gram_isSymm P hP O) hk v hv).trans hs
  · rename_i hk
    haveI : IsEmpty (Fin O.dim) := ⟨fun j => by have hj := j.isLt; omega⟩
    exact le_of_eq (Subsingleton.elim _ _)

theorem direction_some (P : Parameters N d) (hP : P.Valid) (O : Owner N)
    (hO : O.Valid P.floor) (_hO1 : O.physical≤1) {u : EuclideanSpace ℝ (Fin O.dim)}
    (ho : direction P O=some u) :
    ‖u‖=1 ∧ 7*P.threshold/8<KSRayleighAccuracy.realRayleigh (gram P O) u := by
  unfold direction at ho
  split at ho
  · rename_i hk
    split_ifs at ho with hs
    rw [←Option.some.inj ho]
    refine ⟨vector_norm _ _, ?_⟩
    rw [response_eq P hP O hO] at hs ⊢
    change ¬KSRayleighAccuracy.realRayleigh (gram P O) (vector (gram P O) hk)≤P.threshold at hs
    have ht := hP.2.2.2.2.2.1
    linarith
  · simp at ho

end FaithfulMS.SquareDirectGamma
