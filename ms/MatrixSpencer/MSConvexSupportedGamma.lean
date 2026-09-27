import MatrixSpencer.MSManuscriptSupportedGamma
import MatrixSpencer.MSConvexGammaInputBoundScaled

/-! Convex-solver substitution for the original numerical value calls.
All original geometric and scalar parameter definitions are retained. -/
open Matrix Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.MSConvexSupportedGamma
open MSManuscriptSupportedGamma MSManuscriptSupportedOwner
variable [MSConvexOwnerValue.Oracle]
variable {N k d : ℕ}
local instance : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
set_option maxHeartbeats 1400000
attribute [local irreducible] ownerPotential observedOwnedGram

def response (P : Parameters N d) (O : Owner N) :=
  MSConvexGammaMatrix.report P.center (family P O) O.matrix P.regularizer
    P.physicalDimension_pos P.floor
    (MSManuscriptGammaInputBoundScaled.secondCap O.dim d P.centerCap P.regularizer P.floor N)
    (MSManuscriptGammaMatrix.topPrecision O.dim P.threshold)

def direction (P : Parameters N d) (O : Owner N) : Option (EuclideanSpace ℝ (Fin O.dim)) :=
  if hk : 0<O.dim then
    if MSManuscriptGammaTop.stop (response P O) P.threshold hk then none
    else some (MSManuscriptGammaTop.vector (response P O) P.threshold hk)
  else none

theorem response_isSymm (P : Parameters N d) (O : Owner N) : (response P O).IsSymm :=
  MSConvexGammaMatrix.report_isSymm _ _ _ _ _ _ _ _

theorem response_accuracy (P : Parameters N d) (hP : P.Valid) (O : Owner N)
    (hO : O.Valid P.floor) (hO1 : O.physical≤1) (hk : 0<O.dim) :
    ‖Matrix.toEuclideanCLM (𝕜:=ℝ) (gram P O-response P O)‖≤P.threshold/64 := by
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp P.physicalDimension_pos
  have h := MSConvexGammaInputBoundScaled.report_accuracy P.center (family P O)
    (family_isHermitian P hP O) (Nat.cast_nonneg N)
    (MSManuscriptFrameFamily.stored_family_norm_le P.atoms hP.2.1 O hO)
    hP.2.2.1 hP.2.2.2.1 hP.2.2.2.2.1
    (MSManuscriptGammaMatrix.topPrecision_pos hk hP.2.2.2.2.2.1)
    hP.2.2.2.2.2.2 P.physicalDimension_pos hO.2
    (MSManuscriptFrameFamily.stored_matrix_le_one O hO hO1)
  rw [MSManuscriptGammaMatrix.topPrecision_budget hk] at h
  exact h

theorem direction_none (P : Parameters N d) (hP : P.Valid) (O : Owner N)
    (hO : O.Valid P.floor) (hO1 : O.physical≤1) (ho : direction P O=none) : Cap P O := by
  unfold direction at ho
  split at ho
  · rename_i hk
    split_ifs at ho with hs
    · exact MSManuscriptGammaTop.stop_sound _ _ (gram_isSymm P hP O) (response_isSymm P O)
        hP.2.2.2.2.2.1 hk (response_accuracy P hP O hO hO1 hk) hs
  · rename_i hk
    haveI : IsEmpty (Fin O.dim) := ⟨fun j => by have hj := j.isLt; omega⟩
    have he : gram P O=P.threshold • (1 : Matrix (Fin O.dim) (Fin O.dim) ℝ) :=
      Subsingleton.elim _ _
    exact le_of_eq he

theorem direction_some (P : Parameters N d) (hP : P.Valid) (O : Owner N)
    (hO : O.Valid P.floor) (hO1 : O.physical≤1) {u : EuclideanSpace ℝ (Fin O.dim)}
    (ho : direction P O=some u) :
    ‖u‖=1 ∧ 7*P.threshold/8<KSRayleighAccuracy.realRayleigh (gram P O) u := by
  unfold direction at ho
  split at ho
  · rename_i hk
    split_ifs at ho with hs
    rw [←Option.some.inj ho]
    exact MSManuscriptGammaTop.continue_sound _ _ hP.2.2.2.2.2.1 hk
      (response_accuracy P hP O hO hO1 hk) (Bool.eq_false_iff.mpr hs)
  · simp at ho

end MatrixSpencer.MSConvexSupportedGamma
