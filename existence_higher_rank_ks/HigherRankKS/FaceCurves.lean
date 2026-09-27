import HigherRankKS.FaceGeometry
import HigherRankKS.OwnerCurves

/-! Affine discrepancy and owner curves on an original cube face. -/

open Matrix MatrixSpencer
open scoped BigOperators MatrixOrder ComplexOrder

noncomputable section
namespace HigherRankKS.FaceGeometry

variable {N : ℕ} {n : Type*} [Fintype n] [DecidableEq n]

theorem signed_center_liftDirection (A : Fin N → Matrix n n ℂ)
    (x : Fin N → ℝ) (h : {i // i ∈ live x} → ℝ) :
    signedLift (KSPotentialModels.center A (liftDirection x h)) =
      ∑ i : {i // i ∈ live x}, h i • signedLift (A i) := by
  classical
  rw [KSPotentialModels.center, signedLift_sum_smul]
  have hs := Fintype.sum_subtype_add_sum_subtype (fun i => i ∈ live x)
    (fun i => liftDirection x h i • signedLift (A i))
  have hr : (∑ i : {i // i ∉ live x}, liftDirection x h i • signedLift (A i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    simp only [liftDirection, dif_neg i.property, zero_smul]
  rw [hr, add_zero] at hs
  apply hs.symm.trans
  apply Finset.sum_congr (by ext i; simp)
  intro i _
  simp only [liftDirection, dif_pos i.property]

theorem signed_center_face_line (A : Fin N → Matrix n n ℂ)
    (x : Fin N → ℝ) (h : {i // i ∈ live x} → ℝ) (t : ℝ) :
    signedLift (KSPotentialModels.center A (faceState (live x) x (livePoint x + t • h))) =
      signedLift (KSPotentialModels.center A x) +
        t • (∑ i : {i // i ∈ live x}, h i • signedLift (A i)) := by
  rw [faceState_line, ← signed_center_liftDirection A x h]
  simp only [KSPotentialModels.center]
  simp only [signedLift_sum_smul]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_smul,
    MulAction.mul_smul, Finset.sum_add_distrib, Finset.smul_sum]

theorem face_potential_line_eq (A : Fin N → Matrix n n ℂ) {β : ℝ} (hβ : 0 < β)
    (θ : ℝ) {x : Fin N → ℝ} (hx : x ∈ ksCube 1)
    (h : {i // i ∈ live x} → ℝ) (t : ℝ) :
    cubePotential A β θ (faceState (live x) x (livePoint x + t • h)) =
      potential (signedLift (KSPotentialModels.center A x) +
        t • (∑ i : {i // i ∈ live x}, h i • signedLift (A i)))
        (fun i : {i // i ∈ live x} => A i) β
        (OwnerCurves.weights β (livePoint x) h t) θ := by
  rw [face_potential_eq A hβ θ hx, signed_center_face_line]
  rfl

end HigherRankKS.FaceGeometry
