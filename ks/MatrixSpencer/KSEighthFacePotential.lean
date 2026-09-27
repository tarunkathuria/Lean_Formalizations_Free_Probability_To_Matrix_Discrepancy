import MatrixSpencer.KSEighthLiveCoordinates
import MatrixSpencer.KSEighthSmoothness
import MatrixSpencer.KSEighthLiveSource
import MatrixSpencer.KSEighthNumericalValue
import MatrixSpencer.KSNumericalHessian



open Matrix Set Filter Topology
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
noncomputable section
namespace MatrixSpencer.KSEighthFacePotential

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

open KSEighthLiveCoordinates KSPotentialModels KSLiveCurve
variable {N : ℕ} {n : Type*} [Fintype n] [DecidableEq n]
local instance {k : Type*} [Fintype k] [DecidableEq k] : CStarAlgebra (Matrix k k ℂ) := {}

local instance {k : Type*} [Fintype k] [DecidableEq k] :
    NormedAddCommGroup (selfAdjoint (Matrix k k ℝ)) := inferInstance
local instance {k : Type*} [Fintype k] [DecidableEq k] :
    NormedSpace ℝ (selfAdjoint (Matrix k k ℝ)) := inferInstance

abbrev Space (x : Fin N → ℝ) := EuclideanSpace ℝ (Fin (KSEighthLiveEnumeration.count x))

def faceOwners (x : Fin N → ℝ) (z : Space x) : Live (1/8) x → ℝ :=
  fun i => 64 * (1 - (face x z i)^2)

def potential (v : Fin N → n → ℂ) (θ : ℝ) (x : Fin N → ℝ) (z : Space x) : ℝ :=
  ownerPotential (signedLift (center (fun i => KSRankOne.atom (v i)) (face x z)))
    (KSEighthActualState.family (fun i : Live (1/8) x => v i))
    (KSIndependentSource.coefficientCovariance (faceOwners x z)) θ

def fixedCenter (v : Fin N → n → ℂ) (x : Fin N → ℝ) :
    Space x → selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ) :=
  fun z => ∑ i, face x z i •
    (⟨signedLift (KSRankOne.atom (v i)),
      signedLift_isHermitian (KSRankOne.atom_isHermitian (v i))⟩ :
      selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ))

theorem fixedCenter_coe (v : Fin N → n → ℂ) (x : Fin N → ℝ) (z : Space x) :
    (fixedCenter v x z : Matrix (n ⊕ n) (n ⊕ n) ℂ) =
      signedLift (center (fun i => KSRankOne.atom (v i)) (face x z)) := by
  simp [fixedCenter, KSPotentialModels.center, signedLift_sum_smul]

theorem contDiff_face_apply (x : Fin N → ℝ) (i : Fin N) :
    ContDiff ℝ ∞ (fun z => face x z i) :=
  contDiff_const.add ((PiLp.proj 2 (fun _ : Fin N => ℝ) i).contDiff.comp (weightedMap x).contDiff)

theorem contDiff_fixedCenter (v : Fin N → n → ℂ) (x : Fin N → ℝ) :
    ContDiff ℝ ∞ (fixedCenter v x) := by
  apply ContDiff.sum
  intro i _
  exact (contDiff_face_apply x i).smul contDiff_const

theorem contDiff_faceOwners (x : Fin N → ℝ) : ContDiff ℝ ∞ (faceOwners x) := by
  apply contDiff_pi.mpr
  intro i
  exact contDiff_const.mul (contDiff_const.sub ((contDiff_face_apply x i).pow 2))

theorem faceOwners_zero_pos (x : Fin N → ℝ) (i : Live (1/8) x) : 0 < faceOwners x 0 i := by
  simp only [faceOwners, face_zero]
  have hi := abs_lt.mp i.property
  nlinarith [sq_nonneg (x i)]

theorem contDiffAt_potential [Nonempty n] (v : Fin N → n → ℂ) {θ : ℝ} (hθ : 0 < θ)
    (x : Fin N → ℝ) : ContDiffAt ℝ ∞ (potential v θ x) 0 := by
  let A := KSEighthActualState.family (fun i : Live (1/8) x => v i)
  let P := fun z => (fixedCenter v x z, KSEighthSmoothness.coefficientCovarianceCLM (faceOwners x z))
  have hP : ContDiff ℝ ∞ P := (contDiff_fixedCenter v x).prodMk
    ((KSEighthSmoothness.coefficientCovarianceCLM (ι := Live (1/8) x)).contDiff.comp
      (contDiff_faceOwners x))
  have hC : ((P 0).2 : Matrix (Live (1/8) x × Bool) (Live (1/8) x × Bool) ℝ).PosDef :=
    Matrix.posDef_diagonal_iff.mpr (fun j => faceOwners_zero_pos x j.1)
  have hA : ∀ i, (A i).IsHermitian := KSEighthActualState.family_isHermitian _
  have hs := (contDiffAt_jointHermitianOwnerPotential A hA hθ (P 0).1 (P 0).2 hC).comp 0 hP.contDiffAt
  convert hs using 1
  funext z
  change ownerPotential _ _ _ θ = ownerPotential _ _ _ θ
  change ownerPotential _ A _ θ = ownerPotential (fixedCenter v x z) A
    (KSEighthSmoothness.coefficientCovarianceCLM (faceOwners x z)) θ
  rw [fixedCenter_coe, KSEighthSmoothness.coefficientCovarianceCLM_coe]

theorem potential_zero [Nonempty n] (v : Fin N → n → ℂ) {θ : ℝ} (hθ : 0 < θ)
    {x : Fin N → ℝ} (hx : x ∈ ksCube (1/8)) :
    potential v θ x 0 = eighthPotential (fun i => KSRankOne.atom (v i)) θ x := by
  rw [KSEighthLiveSource.potential_state v hx hθ]
  have ho : faceOwners x 0 = KSEighthBalanced.owner (fun i : Live (1/8) x => x i) := by
    funext i
    simp only [faceOwners, face_zero, KSEighthBalanced.owner]
  unfold potential
  rw [face_zero, ho]
  rfl

/-- Equality with the full-label retained-mask energy at every legal query. -/
theorem potential_eq_retained [Nonempty n] (v : Fin N → n → ℂ) {θ a : ℝ} (hθ : 0 < θ)
    (x : Fin N → ℝ) (z : Space x) (ha : a ≤ 1) (hz : face x z ∈ ksCube a) :
    potential v θ x z = commonPotential (fun i => KSRankOne.atom (v i)) θ
      (face x z) (maskedOwners 64 (live (1/8) x) (face x z)) := by
  have hc := maskedOwners_nonneg (by norm_num : (0 : ℝ) ≤ 64) ha hz (live (1/8) x)
  rw [commonPotential, KSCommonSource.potential_eq_independent _ _
    (fun i => KSRankOne.atom_isHermitian (v i)) hc hθ,
    KSEighthLiveSource.potential_restrict v (1/8) x _ (by
      intro i hi
      simp only [maskedOwners, live, Finset.mem_filter, Finset.mem_univ, true_and, if_neg hi])]
  unfold potential
  congr 2
  funext i
  simp only [maskedOwners, live, Finset.mem_filter, Finset.mem_univ, true_and,
    if_pos i.property, faceOwners, naturalOwners]

/-- While the actual movement stays in the same open face, the retained
extension is exactly the actual state potential. -/
theorem potential_eq_state [Nonempty n] (v : Fin N → n → ℂ) {θ ρ : ℝ} (hθ : 0 < θ)
    {x : Fin N → ℝ} (hx : x ∈ ksCube (1/8)) (z : Space x)
    (hm : ∀ i, |x i| < 1/8 → ρ ≤ 1/8 - |x i|) (hz : ‖z‖ < ρ) :
    potential v θ x z = eighthPotential (fun i => KSRankOne.atom (v i)) θ (face x z) := by
  have hcube := face_mem_cube hx z hm hz
  rw [potential_eq_retained v hθ x z (by norm_num : (1/8 : ℝ) ≤ 1) hcube]
  have hl : live (1/8) (face x z) = live (1/8) x := by
    ext i
    simp only [live, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hi : |x i| < (1/8 : ℝ)
    · exact iff_of_true (face_live x z hm hz i hi) hi
    · rw [face_dead x z i hi]
  simp only [eighthPotential, truncatedOwners, hl]

/-- Explicit coefficient direction represented by a normalized live vector. -/
def lineDirection (x : Fin N → ℝ) (w : Space x) : Live (1/8) x → ℝ := fun i => weightedMap x w i

theorem face_line_eq_path (x : Fin N → ℝ) (w : Space x) (t : ℝ) :
    face x (t • w) = path (1/8) x (lineDirection x w) t := by
  funext i
  rw [face, map_smul]
  change x i + t * weightedMap x w i = _
  by_cases hi : |x i| < (1/8 : ℝ)
  · simp only [path, KSLiveCurve.extend, dif_pos hi, lineDirection]
  · rw [weightedMap_apply, KSEighthLiveEnumeration.extend_dead x w i hi]
    simp only [path, KSLiveCurve.extend, dif_neg hi, mul_zero, add_zero]

/-- Exact retained-owner curve identity, without any source positivity or
endpoint hypothesis on the parameter. -/
theorem potential_line_eq (v : Fin N → n → ℂ) (θ : ℝ)
    (x : Fin N → ℝ) (w : Space x) (t : ℝ) :
    potential v θ x (t • w) = KSEighthLocalState.curvePotential
      (center (fun i => KSRankOne.atom (v i)) x) (fun i : Live (1/8) x => v i)
      θ (fun i => x i) (lineDirection x w) t := by
  unfold potential KSEighthLocalState.curvePotential KSEighthLocalState.curveCenter
  rw [face_line_eq_path, KSSpinLiveSource.signed_center_path]
  congr 2
  funext i
  simp only [faceOwners, face_line_eq_path, path_live, KSEighthLocalState.curveOwners]

end MatrixSpencer.KSEighthFacePotential
