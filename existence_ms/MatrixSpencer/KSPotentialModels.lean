import MatrixSpencer.KSCommonSource
import MatrixSpencer.KSEndpointCube

/-! The exact global owner functions and potentials on the two closed cubes. -/

open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix Set

noncomputable section
namespace MatrixSpencer.KSPotentialModels

set_option maxHeartbeats 800000

variable {N : ℕ} {n : Type*} [Fintype n] [DecidableEq n]

def center (A : Fin N → Matrix n n ℂ) (x : Fin N → ℝ) : Matrix n n ℂ :=
  ∑ i, x i • A i

def naturalOwners (u : ℝ) (x : Fin N → ℝ) (i : Fin N) : ℝ := u * (1 - x i ^ 2)

def live (a : ℝ) (x : Fin N → ℝ) : Finset (Fin N) :=
  Finset.univ.filter (fun i => |x i| < a)

def maskedOwners (u : ℝ) (L : Finset (Fin N)) (x : Fin N → ℝ) (i : Fin N) : ℝ :=
  if i ∈ L then naturalOwners u x i else 0

def truncatedOwners (a u : ℝ) (x : Fin N → ℝ) : Fin N → ℝ := maskedOwners u (live a x) x

def commonPotential (A : Fin N → Matrix n n ℂ) (θ : ℝ) (x : Fin N → ℝ) (c : Fin N → ℝ) : ℝ :=
  ownerPotential (signedLift (center A x)) (KSCommonSource.family A)
    (KSCommonSource.coefficientCovariance c) θ

/-- Exact original truncated-cube potential, including deletion of boundary owners. -/
def eighthPotential (A : Fin N → Matrix n n ℂ) (θ : ℝ) (x : Fin N → ℝ) : ℝ :=
  commonPotential A θ x (truncatedOwners (1 / 8) 64 x)

/-- Exact augmented source with all original coefficients in the full unit cube. -/
def spinPotential (A : Fin N → Matrix n n ℂ) (θ : ℝ) (x : Fin N → ℝ) : ℝ :=
  ownerPotential (signedLift (center A x)) (KSSpinSource.family A)
    (KSSpinSource.coefficientCovariance (naturalOwners 64 x)) θ

theorem center_isHermitian (A : Fin N → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (x : Fin N → ℝ) : (center A x).IsHermitian := by
  change (∑ i, x i • A i)ᴴ = ∑ i, x i • A i
  simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, star_trivial, fun i => (hA i).eq]

theorem center_eq_signedSum {d : ℕ} (A : Fin N → CMatrix d) (x : Fin N → ℝ) :
    center A x = signedSum A x := rfl

theorem naturalOwners_nonneg {u a : ℝ} (hu : 0 ≤ u) (ha : a ≤ 1)
    {x : Fin N → ℝ} (hx : x ∈ ksCube a) (i : Fin N) : 0 ≤ naturalOwners u x i := by
  apply mul_nonneg hu
  have hl := hx.1 i
  have hr := hx.2 i
  have hs : x i ^ 2 ≤ 1 := by nlinarith
  linarith

theorem maskedOwners_nonneg {u a : ℝ} (hu : 0 ≤ u) (ha : a ≤ 1)
    {x : Fin N → ℝ} (hx : x ∈ ksCube a) (L : Finset (Fin N)) (i : Fin N) :
    0 ≤ maskedOwners u L x i := by
  unfold maskedOwners
  split_ifs
  · exact naturalOwners_nonneg hu ha hx i
  · exact le_rfl

theorem commonPotential_mono [Nonempty n] (A : Fin N → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (θ : ℝ) (x : Fin N → ℝ)
    {c c' : Fin N → ℝ} (hc : ∀ i, 0 ≤ c i) (hc' : ∀ i, 0 ≤ c' i)
    (hle : ∀ i, c i ≤ c' i) : commonPotential A θ x c ≤ commonPotential A θ x c' := by
  apply ownerPotential_mono_covariance _ _ (KSCommonSource.family_isHermitian A hA)
    (KSCommonSource.coefficientCovariance_posSemidef hc)
    (KSCommonSource.coefficientCovariance_posSemidef hc')
  apply sub_nonneg.mp
  apply Matrix.PosSemidef.nonneg
  change (Matrix.diagonal c' - Matrix.diagonal c).PosSemidef
  rw [Matrix.diagonal_sub]
  exact Matrix.posSemidef_diagonal_iff.mpr (fun i => sub_nonneg.mpr (hle i))

theorem continuous_signed_center (A : Fin N → Matrix n n ℂ) :
    Continuous (fun x : Fin N → ℝ => signedLift (center A x)) := by
  unfold signedLift center
  apply continuous_matrix
  intro i j
  cases i <;> cases j <;>
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.sum_apply,
      Matrix.smul_apply, Matrix.neg_apply, Matrix.zero_apply] <;> fun_prop

theorem continuous_naturalOwners (u : ℝ) : Continuous (naturalOwners (N := N) u) := by
  unfold naturalOwners
  fun_prop

theorem continuous_maskedOwners (u : ℝ) (L : Finset (Fin N)) : Continuous (maskedOwners u L) := by
  apply continuous_pi
  intro i
  unfold maskedOwners naturalOwners
  split_ifs <;> fun_prop

variable {X κ : Type*} [TopologicalSpace X] [Fintype κ] [DecidableEq κ]

theorem continuousOn_diagonal_ownerPotential (A : κ → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (θ : ℝ) (D : Set X)
    (H : X → Matrix n n ℂ) (c : X → κ → ℝ)
    (hH : ContinuousOn H D) (hc : ContinuousOn c D)
    (hpos : ∀ x ∈ D, ∀ i, 0 ≤ c x i) :
    ContinuousOn (fun x => ownerPotential (H x) A (Matrix.diagonal (c x)) θ) D := by
  apply continuousOn_iff_continuous_restrict.mpr
  have hc' : Continuous (fun x : D => c x) := continuousOn_iff_continuous_restrict.mp hc
  have hH' : Continuous (fun x : D => H x) := continuousOn_iff_continuous_restrict.mp hH
  have hC : Continuous (fun x : D => Matrix.diagonal (c x)) := by
    apply continuous_matrix
    intro i j
    simp only [Matrix.diagonal_apply]
    split_ifs
    · exact (continuous_apply i).comp hc'
    · exact continuous_const
  have hp : Continuous (fun x : D => (H x,
      (⟨Matrix.diagonal (c x), Matrix.posSemidef_diagonal_iff.mpr (hpos x x.property)⟩ :
        {C : Matrix κ κ ℝ // C.PosSemidef}))) :=
    hH'.prodMk (hC.subtype_mk _)
  convert (continuous_ownerPotential_psd A hA θ).comp hp using 1

end MatrixSpencer.KSPotentialModels
