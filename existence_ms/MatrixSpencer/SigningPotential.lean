import MatrixSpencer.PhaseRestriction
import MatrixSpencer.SquareConclusion

/-! Fixed rounding tolerance, initial potential, and final norm extraction for
the actual remaining-coordinate potential. -/

open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix
noncomputable section
namespace MatrixSpencer
open PhaseRestriction

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n]
local instance signingPotentialCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance signingPotentialSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance

def signingEpsilon (ι : Type*) [Fintype ι] : ℝ := 1 / (1000 * ((Fintype.card ι : ℝ) + 1))

theorem signingEpsilon_pos : 0 < signingEpsilon ι := by
  unfold signingEpsilon
  positivity

theorem signingEpsilon_le_small : signingEpsilon ι ≤ 1 / 1000 := by
  unfold signingEpsilon
  have hk : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 1000 * ((Fintype.card ι : ℝ) + 1))).mpr
  nlinarith

theorem signingEpsilon_count_small : (Fintype.card ι : ℝ) * signingEpsilon ι ≤ 1 / 1000 := by
  unfold signingEpsilon
  have hk : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  rw [mul_one_div]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 1000 * ((Fintype.card ι : ℝ) + 1))).mpr
  nlinarith

theorem signing_zero_regular : CubeRegular (signingEpsilon ι) (0 : EuclideanSpace ℝ ι) := by
  constructor
  · intro i
    simp
  · intro i
    right
    have h := signingEpsilon_le_small (ι := ι)
    simpa only [PiLp.zero_apply, abs_zero] using (show (0 : ℝ) < 1 - signingEpsilon ι by linarith)

theorem epochCenter_zero_zero (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) :
    epochCenter 0 A hA (0 : EuclideanSpace ℝ ι) = 0 := by
  simp [epochCenter]

/-- A zero live count means every original coordinate is assigned a real sign. -/
theorem full_signs_of_live_card_zero (x : EuclideanSpace ℝ ι) (hx : Fintype.card (Live x) = 0) :
    ∀ i, IsSign (x i) := by
  classical
  haveI : IsEmpty (Live x) := Fintype.card_eq_zero_iff.mp hx
  intro i
  by_contra hi
  exact isEmptyElim (⟨i, fun h => hi ((mem_frozenCoordinates x i).mp h)⟩ : Live x)

/-- The remaining covariance always dominates the same fixed base regularizer. -/
theorem base_le_remainingPotential [Nonempty n] (offset : selfAdjoint (Matrix n n ℂ))
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) (x : EuclideanSpace ℝ ι) :
    baseDensityPotential (epochCenter offset A hA x : Matrix n n ℂ) 1 ≤ remainingPotential offset A hA x :=
  baseDensityPotential_le_owner (epochCenter offset A hA x : Matrix n n ℂ)
    (restrictedFamily A x) (restrictedFamily_hermitian A hA x) Matrix.PosSemidef.one 1

/-- The initial actual live-family potential has the same dimension/count bound. -/
theorem remainingPotential_zero_le_five [Nonempty n]
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) (hN : ∀ i, ‖A i‖ ≤ 1)
    (hd : Fintype.card n ≤ 2 * Fintype.card ι) :
    remainingPotential 0 A hA (0 : EuclideanSpace ℝ ι) ≤ 5 * Real.sqrt (Fintype.card ι : ℝ) := by
  have hcard : Fintype.card (Live (0 : EuclideanSpace ℝ ι)) = Fintype.card ι := by
    rw [live_card]
    have hz : frozenCoordinates (0 : EuclideanSpace ℝ ι) = ∅ := by
      ext i
      simp [mem_frozenCoordinates, IsSign]
    simp [hz]
  unfold remainingPotential
  rw [epochCenter_zero_zero]
  have hb := ownerPotential_initial_le_five (restrictedFamily A (0 : EuclideanSpace ℝ ι))
    (restrictedFamily_hermitian A hA _) (restrictedFamily_contractions A hN _)
    (by simpa only [hcard] using hd)
  simpa only [hcard] using hb

end MatrixSpencer
