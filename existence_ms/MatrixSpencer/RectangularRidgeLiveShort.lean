import MatrixSpencer.MSManuscriptNumericalEpochShort
import MatrixSpencer.CovarianceFaceDomination
import MatrixSpencer.CovarianceTraceLedger

/-!
# Shorting on a fixed original universe with a smaller live set

A stored owner annihilates coordinates frozen before this epoch. Scanning those
constraints again costs no trace. The actual scalar short therefore loses at
most one unit per newly frozen coordinate, plus one for the radial constraint.
-/
open Matrix
open scoped BigOperators MatrixOrder
noncomputable section
namespace MatrixSpencer.RectangularRidgeLiveShort
open MSManuscriptNumericalEpochShort
variable {N : ℕ}

/-- Original frozen annihilators are inherited by every smaller PSD covariance. -/
theorem annihilators_mono (C Q : Matrix (Fin N) (Fin N) ℝ) (hQ : Q.PosSemidef) (hQC : Q ≤ C)
    (F₀ : Finset (Fin N)) (hF₀ : ∀ i ∈ F₀, C *ᵥ Pi.single i 1 = 0) :
    ∀ i ∈ F₀, Q *ᵥ Pi.single i 1 = 0 := by
  intro i hi
  exact posSemidef_mulVec_eq_zero_of_le hQ hQC (hF₀ i hi)

/-- The actual ordered scalar short is unchanged after deleting constraints
already annihilated by its input. -/
theorem epoch_eq_sdiff (C : Matrix (Fin N) (Fin N) ℝ) (hC : C.PosSemidef)
    (F₀ F : Finset (Fin N)) (x : EuclideanSpace ℝ (Fin N))
    (hF₀ : ∀ i ∈ F₀, C *ᵥ Pi.single i 1 = 0) :
    epoch C F x = epoch C (F \ F₀) x := by
  apply le_antisymm
  · apply epoch_maximal C (epoch C F x) hC (epoch_posSemidef C hC F x) (epoch_le C hC F x)
    · intro i hi
      exact epoch_frozen C hC F x i (Finset.mem_sdiff.mp hi).1
    · exact epoch_radial C hC F x
  · apply epoch_maximal C (epoch C (F \ F₀) x) hC
      (epoch_posSemidef C hC (F \ F₀) x) (epoch_le C hC (F \ F₀) x)
    · intro i hi
      by_cases h0 : i ∈ F₀
      · exact annihilators_mono C (epoch C (F \ F₀) x)
          (epoch_posSemidef C hC (F \ F₀) x) (epoch_le C hC (F \ F₀) x) F₀ hF₀ i h0
      · exact epoch_frozen C hC (F \ F₀) x i (Finset.mem_sdiff.mpr ⟨hi, h0⟩)
    · exact epoch_radial C hC (F \ F₀) x

/-- Trace loss counts newly frozen labels in the original index type. -/
theorem epoch_trace_lower (C : Matrix (Fin N) (Fin N) ℝ) (hC : C.PosSemidef) (hC1 : C ≤ 1)
    (F₀ F : Finset (Fin N)) (x : EuclideanSpace ℝ (Fin N))
    (hF₀ : ∀ i ∈ F₀, C *ᵥ Pi.single i 1 = 0) :
    realTrace C - ((F \ F₀).card : ℝ) - 1 ≤ realTrace (epoch C F x) := by
  rw [epoch_eq_sdiff C hC F₀ F x hF₀]
  exact MSManuscriptNumericalEpochShort.epoch_trace_lower C hC hC1 (F \ F₀) x

/-- The live count is independent of the ambient covariance dimension. -/
theorem trace_positive_of_ledger (C : Matrix (Fin N) (Fin N) ℝ)
    (hC : C.PosSemidef) (hC1 : C ≤ 1) (F₀ F : Finset (Fin N))
    (x : EuclideanSpace ℝ (Fin N)) (ℓ dc : ℝ) (hℓ : 32 ≤ ℓ)
    (hF₀ : ∀ i ∈ F₀, C *ᵥ Pi.single i 1 = 0)
    (htrace : ℓ / 8 - dc ≤ realTrace C) (hdc : dc ≤ ℓ / 64)
    (hF : ((F \ F₀).card : ℝ) ≤ ℓ / 64) :
    ℓ / 16 ≤ realTrace (epoch C F x) ∧ 0 < realTrace (epoch C F x) := by
  apply movement_trace_positive_of_ledger hℓ hdc hF
  have ht := epoch_trace_lower C hC hC1 F₀ F x hF₀
  linarith

end MatrixSpencer.RectangularRidgeLiveShort
