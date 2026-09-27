import MatrixSpencer.DyadicEpochTree
import MatrixSpencer.RectangularSigningPotential

/-! Lifting actual dyadic epochs with one fixed exponent, weight, and duration.
The explicitly quantified analytic input builder remains a premise here. -/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace MatrixSpencer
namespace DyadicPhasePotential
noncomputable section
universe u v
open PhaseRestriction
variable {ι : Type u} {n : Type v} [Fintype ι] [Fintype n]
  [DecidableEq ι] [DecidableEq n] [Nonempty n]
local instance dyadicPhasePotentialCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance dyadicPhasePotentialSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance

/-- Actual analytic preparation and mesh inputs on all coefficient types up to the original count.
Every nested restriction retains the same physical dimension and the same three parameters. -/
def HasEpochInputs (n : Type v) [Fintype n] [DecidableEq n] [Nonempty n]
    (m : ℕ) (θ B : ℝ) (N : ℕ) : Prop :=
  ∀ (κ : Type u) [Fintype κ] [DecidableEq κ] (cfg : DyadicEpochConfig κ n),
    cfg.depth = m → cfg.weight = θ → cfg.responseCoefficient = B →
    Fintype.card κ ≤ N → Nonempty (DyadicEpochAnalyticInputs cfg)

def epochConfig (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) (hθ : 0 < θ) (B : ℝ) (hB : 2 ≤ B)
    (offset : selfAdjoint (Matrix n n ℂ)) (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (hN : ∀ i, ‖A i‖ ≤ 1)
    (x : EuclideanSpace ℝ ι) (ε : ℝ) (hε : 0 < ε)
    (hsmall : (Fintype.card ι : ℝ) * ε ≤ 1 / 1000)
    (hx : CubeRegular ε x) (hlarge : 32 ≤ Fintype.card (Live x)) :
    DyadicEpochConfig (Live x) n where
  toEpochConfig := PhaseRestriction.epochConfig offset A hA hN x ε hε hsmall hx hlarge
  depth := m
  depth_positive := hm
  weight := θ
  weight_positive := hθ
  responseCoefficient := B
  response_large := hB

/-- The actual finite epoch is lifted to the original labels and charged to the
actual changing-live-family potential. Only the analytic input builder is conditional. -/
theorem exists_lifted_successful_epoch (m : ℕ) (hm : 1 ≤ m)
    (θ : ℝ) (hθ : 0 < θ) (B : ℝ) (hB : 2 ≤ B) (N : ℕ)
    (hinputs : HasEpochInputs.{u,v} n m θ B N)
    (offset : selfAdjoint (Matrix n n ℂ)) (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (hN : ∀ i, ‖A i‖ ≤ 1) (hcount : Fintype.card ι ≤ N)
    (x : EuclideanSpace ℝ ι) (ε : ℝ) (hε : 0 < ε)
    (hsmall : (Fintype.card ι : ℝ) * ε ≤ 1 / 1000) (hx : CubeRegular ε x)
    (hlarge : 32 ≤ Fintype.card (Live x)) :
    ∃ (z : EuclideanSpace ℝ ι) (time : ℝ), CubeRegular ε z ∧
      (∀ i ∈ frozenCoordinates x, z i = x i) ∧
      frozenCoordinates x ⊆ frozenCoordinates z ∧
      0 ≤ time ∧ time ≤ RectangularEpochParameters.duration B ∧
      ‖x‖ ^ 2 + (Fintype.card (Live x) : ℝ) / 16 * time ≤ ‖z‖ ^ 2 ∧
      (time = RectangularEpochParameters.duration B ∨ (Fintype.card (Live x) : ℝ) / 64 ≤
        ((frozenCoordinates z).card : ℝ) - (frozenCoordinates x).card) ∧
      rectangularRemainingPotential m θ offset A hA z -
        rectangularRemainingPotential m θ offset A hA x ≤
          22 * Real.sqrt (Fintype.card (Live x) : ℝ) := by
  let cfg := epochConfig m hm θ hθ B hB offset A hA hN x ε hε hsmall hx hlarge
  have hc : Fintype.card (Live x) ≤ N :=
    (Fintype.card_subtype_le (fun i => i ∉ frozenCoordinates x)).trans hcount
  obtain ⟨inputs⟩ := hinputs (Live x) cfg rfl rfl rfl hc
  obtain ⟨y, time, hy, ht0, ht1, hgain, hsuccess, hgrowth⟩ := exists_successful_dyadic_epoch cfg inputs
  refine ⟨liftPoint x y, time, liftPoint_regular hx hy,
    (fun i hi => liftPoint_frozen x y hi), frozen_subset_liftPoint x y,
    ht0, ht1, norm_gain_liftPoint x y _ hgain, ?_, ?_⟩
  · rw [frozen_card_gain_real]
    exact hsuccess
  · have hdrop := rectangularRemainingPotential_lift_le m θ offset A hA x y
    change rectangularRemainingPotential m θ offset A hA (liftPoint x y) ≤
      cfg.potential (cfg.center y) 1 at hdrop
    have hbase : cfg.potential cfg.anchor 1 = rectangularRemainingPotential m θ offset A hA x := by
      have hc := center_liftPoint offset A hA x (restrictPoint x)
      rw [liftPoint_restrictPoint] at hc
      change regularizedOwnerPotential
        (epochCenter (restrictedOffset offset A hA x) (restrictedFamily A x)
          (restrictedFamily_hermitian A hA x) (restrictPoint x)) (restrictedFamily A x) 1
          (dyadicTsallisRegularizer m θ) = _
      rw [← hc]
      rfl
    rw [hbase] at hgrowth
    linarith

end
end DyadicPhasePotential
end MatrixSpencer
