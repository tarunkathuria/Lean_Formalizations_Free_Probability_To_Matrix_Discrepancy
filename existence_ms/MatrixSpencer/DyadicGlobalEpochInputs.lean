import MatrixSpencer.DyadicActualEpoch
import MatrixSpencer.DyadicGlobalResponseBudget
import MatrixSpencer.DyadicPhasePotential

/-! The globally fixed coefficient supplies every actual epoch under every label restriction. -/
namespace MatrixSpencer
noncomputable section
universe u v

/-- This is the proved builder required by the finite phase assembly. The
coefficient is explicit; there is no analytic or epoch-existence hypothesis. -/
theorem hasEpochInputs_globalCoefficient (n : Type v) [Fintype n] [DecidableEq n] [Nonempty n]
    (m : ℕ) (θ : ℝ) (N : ℕ) :
    DyadicPhasePotential.HasEpochInputs.{u,v} n m θ
      (DyadicGlobalResponseBudget.globalCoefficient m θ (N : ℝ)) N := by
  intro κ _ _ cfg hm hθ hB hcount
  apply Nonempty.intro
  apply dyadicEpochAnalyticInputs cfg
  apply DyadicGlobalResponseBudget.hasResponseBudget_of_original_count cfg N hcount
  rw [hm, hθ, hB]

end
end MatrixSpencer
