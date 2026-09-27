import MatrixSpencer.CovarianceCalculus
import MatrixSpencer.DyadicCoefficientResponse

/-! Joint covariance/density calculus for the actual dyadic objective.
The covariance source and its fixed-support differential are reused unchanged;
only the actual additive dyadic regularizer is substituted. -/

open Matrix Filter Topology
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff

namespace MatrixSpencer
namespace DyadicCovarianceCalculus
noncomputable section
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n]
local instance dyadicCovarianceCalculusCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance dyadicCovarianceCalculusPhysicalSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance
local instance dyadicCovarianceCalculusCoeffSpace : NormedSpace ℝ (selfAdjoint (Matrix ι ι ℝ)) := inferInstance

def ownerObjective (m : ℕ) (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ)
    (C : Matrix ι ι ℝ) (θ : ℝ) (S : Matrix n n ℂ) : ℝ :=
  regularizedOwnerObjective H A C (dyadicTsallisRegularizer m θ) S

def ownerPotential (m : ℕ) (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ)
    (C : Matrix ι ι ℝ) (θ : ℝ) : ℝ :=
  regularizedOwnerPotential H A C (dyadicTsallisRegularizer m θ)

theorem ownerObjective_eq_densityObjective (m : ℕ) (H : Matrix n n ℂ)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (θ : ℝ) (S : Matrix n n ℂ) :
    ownerObjective m H A C θ S = dyadicDensityObjective H (covarianceKraus A C) m θ S :=
  regularizedOwnerObjective_eq_dyadicDensityObjective H A hA hC m θ S

theorem ownerPotential_eq_densityPotential (m : ℕ) (H : Matrix n n ℂ)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (θ : ℝ) :
    ownerPotential m H A C θ = dyadicDensityPotential H (covarianceKraus A C) m θ :=
  regularizedOwnerPotential_eq_dyadicDensityPotential H A hA hC m θ

def jointOwnerObjective (m : ℕ) (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ) (θ : ℝ)
    (P : selfAdjoint (Matrix ι ι ℝ) × selfAdjoint (Matrix n n ℂ)) : ℝ :=
  ownerObjective m H A P.1 θ P.2

theorem contDiffAt_jointOwnerObjective (m : ℕ) (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (θ : ℝ)
    (C : selfAdjoint (Matrix ι ι ℝ)) (S : selfAdjoint (Matrix n n ℂ))
    (hC : (C : Matrix ι ι ℝ).PosDef) (hS : (S : Matrix n n ℂ).PosDef) :
    ContDiffAt ℝ ∞ (jointOwnerObjective m H A θ) (C, S) := by
  have ht : ContDiffAt ℝ ∞ (fun P : selfAdjoint (Matrix ι ι ℝ) × selfAdjoint (Matrix n n ℂ) =>
      dyadicTsallisPotential m θ P.2) (C, S) :=
    ContDiffAt.comp (g := dyadicTsallisPotential m θ) (f := Prod.snd) (C, S)
      (contDiffAt_dyadicTsallisPotential m θ S hS) contDiffAt_snd
  have hl : ContDiffAt ℝ ∞ (fun P : selfAdjoint (Matrix ι ι ℝ) × selfAdjoint (Matrix n n ℂ) =>
      tracePairing H P.2) (C, S) :=
    (tracePairing H).contDiff.contDiffAt.comp (C, S) contDiffAt_snd
  exact (hl.add (contDiffAt_covarianceFidelity A hA C S hC hS)).add ht

theorem hasStrictFDerivAt_ownerObjective_covariance (m : ℕ)
    (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) (θ : ℝ)
    (C : selfAdjoint (Matrix ι ι ℝ)) (S : selfAdjoint (Matrix n n ℂ))
    (hC : (C : Matrix ι ι ℝ).PosDef) (hS : (S : Matrix n n ℂ).PosDef) :
    HasStrictFDerivAt (fun K : selfAdjoint (Matrix ι ι ℝ) => ownerObjective m H A K θ S)
      (covarianceDerivativeFunctional A C S) C := by
  have hf := ((hasStrictFDerivAt_const (𝕜 := ℝ) (realTrace (H * (S : Matrix n n ℂ))) C).add
    (hasStrictFDerivAt_covarianceFidelity_covariance A hA C S hC hS)).add
    (hasStrictFDerivAt_const (𝕜 := ℝ) (dyadicTsallisPotential m θ S) C)
  simpa only [zero_add, add_zero] using hf

theorem fderiv_ownerObjective_covariance_apply (m : ℕ)
    (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) (θ : ℝ)
    (C ΔC : selfAdjoint (Matrix ι ι ℝ)) (S : selfAdjoint (Matrix n n ℂ))
    (hC : (C : Matrix ι ι ℝ).PosDef) (hS : (S : Matrix n n ℂ).PosDef) :
    fderiv ℝ (fun K : selfAdjoint (Matrix ι ι ℝ) => ownerObjective m H A K θ S) C ΔC =
      realTrace (covarianceSupportTransport A C S * covarianceSource A ΔC S) := by
  rw [(hasStrictFDerivAt_ownerObjective_covariance m H A hA θ C S hC hS).hasFDerivAt.fderiv]
  exact covarianceDerivativeFunctional_apply A hA C ΔC S

end
end DyadicCovarianceCalculus
end MatrixSpencer
