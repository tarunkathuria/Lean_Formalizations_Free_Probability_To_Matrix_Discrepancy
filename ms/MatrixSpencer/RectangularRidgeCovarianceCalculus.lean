import MatrixSpencer.CovarianceCalculus
import MatrixSpencer.RectangularRidgePotentialResponse

/-! Joint covariance/density calculus of the actual mixed objective. The
coefficient covariance is positive on its stored face; physical Kraus sources
may have any rank. Both regularizers are independent of covariance. -/
open Matrix Filter Topology
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
noncomputable section
namespace MatrixSpencer.RectangularRidgeCovarianceCalculus
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n]
local instance : CStarAlgebra (Matrix n n ℂ) := {}
local instance : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance
local instance : NormedSpace ℝ (selfAdjoint (Matrix ι ι ℝ)) := inferInstance

def regularizer (m : ℕ) (θ κ : ℝ) (S : Matrix n n ℂ) : ℝ :=
  dyadicTsallisRegularizer m θ S + 2 * κ * realTrace (CFC.sqrt S)

def ownerObjective (m : ℕ) (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ)
    (C : Matrix ι ι ℝ) (θ κ : ℝ) (S : Matrix n n ℂ) : ℝ :=
  regularizedOwnerObjective H A C (regularizer m θ κ) S

def ownerPotential (m : ℕ) (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ)
    (C : Matrix ι ι ℝ) (θ κ : ℝ) : ℝ :=
  regularizedOwnerPotential H A C (regularizer m θ κ)

theorem ownerObjective_eq_densityObjective (m : ℕ) (H : Matrix n n ℂ)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (θ κ : ℝ) (S : Matrix n n ℂ) :
    ownerObjective m H A C θ κ S =
      RectangularRidgePotential.objective H (covarianceKraus A C) m θ κ S := by
  unfold ownerObjective regularizer regularizedOwnerObjective RectangularRidgePotential.objective
    dyadicDensityObjective
  rw [covarianceSource_eq_kraus A hA hC]
  ring

theorem ownerPotential_eq_densityPotential (m : ℕ) (H : Matrix n n ℂ)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (θ κ : ℝ) :
    ownerPotential m H A C θ κ = RectangularRidgePotential.potential H (covarianceKraus A C) m θ κ := by
  unfold ownerPotential regularizedOwnerPotential RectangularRidgePotential.potential
  congr 2
  funext S
  exact ownerObjective_eq_densityObjective m H A hA hC θ κ S

def jointOwnerObjective (m : ℕ) (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ) (θ κ : ℝ)
    (P : selfAdjoint (Matrix ι ι ℝ) × selfAdjoint (Matrix n n ℂ)) : ℝ :=
  ownerObjective m H A P.1 θ κ P.2

theorem contDiffAt_jointOwnerObjective (m : ℕ) (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (θ κ : ℝ)
    (C : selfAdjoint (Matrix ι ι ℝ)) (S : selfAdjoint (Matrix n n ℂ))
    (hC : (C : Matrix ι ι ℝ).PosDef) (hS : (S : Matrix n n ℂ).PosDef) :
    ContDiffAt ℝ ∞ (jointOwnerObjective m H A θ κ) (C, S) := by
  have ht : ContDiffAt ℝ ∞ (fun P : selfAdjoint (Matrix ι ι ℝ) × selfAdjoint (Matrix n n ℂ) =>
      dyadicTsallisPotential m θ P.2) (C, S) :=
    ContDiffAt.comp (g := dyadicTsallisPotential m θ) (f := Prod.snd) (C, S)
      (contDiffAt_dyadicTsallisPotential m θ S hS) contDiffAt_snd
  have hr : ContDiffAt ℝ ∞ (fun P : selfAdjoint (Matrix ι ι ℝ) × selfAdjoint (Matrix n n ℂ) =>
      tsallisPotential κ P.2) (C, S) :=
    ContDiffAt.comp (g := tsallisPotential κ) (f := Prod.snd) (C, S)
      (contDiffAt_tsallisPotential κ S hS) contDiffAt_snd
  have hl : ContDiffAt ℝ ∞ (fun P : selfAdjoint (Matrix ι ι ℝ) × selfAdjoint (Matrix n n ℂ) =>
      tracePairing H P.2) (C, S) :=
    (tracePairing H).contDiff.contDiffAt.comp (C, S) contDiffAt_snd
  exact (hl.add (contDiffAt_covarianceFidelity A hA C S hC hS)).add (ht.add hr)

theorem hasStrictFDerivAt_ownerObjective_covariance (m : ℕ)
    (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) (θ κ : ℝ)
    (C : selfAdjoint (Matrix ι ι ℝ)) (S : selfAdjoint (Matrix n n ℂ))
    (hC : (C : Matrix ι ι ℝ).PosDef) (hS : (S : Matrix n n ℂ).PosDef) :
    HasStrictFDerivAt (fun K : selfAdjoint (Matrix ι ι ℝ) => ownerObjective m H A K θ κ S)
      (covarianceDerivativeFunctional A C S) C := by
  have hf := ((hasStrictFDerivAt_const (𝕜 := ℝ) (realTrace (H * (S : Matrix n n ℂ))) C).add
    (hasStrictFDerivAt_covarianceFidelity_covariance A hA C S hC hS)).add
      (hasStrictFDerivAt_const (𝕜 := ℝ) (regularizer (n := n) m θ κ (S : Matrix n n ℂ)) C)
  simpa only [zero_add, add_zero] using hf

end MatrixSpencer.RectangularRidgeCovarianceCalculus
