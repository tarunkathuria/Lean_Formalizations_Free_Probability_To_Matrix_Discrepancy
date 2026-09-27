import MatrixSpencer.OwnerShavingDerivative
import MatrixSpencer.OwnerCertificate
import MatrixSpencer.RectangularRidgeOwnerShavingDerivative
import MatrixSpencer.RectangularRidgeCertificate
import MatrixSpencer.MSManuscriptAnchorDensity



open Matrix Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace FaithfulMS.DirectDensity
open MatrixSpencer

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n]
local instance : CStarAlgebra (Matrix n n ℂ) := {}

/-- The square SDP service's mathematical postcondition: feasibility and
optimality, with no response or stability hypothesis. -/
structure SquareSolution (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ)
    (C : Matrix ι ι ℝ) (θ : ℝ) where
  density : Matrix n n ℂ
  feasible : density ∈ densitySet
  maximizing : ∀ T ∈ densitySet, densityObjective H (covarianceKraus A C) θ T ≤
    densityObjective H (covarianceKraus A C) θ density

/-- The rectangular service maximizes the actual power-plus-ridge objective. -/
structure RectangularSolution (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ)
    (C : Matrix ι ι ℝ) (m : ℕ) (θ κ : ℝ) where
  density : Matrix n n ℂ
  feasible : density ∈ densitySet
  maximizing : ∀ T ∈ densitySet,
    RectangularRidgePotential.objective H (covarianceKraus A C) m θ κ T ≤
      RectangularRidgePotential.objective H (covarianceKraus A C) m θ κ density

/-- Explicit density-to-covariance report: compress the physical source,
solve the transport equation by square roots, extend by zero, and pair the
result against the atoms. No objective-value differences occur here. -/
def gamma (A : ι → Matrix n n ℂ) (C : Matrix ι ι ℝ)
    (S : Matrix n n ℂ) : Matrix ι ι ℝ :=
  RectangularRidgeOwnerFrame.ownedGram A C S

theorem gamma_formula (A : ι → Matrix n n ℂ) (C : Matrix ι ι ℝ)
    (S : Matrix n n ℂ) :
    gamma A C S = covarianceGram A S
      (krausSupportEmbedding (covarianceKraus A C) *
        transportOptimizer (krausCompressedDensity (covarianceKraus A C) S)
          (krausChannel (krausReducedFamily (covarianceKraus A C))
            (krausCompressedDensity (covarianceKraus A C) S)) *
        (krausSupportEmbedding (covarianceKraus A C))ᴴ) := rfl

theorem gamma_posSemidef (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (C : Matrix ι ι ℝ)
    {S : Matrix n n ℂ} (hS : S.PosDef) : (gamma A C S).PosSemidef :=
  covarianceGram_posSemidef A hA _ _ hS.posSemidef
    ((RectangularRidgeOwnerFrame.sourceTransport_posDef A hA C hS).posSemidef.mul_mul_conjTranspose_same _)

variable [Nonempty n]

theorem SquareSolution.density_eq_optimizer
    {H : Matrix n n ℂ} {A : ι → Matrix n n ℂ} {C : Matrix ι ι ℝ}
    {θ : ℝ} (p : SquareSolution H A C θ) (hθ : 0 < θ) :
    p.density = densityOptimizer H (covarianceKraus A C) θ :=
  (strictConcaveOn_densityObjective H (covarianceKraus A C) hθ).eq_of_isMaxOn
    p.maximizing (densityOptimizer_isMaxOn H (covarianceKraus A C) θ)
    p.feasible (densityOptimizer_mem H (covarianceKraus A C) θ)

theorem RectangularSolution.density_eq_optimizer
    {H : Matrix n n ℂ} {A : ι → Matrix n n ℂ} {C : Matrix ι ι ℝ}
    {m : ℕ} {θ κ : ℝ} (p : RectangularSolution H A C m θ κ)
    (hm : 1 ≤ m) (hθ : 0 < θ) (hκ : 0 ≤ κ) :
    p.density = RectangularRidgePotential.optimizer H (covarianceKraus A C) m θ κ :=
  RectangularRidgePotential.maximizers_eq H (covarianceKraus A C) hm hθ hκ
    p.feasible (RectangularRidgePotential.optimizer_mem H (covarianceKraus A C) m θ κ)
    p.maximizing (RectangularRidgePotential.optimizer_max H (covarianceKraus A C) m θ κ)

theorem SquareSolution.gamma_eq
    (H : selfAdjoint (Matrix n n ℂ)) {A : ι → Matrix n n ℂ}
    {C : Matrix ι ι ℝ} {θ : ℝ}
    (p : SquareSolution (H : Matrix n n ℂ) A C θ) (hθ : 0 < θ) :
    gamma A C p.density = observedOwnedGram H A C θ := by
  rw [p.density_eq_optimizer hθ]
  rfl

/-- The directly computed report is the derivative of the optimized square
potential in every supported covariance direction of rank one. -/
theorem SquareSolution.gamma_derivative
    (H : selfAdjoint (Matrix n n ℂ)) {A : ι → Matrix n n ℂ}
    (hA : ∀ i, (A i).IsHermitian) {C : Matrix ι ι ℝ} (hC : C.PosSemidef)
    {θ : ℝ} (p : SquareSolution (H : Matrix n n ℂ) A C θ) (hθ : 0 < θ)
    (u : EuclideanSpace ℝ ι)
    (hu : u ∈ LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℝ) C).toLinearMap) :
    HasDerivAt (fun t : ℝ => ownerPotential (H : Matrix n n ℂ) A
      (C - t • realRankOne (WithLp.ofLp u)) θ)
      (-(WithLp.ofLp u ⬝ᵥ (gamma A C p.density *ᵥ WithLp.ofLp u))) 0 := by
  rw [p.gamma_eq H hθ]
  exact hasDerivAt_ownerPotential_supported_shave H A hA hC u hu hθ

/-- The same computation serves the rectangular potential; only the density
objective solved by the service changes. -/
theorem RectangularSolution.gamma_derivative
    (H : selfAdjoint (Matrix n n ℂ)) {A : ι → Matrix n n ℂ}
    (hA : ∀ i, (A i).IsHermitian) {C : Matrix ι ι ℝ} (hC : C.PosSemidef)
    {m : ℕ} {θ κ : ℝ} (p : RectangularSolution (H : Matrix n n ℂ) A C m θ κ)
    (hm : 1 ≤ m) (hθ : 0 < θ) (hκ : 0 < κ)
    (u : EuclideanSpace ℝ ι)
    (hu : u ∈ LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℝ) C).toLinearMap) :
    HasDerivAt (fun t : ℝ => regularizedOwnerPotential (H : Matrix n n ℂ) A
      (C - t • realRankOne (WithLp.ofLp u))
        (RectangularRidgeCovarianceCalculus.regularizer m θ κ))
      (-(WithLp.ofLp u ⬝ᵥ (gamma A C p.density *ᵥ WithLp.ofLp u))) 0 := by
  rw [p.density_eq_optimizer hm hθ hκ.le]
  exact hasDerivAt_ridgeOwnerPotential_supported_shave H A hA hC u hu m hm θ κ hθ hκ

/-- Reading the objective at the returned primal density gives its exact
potential value; no independent potential oracle is needed. -/
theorem SquareSolution.value_eq
    {H : Matrix n n ℂ} {A : ι → Matrix n n ℂ} {C : Matrix ι ι ℝ} {θ : ℝ}
    (p : SquareSolution H A C θ) :
    densityObjective H (covarianceKraus A C) θ p.density =
      densityPotential H (covarianceKraus A C) θ :=
  (densityPotential_eq_of_maximizer H (covarianceKraus A C) θ
    p.feasible p.maximizing).symm

theorem RectangularSolution.value_eq
    {H : Matrix n n ℂ} {A : ι → Matrix n n ℂ} {C : Matrix ι ι ℝ}
    {m : ℕ} {θ κ : ℝ} (p : RectangularSolution H A C m θ κ) :
    RectangularRidgePotential.objective H (covarianceKraus A C) m θ κ p.density =
      RectangularRidgePotential.potential H (covarianceKraus A C) m θ κ :=
  (RectangularRidgePotential.potential_eq_of_maximizer H (covarianceKraus A C)
    m θ κ p.feasible p.maximizing).symm

theorem SquareSolution.owner_value_eq
    {H : Matrix n n ℂ} {A : ι → Matrix n n ℂ} {C : Matrix ι ι ℝ} {θ : ℝ}
    (p : SquareSolution H A C θ) (hA : ∀ i, (A i).IsHermitian) (hC : C.PosSemidef) :
    ownerObjective H A C θ p.density = ownerPotential H A C θ := by
  rw [ownerObjective_eq_densityObjective H A hA hC,
    ownerPotential_eq_densityPotential H A hA hC]
  exact p.value_eq

theorem RectangularSolution.owner_value_eq
    {H : Matrix n n ℂ} {A : ι → Matrix n n ℂ} {C : Matrix ι ι ℝ}
    {m : ℕ} {θ κ : ℝ} (p : RectangularSolution H A C m θ κ)
    (hA : ∀ i, (A i).IsHermitian) (hC : C.PosSemidef) :
    RectangularRidgeCovarianceCalculus.ownerObjective m H A C θ κ p.density =
      RectangularRidgeCovarianceCalculus.ownerPotential m H A C θ κ := by
  rw [RectangularRidgeCovarianceCalculus.ownerObjective_eq_densityObjective m H A hA hC,
    RectangularRidgeCovarianceCalculus.ownerPotential_eq_densityPotential m H A hA hC]
  exact p.value_eq

/-- A source-free optimizing-density call returns exactly the density saved
by the square walk's mathematical supporting certificate. -/
theorem SquareSolution.saved_density_eq
    {H : Matrix n n ℂ} {θ : ℝ}
    (p : SquareSolution H (fun _ : Empty => (0 : Matrix n n ℂ)) 0 θ)
    (hθ : 0 < θ) : p.density = ownerCertificateDensity H θ := by
  rw [p.density_eq_optimizer hθ]
  congr 1

theorem RectangularSolution.saved_density_eq
    {H : Matrix n n ℂ} {m : ℕ} {θ κ : ℝ}
    (p : RectangularSolution H (fun _ : Empty => (0 : Matrix n n ℂ)) 0 m θ κ)
    (hm : 1 ≤ m) (hθ : 0 < θ) (hκ : 0 ≤ κ) :
    p.density = RectangularRidgeCertificate.density H m θ κ := by
  rw [p.density_eq_optimizer hm hθ hκ]
  congr 1

/-- A primal density at the source-free center directly gives the supporting
plane used for epoch acceptance. -/
theorem square_supporting_plane {H : Matrix n n ℂ} {θ : ℝ}
    (S : Matrix n n ℂ) (hS : S ∈ densitySet)
    (hmax : ∀ T ∈ densitySet,
      densityObjective H (fun _ : Empty => (0 : Matrix n n ℂ)) θ T ≤
        densityObjective H (fun _ : Empty => (0 : Matrix n n ℂ)) θ S)
    (D : Matrix n n ℂ) :
    baseDensityPotential H θ + realTrace (S * D) ≤ baseDensityPotential (H + D) θ := by
  have h := densityPotential_supporting_plane H (H + D)
    (fun _ : Empty => (0 : Matrix n n ℂ)) θ hS hmax
  simpa only [add_sub_cancel_left, realTrace_mul_comm S D] using h

/-- Distance-accurate primal densities also give accurate saved-plane reports,
independently of how that density accuracy is obtained by the SDP service. -/
theorem supporting_plane_report_error {d : ℕ} (S T D : Matrix (Fin d)
    (Fin d) ℂ) (hS : S.IsHermitian) (hT : T.IsHermitian)
    (hD : D.IsHermitian) {e : ℝ}
    (herr : Real.sqrt (KSOwnerInputBounds.matrixEnergy (S - T)) ≤ e) :
    |realTrace (S * D) - realTrace (T * D)| ≤
      e * Real.sqrt (KSOwnerInputBounds.matrixEnergy D) := by
  rw [← realTrace_sub, ← Matrix.sub_mul]
  exact (MSManuscriptAnchorDensity.trace_pairing_bound (S - T) D (hS.sub hT) hD).trans
    (mul_le_mul_of_nonneg_right herr (Real.sqrt_nonneg _))

end FaithfulMS.DirectDensity
