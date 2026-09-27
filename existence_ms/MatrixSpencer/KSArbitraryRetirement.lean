import MatrixSpencer.KSArbitraryTransportContact
import MatrixSpencer.KSOwnerRetirement

/-! Safe retirement in any fixed isometric source frame, including singular sources. -/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSArbitraryRetirement
open KSSafeRetirement
variable {ι κ n m : Type*} [Fintype ι] [Fintype κ] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m] [Nonempty n]
local instance : CStarAlgebra (Matrix n n ℂ) := {}

theorem retire_of_supported_matrix_le
    (H Hnew : Matrix n n ℂ) (B : ι → Matrix n n ℂ) (Bnew : κ → Matrix n n ℂ)
    (V : Matrix n m ℂ) (hV : Vᴴ * V = 1) {θ : ℝ} (hθ : 0 < θ)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (ht : realTrace (S : Matrix n n ℂ) = 1)
    (hmax : ∀ T ∈ densitySet, densityObjective H B θ T ≤ densityObjective H B θ S)
    {Z : Matrix m m ℂ} (hZ : Z.PosDef)
    (hM : (Vᴴ * krausChannel B S * V).PosDef)
    (hsolve : Z * (Vᴴ * krausChannel B S * V) * Z = Vᴴ * (S : Matrix n n ℂ) * V)
    (hsupport : ∀ X : Matrix n n ℂ, X.PosSemidef →
      V * (Vᴴ * krausChannel B X * V) * Vᴴ = krausChannel B X)
    (hnewSupport : ∀ X ∈ densitySet,
      V * (Vᴴ * krausChannel Bnew X * V) * Vᴴ = krausChannel Bnew X)
    (hle : Hnew + supportedGradient Bnew V Z ≤ H + supportedGradient B V Z) :
    densityPotential Hnew Bnew θ ≤ densityPotential H B θ := by
  have hu := densityPotential_le_supported Hnew Bnew V hV hZ θ hnewSupport
  exact hu.trans ((baseDensityPotential_mono hle θ).trans
    (KSArbitraryTransportContact.basePotential_contact H B V hV hθ S hS ht hmax
      hZ hM hsolve hsupport).le)

/-- Owner deletion in an arbitrary frame. Domination of the new source
proves support containment automatically. -/
theorem owner_retire_of_supported_matrix_le [DecidableEq ι]
    (H Hnew : Matrix n n ℂ) (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C Cnew : Matrix ι ι ℝ} (hC : C.PosSemidef) (hCnew : Cnew.PosSemidef) (hdel : Cnew ≤ C)
    (V : Matrix n m ℂ) (hV : Vᴴ * V = 1) {θ : ℝ} (hθ : 0 < θ)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (ht : realTrace (S : Matrix n n ℂ) = 1)
    (hmax : ∀ T ∈ densitySet,
      densityObjective H (covarianceKraus A C) θ T ≤ densityObjective H (covarianceKraus A C) θ S)
    {Z : Matrix m m ℂ} (hZ : Z.PosDef)
    (hM : (Vᴴ * krausChannel (covarianceKraus A C) S * V).PosDef)
    (hsolve : Z * (Vᴴ * krausChannel (covarianceKraus A C) S * V) * Z =
      Vᴴ * (S : Matrix n n ℂ) * V)
    (hsupport : ∀ X : Matrix n n ℂ, X.PosSemidef →
      V * (Vᴴ * krausChannel (covarianceKraus A C) X * V) * Vᴴ =
        krausChannel (covarianceKraus A C) X)
    (hmove : Hnew + covarianceSource A Cnew (V * Z * Vᴴ) ≤
      H + covarianceSource A C (V * Z * Vᴴ)) :
    ownerPotential Hnew A Cnew θ ≤ ownerPotential H A C θ := by
  rw [ownerPotential_eq_densityPotential Hnew A hA hCnew θ,
    ownerPotential_eq_densityPotential H A hA hC θ]
  apply retire_of_supported_matrix_le H Hnew (covarianceKraus A C) (covarianceKraus A Cnew)
    V hV hθ S hS ht hmax hZ hM hsolve hsupport
  · intro X hX
    have hdom : krausChannel (covarianceKraus A Cnew) X ≤ krausChannel (covarianceKraus A C) X := by
      rw [← covarianceSource_eq_kraus A hA hCnew, ← covarianceSource_eq_kraus A hA hC]
      exact covarianceSource_mono A hA hdel hX.1
    exact KSOwnerRetirement.support_reconstruct_of_le V hV
      (Vᴴ * krausChannel (covarianceKraus A C) X * V)
      (krausChannel_posSemidef _ hX.1) (by rwa [hsupport X hX.1])
  · change Hnew + (V * Z⁻¹ * Vᴴ + sourceAdjoint (covarianceKraus A Cnew) (V * Z * Vᴴ)) ≤
      H + (V * Z⁻¹ * Vᴴ + sourceAdjoint (covarianceKraus A C) (V * Z * Vᴴ))
    rw [KSOwnerRetirement.sourceAdjoint_covarianceKraus A hA hCnew,
      KSOwnerRetirement.sourceAdjoint_covarianceKraus A hA hC]
    convert add_le_add_right hmove (V * Z⁻¹ * Vᴴ) using 1 <;> abel

end MatrixSpencer.KSArbitraryRetirement
