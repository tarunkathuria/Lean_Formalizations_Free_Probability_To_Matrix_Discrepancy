import MatrixSpencer.KSArbitraryRetirement
import MatrixSpencer.KSStateRetirement

/-! Actual unit-cube retirement tests for any valid fixed support transport. -/

open Matrix Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSSpinChosenRetirement
open KSPotentialModels KSSafeRetirement KSEndpointRetirement KSRankOne

variable {ι n m : Type*} [Fintype ι] [Fintype n] [Fintype m]
  [DecidableEq ι] [DecidableEq n] [DecidableEq m] [Nonempty n]
local instance {k : Type*} [Fintype k] [DecidableEq k] : CStarAlgebra (Matrix k k ℂ) := {}

theorem spin_retire_in_frame
    (H : Matrix (n ⊕ n) (n ⊕ n) ℂ) (v : ι → n → ℂ)
    (c : ι → ℝ) (hc : ∀ j, 0 ≤ c j) (V : Matrix (n ⊕ n) m ℂ)
    (hV : Vᴴ * V = 1) {θ : ℝ} (hθ : 0 < θ)
    (S : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ))
    (hS : (S : Matrix (n ⊕ n) (n ⊕ n) ℂ).PosDef)
    (ht : realTrace (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) = 1)
    (hmax : ∀ T ∈ densitySet,
      densityObjective H (covarianceKraus (KSSpinSource.family (fun j => atom (v j)))
        (KSSpinSource.coefficientCovariance c)) θ T ≤
      densityObjective H (covarianceKraus (KSSpinSource.family (fun j => atom (v j)))
        (KSSpinSource.coefficientCovariance c)) θ S)
    {Z : Matrix m m ℂ} (hZ : Z.PosDef)
    (hM : (Vᴴ * covarianceSource (KSSpinSource.family (fun j => atom (v j)))
      (KSSpinSource.coefficientCovariance c) S * V).PosDef)
    (hsolve : Z * (Vᴴ * covarianceSource (KSSpinSource.family (fun j => atom (v j)))
      (KSSpinSource.coefficientCovariance c) S * V) * Z =
        Vᴴ * (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) * V)
    (hsupport : ∀ X : Matrix (n ⊕ n) (n ⊕ n) ℂ, X.PosSemidef →
      V * (Vᴴ * covarianceSource (KSSpinSource.family (fun j => atom (v j)))
        (KSSpinSource.coefficientCovariance c) X * V) * Vᴴ =
        covarianceSource (KSSpinSource.family (fun j => atom (v j)))
          (KSSpinSource.coefficientCovariance c) X)
    (i : ι) (δ : ℝ)
    (hsafe : |δ| ≤ c i * realTrace (KSSpinSource.doubled (atom (v i)) * (V * Z * Vᴴ))) :
    ownerPotential (H + δ • signedLift (atom (v i)))
      (KSSpinSource.family (fun j => atom (v j)))
      (KSSpinSource.coefficientCovariance (Function.update c i 0)) θ ≤
    ownerPotential H (KSSpinSource.family (fun j => atom (v j)))
      (KSSpinSource.coefficientCovariance c) θ := by
  have hA := KSSpinSource.family_isHermitian (fun j => atom (v j)) (fun j => atom_isHermitian _)
  have hC := KSSpinSource.coefficientCovariance_posSemidef hc
  have he (X : Matrix (n ⊕ n) (n ⊕ n) ℂ) := covarianceSource_eq_kraus _ hA hC X
  apply KSArbitraryRetirement.owner_retire_of_supported_matrix_le H _ _ hA hC
    (KSSpinSource.coefficientCovariance_posSemidef (update_zero_nonneg hc i))
    (spin_covariance_delete_le c hc i) V hV hθ S hS ht hmax hZ
  · simpa only [← he] using hM
  · simpa only [← he] using hsolve
  · intro X hX
    simpa only [← he] using hsupport X hX
  · rw [spin_source_delete v c i (Matrix.isHermitian_mul_mul_conjTranspose V hZ.isHermitian)]
    have hstep := spin_step_le (atom_posSemidef (v i)) hsafe
    have hsum := add_le_add_left (sub_nonpos.mpr hstep)
      (H + covarianceSource (KSSpinSource.family (fun j => atom (v j)))
        (KSSpinSource.coefficientCovariance c) (V * Z * Vᴴ))
    simp only [add_zero] at hsum
    convert hsum using 1 <;> abel

variable {N : ℕ}

theorem maxFrozen_noSafe_in_frame
    (v : Fin N → n → ℂ) {θ : ℝ} (hθ : 0 < θ) {x : Fin N → ℝ}
    (hx : MaxFrozenMinimum 1 (spinPotential (fun j => atom (v j)) θ) x)
    (V : Matrix (n ⊕ n) m ℂ) (hV : Vᴴ * V = 1)
    (S : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ))
    (hS : (S : Matrix (n ⊕ n) (n ⊕ n) ℂ).PosDef)
    (ht : realTrace (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) = 1)
    (hmax : ∀ T ∈ densitySet,
      densityObjective (signedLift (center (fun j => atom (v j)) x))
        (covarianceKraus (KSSpinSource.family (fun j => atom (v j)))
          (KSSpinSource.coefficientCovariance (naturalOwners 64 x))) θ T ≤
      densityObjective (signedLift (center (fun j => atom (v j)) x))
        (covarianceKraus (KSSpinSource.family (fun j => atom (v j)))
          (KSSpinSource.coefficientCovariance (naturalOwners 64 x))) θ S)
    {Z : Matrix m m ℂ} (hZ : Z.PosDef)
    (hM : (Vᴴ * covarianceSource (KSSpinSource.family (fun j => atom (v j)))
      (KSSpinSource.coefficientCovariance (naturalOwners 64 x)) S * V).PosDef)
    (hsolve : Z * (Vᴴ * covarianceSource (KSSpinSource.family (fun j => atom (v j)))
      (KSSpinSource.coefficientCovariance (naturalOwners 64 x)) S * V) * Z =
        Vᴴ * (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) * V)
    (hsupport : ∀ X : Matrix (n ⊕ n) (n ⊕ n) ℂ, X.PosSemidef →
      V * (Vᴴ * covarianceSource (KSSpinSource.family (fun j => atom (v j)))
        (KSSpinSource.coefficientCovariance (naturalOwners 64 x)) X * V) * Vᴴ =
        covarianceSource (KSSpinSource.family (fun j => atom (v j)))
          (KSSpinSource.coefficientCovariance (naturalOwners 64 x)) X)
    (i : Fin N) (hi : |x i| < 1) :
    naturalOwners 64 x i * realTrace (KSSpinSource.doubled (atom (v i)) * (V * Z * Vᴴ)) <
      1 - |x i| := by
  apply lt_of_not_ge
  intro hs
  apply hx.no_update (by norm_num) i hi (nearestSign_isSign (x i)).symm
  unfold spinPotential
  rw [signed_center_update, naturalOwners_update_endpoint 64 x i (nearestSign_isSign _)]
  apply spin_retire_in_frame _ v (naturalOwners 64 x)
    (fun j => naturalOwners_nonneg (by norm_num) le_rfl hx.1 j) V hV hθ S hS ht hmax
    hZ hM hsolve hsupport i (nearestSign (x i) - x i)
  rwa [nearestSign_distance ⟨hx.1.1 i, hx.1.2 i⟩]

end MatrixSpencer.KSSpinChosenRetirement
