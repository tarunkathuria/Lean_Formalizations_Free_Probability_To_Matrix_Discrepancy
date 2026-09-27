import MatrixSpencer.KSSpinChosenRetirement

/-!
# Safe owner retirement assisted by an extra physical debit

Deleting owner i and moving its signed coefficient by t does not increase
the actual optimized owner potential when |t| is at most c_i q_i plus the
extra debit δ. This is proved with the actual supported source and optimizer,
using the previously established matrix domination retirement theorem.
-/

open Matrix Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSDebitRetirement
open KSPotentialModels KSSafeRetirement KSEndpointRetirement KSRankOne

variable {ι n m : Type*} [Fintype ι] [Fintype n] [Fintype m]
  [DecidableEq ι] [DecidableEq n] [DecidableEq m] [Nonempty n]
local instance {k : Type*} [Fintype k] [DecidableEq k] : CStarAlgebra (Matrix k k ℂ) := {}

/-- The additional debit extends the safe endpoint-step allowance by δ. -/
theorem spin_retire_with_debit_in_frame
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
    (i : ι) (t δ : ℝ)
    (hsafe : |t| ≤ c i * realTrace (KSSpinSource.doubled (atom (v i)) * (V * Z * Vᴴ)) + δ) :
    ownerPotential (H + t • signedLift (atom (v i)) - δ • KSSpinSource.doubled (atom (v i)))
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
    rw [add_smul] at hstep
    have hsum := add_le_add_left (sub_nonpos.mpr hstep)
      (H + covarianceSource (KSSpinSource.family (fun j => atom (v j)))
        (KSSpinSource.coefficientCovariance c) (V * Z * Vᴴ))
    simp only [add_zero] at hsum
    convert hsum using 1
    abel


/-- Rejection of the actual nearest-endpoint candidate forces the scalar gap
that underlies both the boundary margin and the failed safe-retirement test.
Numerical report errors are separate from this exact-potential implication. -/
theorem rejected_nearest_retirement_gap
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
    (i : ι) (a δ : ℝ) (ha : -1 ≤ a ∧ a ≤ 1)
    (hreject : ownerPotential H (KSSpinSource.family (fun j => atom (v j)))
        (KSSpinSource.coefficientCovariance c) θ <
      ownerPotential
        (H + (nearestSign a - a) • signedLift (atom (v i)) -
          δ • KSSpinSource.doubled (atom (v i)))
        (KSSpinSource.family (fun j => atom (v j)))
        (KSSpinSource.coefficientCovariance (Function.update c i 0)) θ) :
    c i * realTrace (KSSpinSource.doubled (atom (v i)) * (V * Z * Vᴴ)) + δ <
      1 - |a| := by
  apply lt_of_not_ge
  intro hsafe
  apply (not_le_of_gt hreject)
  apply spin_retire_with_debit_in_frame H v c hc V hV hθ S hS ht hmax
    hZ hM hsolve hsupport i (nearestSign a - a) δ
  rwa [nearestSign_distance ha]

omit [Fintype ι] [DecidableEq ι] [DecidableEq m] [Nonempty n] in
/-- The transport contribution is nonnegative, so the exact rejection gap
implies both a boundary margin above δ and the original no-safe inequality. -/
theorem gap_implies_margin_and_noSafe
    (v : ι → n → ℂ) (c : ι → ℝ) (hc : ∀ j, 0 ≤ c j)
    (V : Matrix (n ⊕ n) m ℂ) {Z : Matrix m m ℂ} (hZ : Z.PosSemidef)
    (i : ι) {a δ : ℝ} (hδ : 0 ≤ δ)
    (hgap : c i * realTrace (KSSpinSource.doubled (atom (v i)) * (V * Z * Vᴴ)) + δ <
      1 - |a|) :
    δ < 1 - |a| ∧
      c i * realTrace (KSSpinSource.doubled (atom (v i)) * (V * Z * Vᴴ)) < 1 - |a| := by
  have hq := realTrace_mul_nonneg (KSSpinSource.doubled_posSemidef (atom_posSemidef (v i)))
    (hZ.mul_mul_conjTranspose_same V)
  have hcq := mul_nonneg (hc i) hq
  constructor <;> linarith

end MatrixSpencer.KSDebitRetirement
