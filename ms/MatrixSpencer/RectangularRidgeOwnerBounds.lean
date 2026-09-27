import MatrixSpencer.RectangularRidgeCovarianceCalculus
import MatrixSpencer.RegularizedOwnerPotential
import MatrixSpencer.SpectralDensity
import MatrixSpencer.SignedLift

/-!
# Basic bounds for the actual rectangular mixed owner potential

The regularizer is the existing dyadic Tsallis term plus its square-root
ridge. All covariance monotonicity, excess and reinstall bounds below apply
directly to the original Hermitian contraction family and PSD coefficient
covariance; no derived geometry or analytic certificate is assumed.
-/
open Matrix Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.RectangularRidgeOwnerBounds
open RectangularRidgeCovarianceCalculus
variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]
local instance ridgeOwnerBoundsCStar : CStarAlgebra (Matrix n n ℂ) := {}

/-- The zero-covariance potential, with exactly the same mixed regularizer. -/
def basePotential (m : ℕ) (H : Matrix n n ℂ) (θ κ : ℝ) : ℝ :=
  regularizedBasePotential H (regularizer m θ κ)

omit [Fintype ι] [DecidableEq ι] in
lemma continuousOn_regularizer (m : ℕ) (θ κ : ℝ) :
    ContinuousOn (regularizer (n := n) m θ κ) densitySet := by
  apply continuousOn_iff_continuous_restrict.mpr
  have hs : Continuous (fun S : (densitySet : Set (Matrix n n ℂ)) => (S : Matrix n n ℂ)) :=
    continuous_subtype_val
  have ht := continuousOn_iff_continuous_restrict.mp
    (continuousOn_density_dyadicTsallisRegularizer (n := n) m θ)
  have hr := continuous_matrix_sqrt_of_psd hs (fun S => S.property.1)
  exact ht.add (continuous_const.mul (continuous_realTrace.comp hr))

omit [Fintype ι] [DecidableEq ι] in
lemma regularizer_nonneg {m : ℕ} (hm : 1 ≤ m) {θ κ : ℝ} (hθ : 0 ≤ θ) (hκ : 0 ≤ κ)
    {S : Matrix n n ℂ} (hS : S.PosSemidef) : 0 ≤ regularizer m θ κ S :=
  add_nonneg (dyadicTsallisRegularizer_nonneg hm hθ hS)
    (mul_nonneg (mul_nonneg (by norm_num) hκ)
      (realTrace_nonneg (CFC.sqrt_nonneg S).posSemidef))

omit [Fintype ι] [DecidableEq ι] in
lemma regularizer_density_bound {m : ℕ} (hm : 1 ≤ m) {θ κ : ℝ} (hθ : 0 ≤ θ) (hκ : 0 ≤ κ)
    {S : Matrix n n ℂ} (hS : S ∈ densitySet) : regularizer m θ κ S ≤
      θ * (Fintype.card n : ℝ) ^ (1 / (2 ^ m : ℝ)) / (1 - 1 / (2 ^ m : ℝ)) +
        2 * κ * Real.sqrt (Fintype.card n : ℝ) :=
  add_le_add (dyadicTsallisRegularizer_density_bound_reciprocal hm hθ hS)
    (mul_le_mul_of_nonneg_left (density_trace_sqrt_le_sqrt_card hS)
      (mul_nonneg (by norm_num) hκ))

omit [DecidableEq ι] in
@[simp] theorem owner_zero (m : ℕ) (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ) (θ κ : ℝ) :
    RectangularRidgeCovarianceCalculus.ownerPotential m H A 0 θ κ = basePotential m H θ κ :=
  regularizedOwnerPotential_zero H A (regularizer m θ κ)

variable [Nonempty n]

/-- Monotonicity includes singular and zero coefficient covariances. -/
theorem mono_covariance (m : ℕ) (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) {C D : Matrix ι ι ℝ}
    (hC : C.PosSemidef) (hD : D.PosSemidef) (hCD : C ≤ D) (θ κ : ℝ) :
    RectangularRidgeCovarianceCalculus.ownerPotential m H A C θ κ ≤ RectangularRidgeCovarianceCalculus.ownerPotential m H A D θ κ :=
  regularizedOwnerPotential_mono_covariance H A hA hC hD hCD
    (regularizer m θ κ) (continuousOn_regularizer m θ κ)

theorem base_le_owner (m : ℕ) (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (θ κ : ℝ) :
    basePotential m H θ κ ≤ RectangularRidgeCovarianceCalculus.ownerPotential m H A C θ κ :=
  regularizedBasePotential_le_owner H A hA hC (regularizer m θ κ) (continuousOn_regularizer m θ κ)

/-- Covariance excess is bounded by the original retained label count. -/
theorem owner_le_base_add (m : ℕ) (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (hN : ∀ i, ‖A i‖ ≤ 1)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (hC1 : C ≤ 1) (θ κ : ℝ) :
    RectangularRidgeCovarianceCalculus.ownerPotential m H A C θ κ ≤ basePotential m H θ κ + 2 * Real.sqrt (Fintype.card ι : ℝ) :=
  regularizedOwnerPotential_le_base_add H A hA hN hC hC1
    (regularizer m θ κ) (continuousOn_regularizer m θ κ)

theorem owner_excess_bounds (m : ℕ) (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (hN : ∀ i, ‖A i‖ ≤ 1)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (hC1 : C ≤ 1) (θ κ : ℝ) :
    0 ≤ RectangularRidgeCovarianceCalculus.ownerPotential m H A C θ κ - RectangularRidgeCovarianceCalculus.ownerPotential m H A 0 θ κ ∧
      RectangularRidgeCovarianceCalculus.ownerPotential m H A C θ κ - RectangularRidgeCovarianceCalculus.ownerPotential m H A 0 θ κ ≤
        2 * Real.sqrt (Fintype.card ι : ℝ) := by
  rw [owner_zero]
  exact ⟨sub_nonneg.mpr (base_le_owner m H A hA hC θ κ),
    (sub_le_iff_le_add).mpr (by simpa only [add_comm] using owner_le_base_add m H A hA hN hC hC1 θ κ)⟩

/-- Reinstallation may change the retained original labels; only the new count is charged. -/
theorem reinstall_le {ι' : Type*} [Fintype ι'] [DecidableEq ι']
    (m : ℕ) (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ) (A' : ι' → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (hA' : ∀ i, (A' i).IsHermitian) (hN' : ∀ i, ‖A' i‖ ≤ 1)
    {C : Matrix ι ι ℝ} {C' : Matrix ι' ι' ℝ}
    (hC : C.PosSemidef) (hC' : C'.PosSemidef) (hC'1 : C' ≤ 1) (θ κ : ℝ) :
    RectangularRidgeCovarianceCalculus.ownerPotential m H A' C' θ κ - RectangularRidgeCovarianceCalculus.ownerPotential m H A C θ κ ≤
      2 * Real.sqrt (Fintype.card ι' : ℝ) :=
  regularizedOwnerPotential_refresh_le H A A' hA hA' hN' hC hC' hC'1
    (regularizer m θ κ) (continuousOn_regularizer m θ κ)

theorem sub_le_norm (m : ℕ) {H H' : Matrix n n ℂ} (hH : H.IsHermitian) (hH' : H'.IsHermitian)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (θ κ : ℝ) :
    RectangularRidgeCovarianceCalculus.ownerPotential m H' A C θ κ - RectangularRidgeCovarianceCalculus.ownerPotential m H A C θ κ ≤ ‖H' - H‖ :=
  regularizedOwnerPotential_sub_le_norm hH hH' A hA hC (regularizer m θ κ)
    (continuousOn_regularizer m θ κ)

theorem abs_sub_le_norm (m : ℕ) {H H' : Matrix n n ℂ} (hH : H.IsHermitian) (hH' : H'.IsHermitian)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (θ κ : ℝ) :
    |RectangularRidgeCovarianceCalculus.ownerPotential m H' A C θ κ - RectangularRidgeCovarianceCalculus.ownerPotential m H A C θ κ| ≤ ‖H' - H‖ :=
  abs_regularizedOwnerPotential_sub_le_norm hH hH' A hA hC (regularizer m θ κ)
    (continuousOn_regularizer m θ κ)

omit [Fintype ι] [DecidableEq ι] in
theorem trace_le_base (m : ℕ) (hm : 1 ≤ m) (H : Matrix n n ℂ) {θ κ : ℝ}
    (hθ : 0 ≤ θ) (hκ : 0 ≤ κ) {S : Matrix n n ℂ} (hS : S ∈ densitySet) :
    realTrace (H * S) ≤ basePotential m H θ κ := by
  have h := regularizedBaseObjective_le_potential H (regularizer m θ κ)
    (continuousOn_regularizer m θ κ) hS
  have hr := regularizer_nonneg hm hθ hκ hS.1
  unfold regularizedBaseObjective at h
  unfold basePotential
  linarith

/-- Every actual Hermitian eigenvalue is bounded by the mixed owner potential. -/
theorem eigenvalue_le (m : ℕ) (hm : 1 ≤ m) {H : Matrix n n ℂ} (hH : H.IsHermitian)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) {θ κ : ℝ} (hθ : 0 ≤ θ) (hκ : 0 ≤ κ) (i : n) :
    hH.eigenvalues i ≤ RectangularRidgeCovarianceCalculus.ownerPotential m H A C θ κ := by
  have h := trace_le_base m hm H hθ hκ (eigenDensity_mem hH i)
  rw [realTrace_mul_eigenDensity] at h
  exact h.trans (base_le_owner m H A hA hC θ κ)

omit [Fintype ι] [DecidableEq ι] in
/-- The signed lift converts the spectral-edge lower bound to the ordinary two-sided norm. -/
theorem norm_le_signedLift_base (m : ℕ) (hm : 1 ≤ m) {H : Matrix n n ℂ}
    (hH : H.IsHermitian) {θ κ : ℝ} (hθ : 0 ≤ θ) (hκ : 0 ≤ κ) :
    ‖H‖ ≤ basePotential m (signedLift H) θ κ := by
  letI : CStarAlgebra (Matrix (n ⊕ n) (n ⊕ n) ℂ) := {}
  obtain ⟨S, hS, hval⟩ := exists_signedLift_density_norm hH
  simpa only [hval] using trace_le_base m hm (signedLift H) hθ hκ hS

/-- Explicit initial budget, with the added ridge cost visible. -/
theorem le_norm_add (m : ℕ) (hm : 1 ≤ m) {H : Matrix n n ℂ} (hH : H.IsHermitian)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) (hN : ∀ i, ‖A i‖ ≤ 1)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (hC1 : C ≤ 1)
    {θ κ : ℝ} (hθ : 0 ≤ θ) (hκ : 0 ≤ κ) :
    RectangularRidgeCovarianceCalculus.ownerPotential m H A C θ κ ≤ ‖H‖ + 2 * Real.sqrt (Fintype.card ι : ℝ) +
      (θ * (Fintype.card n : ℝ) ^ (1 / (2 ^ m : ℝ)) / (1 - 1 / (2 ^ m : ℝ)) +
        2 * κ * Real.sqrt (Fintype.card n : ℝ)) :=
  regularizedOwnerPotential_le_norm_add hH A hA hN hC hC1
    (regularizer m θ κ) (continuousOn_regularizer m θ κ)
    (fun _ hS => regularizer_density_bound hm hθ hκ hS)

end MatrixSpencer.RectangularRidgeOwnerBounds
