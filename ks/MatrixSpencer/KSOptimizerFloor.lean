import MatrixSpencer.KSSafeRetirement
import MatrixSpencer.SpectralDensity
import MatrixSpencer.KSFullHermitianChart

/-!
# An explicit spectral floor for the actual density optimizer

Stationarity and the positive supported fidelity gradient bound the inverse
square root by the actual objective value plus the center norm. This yields
a computable floor from a supplied objective cap, and then from input norm
and Kraus-source budgets. No minimum eigenvalue is chosen nonconstructively.
-/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

noncomputable section

namespace MatrixSpencer.KSOptimizerFloor

variable {ι n m : Type*} [Fintype ι] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

local instance {k : Type*} [Fintype k] [DecidableEq k] : CStarAlgebra (Matrix k k ℂ) := {}
local instance : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance

open KSSafeRetirement

omit [DecidableEq n] in
theorem supportedGradient_posSemidef (B : ι → Matrix n n ℂ) (V : Matrix n m ℂ)
    {Z : Matrix m m ℂ} (hZ : Z.PosDef) : (supportedGradient B V Z).PosSemidef := by
  apply Matrix.nonneg_iff_posSemidef.mp
  apply add_nonneg (hZ.inv.posSemidef.mul_mul_conjTranspose_same V).nonneg
  apply Finset.sum_nonneg
  intro i _
  exact ((hZ.posSemidef.mul_mul_conjTranspose_same V).conjTranspose_mul_mul_same (B i)).nonneg

theorem actualSupportedGradient_posSemidef (B : ι → Matrix n n ℂ)
    {S : Matrix n n ℂ} (hS : S.PosDef) : (actualSupportedGradient B S).PosSemidef :=
  supportedGradient_posSemidef B (krausSupportEmbedding B) (actualSupportTransport_posDef B hS)

theorem inverseSqrt_mul_self (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) : inverseSqrt S * (S : Matrix n n ℂ) = CFC.sqrt (S : Matrix n n ℂ) := by
  unfold inverseSqrt
  conv_lhs => rhs; rw [← CFC.sqrt_mul_sqrt_self (S : Matrix n n ℂ) hS.posSemidef.nonneg]
  rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _
    ((CFC.sqrt (S : Matrix n n ℂ)).isUnit_iff_isUnit_det.mp hS.posDef_sqrt.isUnit), Matrix.one_mul]

/-- Euler contact for the positive fidelity gradient and stationarity on
`T-S` control every density pairing of the inverse square root. -/
theorem inverseSqrt_pairing_le (H : Matrix n n ℂ) (hH : H.IsHermitian)
    (B : ι → Matrix n n ℂ) {θ : ℝ} (hθ : 0 < θ)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (htr : realTrace (S : Matrix n n ℂ) = 1)
    (hmax : ∀ T ∈ densitySet, densityObjective H B θ T ≤ densityObjective H B θ S)
    {T : Matrix n n ℂ} (hT : T ∈ densitySet) :
    θ * realTrace (inverseSqrt S * T) ≤ densityObjective H B θ S + ‖H‖ := by
  let T' : selfAdjoint (Matrix n n ℂ) := ⟨T, hT.1.isHermitian⟩
  let D : densityTangent (n := n) := ⟨T' - S, by
    change realTrace (T - (S : Matrix n n ℂ)) = 0
    rw [realTrace_sub, hT.2, htr, sub_self]⟩
  have hstat := density_maximizer_stationary_source_unrestricted H B θ S hS htr hmax
  have hzero := congrArg (fun F : densityTangent (n := n) →L[ℝ] ℝ => F D) hstat
  change fderiv ℝ (hermitianDensityObjective H B θ) S (T' - S) = 0 at hzero
  have hd (X : selfAdjoint (Matrix n n ℂ)) :
      fderiv ℝ (hermitianDensityObjective H B θ) S X =
        realTrace (H * (X : Matrix n n ℂ)) +
        realTrace (actualSupportedGradient B S * (X : Matrix n n ℂ)) +
        θ * realTrace (inverseSqrt S * (X : Matrix n n ℂ)) := by
    rw [fderiv_hermitianDensityObjective_eq_source_unrestricted H B θ S hS,
      fderiv_krausSourceFidelity_eq_supportedGradient B S hS,
      fderiv_tsallisPotential_eq θ S hS]
    rfl
  rw [map_sub, hd, hd, actualSupportedGradient_contact B hS, inverseSqrt_mul_self S hS] at hzero
  have hG := realTrace_mul_nonneg (actualSupportedGradient_posSemidef B hS) hT.1
  have hHlo := (abs_le.mp (abs_realTrace_mul_density_le_norm hH hT)).1
  have ht := mul_nonneg hθ.le (realTrace_nonneg (CFC.sqrt_nonneg (S : Matrix n n ℂ)).posSemidef)
  change realTrace (H * T) + realTrace (actualSupportedGradient B S * T) +
    θ * realTrace (inverseSqrt S * T) -
      (realTrace (H * (S : Matrix n n ℂ)) + 2 * fidelity S (krausChannel B S) +
        θ * realTrace (CFC.sqrt (S : Matrix n n ℂ))) = 0 at hzero
  unfold densityObjective
  linarith

theorem le_scalar_of_density_pairings {A : Matrix n n ℂ} (hA : A.IsHermitian) (c : ℝ)
    (hpair : ∀ T ∈ densitySet, realTrace (A * T) ≤ c) : A ≤ c • (1 : Matrix n n ℂ) := by
  rw [← Algebra.algebraMap_eq_smul_one, le_algebraMap_iff_spectrum_le hA,
    hA.spectrum_real_eq_range_eigenvalues]
  rintro r ⟨i, rfl⟩
  simpa only [realTrace_mul_eigenDensity] using hpair (eigenDensity hA i) (eigenDensity_mem hA i)

theorem inverse_order {A B : Matrix n n ℂ} (hA : A.PosDef) (hB : B.PosDef)
    (hAB : A ≤ B) : B⁻¹ ≤ A⁻¹ := by
  obtain ⟨a, rfl⟩ := hA.isUnit
  obtain ⟨b, rfl⟩ := hB.isUnit
  simpa only [Matrix.coe_units_inv] using CStarAlgebra.inv_le_inv hA.posSemidef.nonneg hAB

theorem scalar_inverse {c : ℝ} (hc : c ≠ 0) :
    (c • (1 : Matrix n n ℂ))⁻¹ = c⁻¹ • (1 : Matrix n n ℂ) := by
  apply Matrix.inv_eq_left_inv
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul,
    mul_inv_cancel₀ hc, one_smul]

set_option maxHeartbeats 600000 in
theorem square_scalar_floor {Q : Matrix n n ℂ}
    {a : ℝ} (ha : 0 ≤ a) (hfloor : a • (1 : Matrix n n ℂ) ≤ Q) :
    a ^ 2 • (1 : Matrix n n ℂ) ≤ Q * Q := by
  have hD : (Q - a • (1 : Matrix n n ℂ)).PosSemidef := Matrix.le_iff.mp hfloor
  have hDsq : ((Q - a • (1 : Matrix n n ℂ)) * (Q - a • (1 : Matrix n n ℂ))).PosSemidef := by
    have hp := Matrix.posSemidef_conjTranspose_mul_self (Q - a • (1 : Matrix n n ℂ))
    rwa [hD.isHermitian.eq] at hp
  apply Matrix.le_iff.mpr
  have hid : Q * Q - a ^ 2 • (1 : Matrix n n ℂ) =
      (Q - a • 1) * (Q - a • 1) + (2 * a) • (Q - a • 1) := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one, smul_sub, smul_smul]
    module
  rw [hid]
  exact hDsq.add (hD.smul (by positivity : 0 ≤ 2 * a))

/-- A bound on the inverse square root gives the explicit squared reciprocal
spectral floor. The proof uses matrix inverse order and scalar commutation. -/
theorem floor_of_inverseSqrt_le (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) {c : ℝ} (hc : 0 < c)
    (hinv : inverseSqrt S ≤ c • (1 : Matrix n n ℂ)) :
    (c⁻¹) ^ 2 • (1 : Matrix n n ℂ) ≤ (S : Matrix n n ℂ) := by
  have hi := inverse_order hS.posDef_sqrt.inv (Matrix.PosDef.one.smul hc) hinv
  rw [scalar_inverse hc.ne',
    Matrix.nonsing_inv_nonsing_inv _ ((CFC.sqrt (S : Matrix n n ℂ)).isUnit_iff_isUnit_det.mp hS.posDef_sqrt.isUnit)] at hi
  have hs := square_scalar_floor (inv_nonneg.mpr hc.le) hi
  rwa [CFC.sqrt_mul_sqrt_self _ hS.posSemidef.nonneg] at hs

/-- The actual optimizer has an explicit floor from an actual objective cap.
This is the bound used when the walk already tracks a potential budget. -/
theorem maximizer_floor_of_objective_cap (H : Matrix n n ℂ) (hH : H.IsHermitian)
    (B : ι → Matrix n n ℂ) {θ K : ℝ} (hθ : 0 < θ) (hK : 0 < K)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (htr : realTrace (S : Matrix n n ℂ) = 1)
    (hmax : ∀ T ∈ densitySet, densityObjective H B θ T ≤ densityObjective H B θ S)
    (hcap : densityObjective H B θ S + ‖H‖ ≤ K) :
    (θ / K) ^ 2 • (1 : Matrix n n ℂ) ≤ (S : Matrix n n ℂ) := by
  have hinv : inverseSqrt S ≤ (K / θ) • (1 : Matrix n n ℂ) := by
    apply le_scalar_of_density_pairings hS.posDef_sqrt.inv.isHermitian
    intro T hT
    apply (le_div_iff₀ hθ).mpr
    change realTrace (inverseSqrt S * T) * θ ≤ K
    have hp := inverseSqrt_pairing_le H hH B hθ S hS htr hmax hT
    nlinarith
  simpa only [inv_div] using floor_of_inverseSqrt_le S hS (div_pos hK hθ) hinv

/-- Canonical optimizer version using the actual potential budget tracked by
the outer walk. Faithfulness and stationarity are proved internally. -/
theorem densityOptimizer_floor_of_potential_cap [Nonempty n]
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (B : ι → Matrix n n ℂ)
    {θ K : ℝ} (hθ : 0 < θ) (hK : 0 < K)
    (hcap : densityPotential H B θ + ‖H‖ ≤ K) :
    (θ / K) ^ 2 • (1 : Matrix n n ℂ) ≤ densityOptimizer H B θ := by
  apply maximizer_floor_of_objective_cap H hH B hθ hK
    (hermitianDensityOptimizer H B θ) (densityOptimizer_posDef H B hθ)
    (densityOptimizer_mem H B θ).2 (densityOptimizer_isMaxOn H B θ)
  exact (add_le_add_right (densityObjective_le_potential H B θ (densityOptimizer_mem H B θ)) ‖H‖).trans hcap

theorem kraus_trace_le_of_budget (B : ι → Matrix n n ℂ) {κ : ℝ}
    (hbudget : (∑ i, (B i)ᴴ * B i) ≤ κ • (1 : Matrix n n ℂ))
    {S : Matrix n n ℂ} (hS : S ∈ densitySet) : realTrace (krausChannel B S) ≤ κ := by
  have htr : realTrace (krausChannel B S) = realTrace ((∑ i, (B i)ᴴ * B i) * S) := by
    simpa only [sourceAdjoint, Matrix.mul_one, Matrix.one_mul] using
      (realTrace_sourceAdjoint B 1 S).symm
  have hb := realTrace_mul_mono hS.1 hbudget
  rw [realTrace_mul_comm S (∑ i, (B i)ᴴ * B i), Matrix.mul_smul, Matrix.mul_one,
    realTrace_smul, hS.2, mul_one] at hb
  rwa [htr]

/-- The input norm and Kraus budget give a concrete cap for the full objective. -/
theorem objective_le_input_bound (H : Matrix n n ℂ) (hH : H.IsHermitian)
    (B : ι → Matrix n n ℂ) {θ R κ : ℝ} (hθ : 0 ≤ θ) (hR : ‖H‖ ≤ R)
    (hbudget : (∑ i, (B i)ᴴ * B i) ≤ κ • (1 : Matrix n n ℂ))
    {S : Matrix n n ℂ} (hS : S ∈ densitySet) :
    densityObjective H B θ S ≤ R + 2 * Real.sqrt κ +
      2 * θ * Real.sqrt (Fintype.card n : ℝ) := by
  have hlin := (realTrace_mul_density_le_norm hH hS).trans hR
  have hfid := fidelity_le_sqrt_trace_mul hS.1 (krausChannel_posSemidef B hS.1)
  rw [hS.2, one_mul] at hfid
  have hf := hfid.trans (Real.sqrt_le_sqrt (kraus_trace_le_of_budget B hbudget hS))
  have hr := mul_le_mul_of_nonneg_left (density_trace_sqrt_le_sqrt_card hS)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hθ)
  unfold densityObjective
  linarith

def inputDenominator (R κ θ : ℝ) : ℝ :=
  2 * R + 2 * Real.sqrt κ + 2 * θ * Real.sqrt (Fintype.card n : ℝ)

omit [DecidableEq n] in
theorem inputDenominator_pos [Nonempty n] {R κ θ : ℝ} (hR : 0 ≤ R) (hθ : 0 < θ) :
    0 < inputDenominator (n := n) R κ θ := by
  have hn : 0 < Real.sqrt (Fintype.card n : ℝ) :=
    Real.sqrt_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)
  unfold inputDenominator
  positivity

omit [DecidableEq n] in
theorem inputFloor_pos [Nonempty n] {R κ θ : ℝ} (hR : 0 ≤ R) (hθ : 0 < θ) :
    0 < (θ / inputDenominator (n := n) R κ θ) ^ 2 :=
  sq_pos_of_pos (div_pos hθ (inputDenominator_pos hR hθ))

/-- Explicit floor for the canonical optimizer, entirely from input bounds. -/
theorem densityOptimizer_floor [Nonempty n] (H : Matrix n n ℂ) (hH : H.IsHermitian)
    (B : ι → Matrix n n ℂ) {θ R κ : ℝ} (hθ : 0 < θ) (hR : ‖H‖ ≤ R)
    (hbudget : (∑ i, (B i)ᴴ * B i) ≤ κ • (1 : Matrix n n ℂ)) :
    (θ / inputDenominator (n := n) R κ θ) ^ 2 • (1 : Matrix n n ℂ) ≤ densityOptimizer H B θ := by
  let S := hermitianDensityOptimizer H B θ
  have hmem := densityOptimizer_mem H B θ
  apply maximizer_floor_of_objective_cap H hH B hθ
    (inputDenominator_pos ((norm_nonneg H).trans hR) hθ) S
    (densityOptimizer_posDef H B hθ) hmem.2 (densityOptimizer_isMaxOn H B θ)
  have hb := objective_le_input_bound H hH B hθ.le hR hbudget hmem
  change densityObjective H B θ (densityOptimizer H B θ) + ‖H‖ ≤ _
  unfold inputDenominator
  linarith

/-- This explicit positive density floor can be passed to the full-coordinate
projected optimizer theorem without a separate optimizer-membership hypothesis. -/
theorem optimizer_coordinates_mem_floor [Nonempty n]
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (B : ι → Matrix n n ℂ)
    {θ R κ : ℝ} (hθ : 0 < θ) (hR : ‖H‖ ≤ R)
    (hbudget : (∑ i, (B i)ᴴ * B i) ≤ κ • (1 : Matrix n n ℂ)) :
    (KSFullHermitianChart.chartEquiv n).symm (hermitianDensityOptimizer H B θ) ∈
      KSObjectiveChart.densityFloor (KSFullHermitianChart.chart n)
        ((θ / inputDenominator (n := n) R κ θ) ^ 2) := by
  have he : KSFullHermitianChart.chart n
      ((KSFullHermitianChart.chartEquiv n).symm (hermitianDensityOptimizer H B θ)) =
        hermitianDensityOptimizer H B θ := (KSFullHermitianChart.chartEquiv n).apply_symm_apply _
  change _ ∧ _
  rw [he]
  exact ⟨densityOptimizer_floor H hH B hθ hR hbudget, (densityOptimizer_mem H B θ).2⟩

end MatrixSpencer.KSOptimizerFloor
