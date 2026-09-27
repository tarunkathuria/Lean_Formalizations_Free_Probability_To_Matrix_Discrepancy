import MatrixSpencer.DyadicDensityCalculus
import MatrixSpencer.DyadicBoundaryGain

/-! Faithfulness of actual dyadic density maximizers for arbitrary Kraus data.
The Kraus matrices need not be Hermitian or contractions, and their source
may be singular. The kernel perturbation is constructed from the density. -/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

namespace MatrixSpencer

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]

theorem dyadicDensityObjective_kernel_perturbation_lower (H : Matrix n n ℂ)
    (B : ι → Matrix n n ℂ) {m : ℕ} (hm : 1 ≤ m) {θ : ℝ} (hθ : 0 ≤ θ)
    {S U : Matrix n n ℂ} (hS : S.PosSemidef) (hU : U.PosSemidef)
    (htrace : realTrace U = 1) (hUU : U * U = U) (hSU : S * U = 0) (hUS : U * S = 0)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    (1 - r ^ (2 ^ m)) * dyadicDensityObjective H B m θ S + r ^ (2 ^ m) * realTrace (H * U) +
      DyadicBoundaryGain.scale m θ * r ^ (2 ^ m - 1) ≤
      dyadicDensityObjective H B m θ ((1 - r ^ (2 ^ m)) • S + r ^ (2 ^ m) • U) := by
  have hrpow : r ^ (2 ^ m) ≤ 1 := pow_le_one₀ hr hr1
  have ha : 0 ≤ 1 - r ^ (2 ^ m) := by linarith
  have hb : 0 ≤ r ^ (2 ^ m) := pow_nonneg hr _
  have hf := fidelity_concave hS hU (krausChannel_posSemidef B hS)
    (krausChannel_posSemidef B hU) ha hb (by ring)
  have hfU := mul_nonneg hb (fidelity_nonneg U (krausChannel B U))
  have hreg := DyadicBoundaryGain.regularizer_kernel_perturbation_lower hm hθ hS hU htrace hUU hSU hUS hr hr1
  simp only [dyadicDensityObjective, krausChannel_weighted_add, Matrix.mul_add,
    Matrix.mul_smul, realTrace_add, realTrace_smul]
  nlinarith

/-- Any actual global maximizer is positive definite. No condition is imposed on its source rank. -/
theorem dyadicDensity_maximizer_posDef (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    {m : ℕ} (hm : 1 ≤ m) {θ : ℝ} (hθ : 0 < θ)
    {S : Matrix n n ℂ} (hS : S ∈ densitySet)
    (hmax : ∀ T ∈ densitySet, dyadicDensityObjective H B m θ T ≤ dyadicDensityObjective H B m θ S) :
    S.PosDef := by
  by_contra hn
  obtain ⟨U, hU, htrace, hUU, hrootU, hUroot⟩ := exists_kernel_density_projection hS.1 hn
  have hSU : S * U = 0 := by
    calc
      _ = CFC.sqrt S * (CFC.sqrt S * U) := by
        rw [← Matrix.mul_assoc, CFC.sqrt_mul_sqrt_self S hS.1.nonneg]
      _ = 0 := by rw [hrootU, Matrix.mul_zero]
  have hUS : U * S = 0 := by
    calc
      _ = (U * CFC.sqrt S) * CFC.sqrt S := by
        rw [Matrix.mul_assoc, CFC.sqrt_mul_sqrt_self S hS.1.nonneg]
      _ = 0 := by rw [hUroot, Matrix.zero_mul]
  let K := |realTrace (H * U) - dyadicDensityObjective H B m θ S|
  have hK : 0 ≤ K := abs_nonneg _
  have hK1 : 0 < K + 1 := by linarith
  have hc : 0 < DyadicBoundaryGain.scale m θ := DyadicBoundaryGain.scale_pos hm hθ
  have hsmall : 0 < min 1 (DyadicBoundaryGain.scale m θ / (K + 1)) :=
    lt_min (by norm_num) (div_pos hc hK1)
  obtain ⟨r, hr, hrsmall⟩ := exists_between hsmall
  have hr1 : r < 1 := (lt_min_iff.mp hrsmall).1
  have hrK1 : r * (K + 1) < DyadicBoundaryGain.scale m θ :=
    (lt_div_iff₀ hK1).mp (lt_min_iff.mp hrsmall).2
  have hrK : K * r < DyadicBoundaryGain.scale m θ := by nlinarith
  have he : (2 ^ m - 1) + 1 = 2 ^ m := by have := DyadicBoundaryGain.order_ge_two hm; omega
  have hgain : 0 < DyadicBoundaryGain.scale m θ * r ^ (2 ^ m - 1) - r ^ (2 ^ m) * K := by
    calc
      0 < r ^ (2 ^ m - 1) * (DyadicBoundaryGain.scale m θ - K * r) :=
        mul_pos (pow_pos hr _) (sub_pos.mpr hrK)
      _ = DyadicBoundaryGain.scale m θ * r ^ (2 ^ m - 1) - r ^ (2 ^ m) * K := by
        have hpow : r ^ (2 ^ m) = r ^ (2 ^ m - 1) * r := by rw [← pow_succ, he]
        rw [hpow]
        ring
  have hrpow : r ^ (2 ^ m) ≤ 1 := pow_le_one₀ hr.le hr1.le
  have ha : 0 ≤ 1 - r ^ (2 ^ m) := by linarith
  have hb : 0 ≤ r ^ (2 ^ m) := pow_nonneg hr.le _
  have hmix : (1 - r ^ (2 ^ m)) • S + r ^ (2 ^ m) • U ∈ densitySet :=
    densitySet_convex hS ⟨hU, htrace⟩ ha hb (by ring)
  have hlower := dyadicDensityObjective_kernel_perturbation_lower H B hm hθ.le
    hS.1 hU htrace hUU hSU hUS hr.le hr1.le
  have hupper := hmax ((1 - r ^ (2 ^ m)) • S + r ^ (2 ^ m) • U) hmix
  have herr : -K ≤ realTrace (H * U) - dyadicDensityObjective H B m θ S := neg_abs_le _
  have herr' := mul_le_mul_of_nonneg_left herr hb
  nlinarith

end MatrixSpencer
