import HigherRankKS.CarrierPower
import HigherRankKS.MatrixPowerConcavity
import MatrixSpencer.TraceSqrtConcavity

/-!
# Homogeneity and concavity of the concrete carrier

The carrier is the trace perspective of the fractional matrix power.
The proofs include zero inputs and zero coefficients.
-/

open Matrix MatrixSpencer Set
open scoped NNReal MatrixOrder ComplexOrder Matrix.Norms.L2Operator

noncomputable section
namespace HigherRankKS

variable {n : Type*} [Fintype n] [DecidableEq n]
local instance carrierConcavityCStar : CStarAlgebra (Matrix n n ℂ) := {}

/-- Nonnegative scalar multiplication commutes with a nonnegative matrix power. -/
theorem matrix_rpow_smul {M : Matrix n n ℂ} (hM : M.PosSemidef)
    {t p : ℝ} (ht : 0 ≤ t) (hp : 0 ≤ p) :
    CFC.rpow (t • M) p = (t ^ p) • CFC.rpow M p := by
  let s : ℝ≥0 := ⟨t, ht⟩
  have hs : (s : ℝ) = t := rfl
  have h : cfc (fun x : ℝ≥0 => x ^ p) (s • M) =
      (s ^ p) • cfc (fun x : ℝ≥0 => x ^ p) M := by
    rw [← cfc_comp_smul s (fun x : ℝ≥0 => x ^ p) M
      ((NNReal.continuous_rpow_const hp).continuousOn) hM.nonneg]
    simp_rw [smul_eq_mul, NNReal.mul_rpow]
    exact cfc_const_mul (s ^ p) (fun x : ℝ≥0 => x ^ p) M
      ((NNReal.continuous_rpow_const hp).continuousOn)
  simpa only [NNReal.smul_def, NNReal.coe_rpow, hs, CFC.rpow] using h

/-- The actual carrier is positively homogeneous of degree one. -/
theorem carrierPower_smul {β t : ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    (ht : 0 ≤ t) {M : Matrix n n ℂ} (hM : M.PosSemidef) :
    carrierPower β (t • M) = t • carrierPower β M := by
  by_cases ht0 : t = 0
  · simp [ht0, carrierPower_zero hβ]
  have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
  rw [carrierPower, realTrace_smul, matrix_rpow_smul hM ht (sub_nonneg.mpr hβ1.le)]
  change (t * realTrace M) ^ β • (t ^ (1 - β) • CFC.rpow M (1 - β)) = _
  rw [Real.mul_rpow ht (realTrace_nonneg hM)]
  have he : t ^ β * t ^ (1 - β) = t := by
    rw [← Real.rpow_add htpos, show β + (1 - β) = 1 by ring, Real.rpow_one]
  simp only [carrierPower, smul_smul]
  congr 1
  calc
    (t ^ β * realTrace M ^ β) * t ^ (1 - β) =
        (t ^ β * t ^ (1 - β)) * realTrace M ^ β := by ring
    _ = t * realTrace M ^ β := by rw [he]

omit [DecidableEq n] in
/-- A nonzero PSD matrix has positive trace. -/
theorem realTrace_pos_of_posSemidef_ne_zero {M : Matrix n n ℂ}
    (hM : M.PosSemidef) (hne : M ≠ 0) : 0 < realTrace M :=
  lt_of_le_of_ne (realTrace_nonneg hM)
    (Ne.symm (fun h => hne (posSemidef_eq_zero_of_realTrace_eq_zero hM h)))

/-- The trace perspective formula at every nonzero PSD input. -/
theorem carrierPower_eq_perspective {β : ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    {M : Matrix n n ℂ} (hM : M.PosSemidef) (ht : 0 < realTrace M) :
    carrierPower β M = (realTrace M) •
      CFC.rpow ((realTrace M)⁻¹ • M) (1 - β) := by
  have hn : ((realTrace M)⁻¹ • M).PosSemidef :=
    (smul_nonneg (inv_pos.mpr ht).le hM.nonneg).posSemidef
  have ht1 : realTrace ((realTrace M)⁻¹ • M) = 1 := by
    rw [realTrace_smul, inv_mul_cancel₀ ht.ne']
  calc
    carrierPower β M = carrierPower β ((realTrace M) • ((realTrace M)⁻¹ • M)) := by
      rw [smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
    _ = (realTrace M) • carrierPower β ((realTrace M)⁻¹ • M) :=
      carrierPower_smul hβ hβ1 ht.le hn
    _ = _ := by
      rw [carrierPower, ht1]
      change realTrace M • ((1 : ℝ) ^ β • CFC.rpow ((realTrace M)⁻¹ • M) (1 - β)) = _
      rw [Real.one_rpow, one_smul]

/-- The trace perspective is superadditive on the PSD cone. -/
theorem carrierPower_add_le {β : ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    carrierPower β A + carrierPower β B ≤ carrierPower β (A + B) := by
  by_cases hA0 : A = 0
  · simp [hA0, carrierPower_zero hβ]
  by_cases hB0 : B = 0
  · simp [hB0, carrierPower_zero hβ]
  let pA := realTrace A
  let pB := realTrace B
  let p := pA + pB
  have hpA : 0 < pA := realTrace_pos_of_posSemidef_ne_zero hA hA0
  have hpB : 0 < pB := realTrace_pos_of_posSemidef_ne_zero hB hB0
  have hp : 0 < p := add_pos hpA hpB
  have hAB : (A + B).PosSemidef := hA.add hB
  have htrace : realTrace (A + B) = p := realTrace_add A B
  have hAn : (pA⁻¹ • A).PosSemidef :=
    (smul_nonneg (inv_pos.mpr hpA).le hA.nonneg).posSemidef
  have hBn : (pB⁻¹ • B).PosSemidef :=
    (smul_nonneg (inv_pos.mpr hpB).le hB.nonneg).posSemidef
  have hw : pA / p + pB / p = 1 := by
    rw [← add_div]
    exact div_self hp.ne'
  have hnorm : (pA / p) • (pA⁻¹ • A) + (pB / p) • (pB⁻¹ • B) = p⁻¹ • (A + B) := by
    have hcA : pA / p * pA⁻¹ = p⁻¹ := by field_simp
    have hcB : pB / p * pB⁻¹ = p⁻¹ := by field_simp
    rw [smul_smul, smul_smul, hcA, hcB, smul_add]
  have hα : 1 - β ∈ Ioo 0 1 := ⟨sub_pos.mpr hβ1, by linarith⟩
  have h := smul_le_smul_of_nonneg_left
    (matrix_rpow_concave hα hAn hBn (div_pos hpA hp).le (div_pos hpB hp).le hw) hp.le
  rw [hnorm, smul_add, smul_smul, smul_smul] at h
  have hcA : p * (pA / p) = pA := by field_simp
  have hcB : p * (pB / p) = pB := by field_simp
  rw [hcA, hcB] at h
  rw [carrierPower_eq_perspective hβ hβ1 hA hpA,
    carrierPower_eq_perspective hβ hβ1 hB hpB,
    carrierPower_eq_perspective hβ hβ1 hAB (by rwa [htrace]), htrace]
  exact h

/-- The homogeneous carrier satisfies the weighted concavity inequality
for arbitrary nonnegative weights. -/
theorem carrierPower_weighted_add_le {β : ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a • carrierPower β A + b • carrierPower β B ≤ carrierPower β (a • A + b • B) := by
  rw [← carrierPower_smul hβ hβ1 ha hA, ← carrierPower_smul hβ hβ1 hb hB]
  exact carrierPower_add_le hβ hβ1
    (smul_nonneg ha hA.nonneg).posSemidef (smul_nonneg hb hB.nonneg).posSemidef

/-- Operator concavity of the actual trace-homogeneous carrier on the full PSD cone. -/
theorem concaveOn_carrierPower {β : ℝ} (hβ : 0 < β) (hβ1 : β < 1) :
    ConcaveOn ℝ {M : Matrix n n ℂ | M.PosSemidef} (carrierPower β) := by
  refine ⟨?_, ?_⟩
  · intro A hA B hB a b ha hb _hab
    exact (add_nonneg (smul_nonneg ha hA.nonneg) (smul_nonneg hb hB.nonneg)).posSemidef
  · intro A hA B hB a b ha hb _hab
    exact carrierPower_weighted_add_le hβ hβ1 hA hB ha hb

end HigherRankKS
