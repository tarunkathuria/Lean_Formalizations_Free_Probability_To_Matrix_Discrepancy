import AugmentedHigherRankKS.RuntimeRegularity.ResolventHigherDerivatives
import MatrixSpencer.KSOptimizerFloor
import MatrixSpencer.KSFidelityUpper
import MatrixSpencer.KSBalancedSpin

/-! Resolvent words have two-sided relative order bounds. The estimate
normalizes the input direction, not the smallest eigenvalue of its carrier. -/

open Matrix MatrixSpencer
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

noncomputable section
namespace HigherRankKSRuntime.RelativeResolventWords
open ResolventHigherDerivatives

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
local instance : CStarAlgebra (Matrix n n ℂ) := {}

def middle (C B : Matrix n n ℂ) (k : ℕ) : Matrix n n ℂ := (C * B) ^ k * C

theorem middle_isHermitian {C B : Matrix n n ℂ}
    (hC : C.IsHermitian) (hB : B.IsHermitian) (k : ℕ) :
    (middle C B k).IsHermitian := by
  change (middle C B k)ᴴ = middle C B k
  simp only [middle, Matrix.conjTranspose_mul, Matrix.conjTranspose_pow, hC.eq, hB.eq]
  exact (mul_pow_mul C B k).symm

theorem middle_succ (C B : Matrix n n ℂ) (k : ℕ) :
    middle C B (k + 1) = middle C B k * B * C := by
  simp only [middle, pow_succ, Matrix.mul_assoc]

theorem middle_norm {C B : Matrix n n ℂ} {b : ℝ}
    (hC : ‖C‖ ≤ b) (hB : ‖B‖ ≤ 1) (k : ℕ) : ‖middle C B k‖ ≤ b ^ (k + 1) := by
  have hb : 0 ≤ b := (norm_nonneg C).trans hC
  have hCB : ‖C * B‖ ≤ b := (norm_mul_le C B).trans
    (by simpa using mul_le_mul hC hB (norm_nonneg _) hb)
  calc
    ‖middle C B k‖ ≤ ‖C * B‖ ^ k * ‖C‖ := (norm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right (norm_pow_le _ _) (norm_nonneg _))
    _ ≤ b ^ k * b := mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hCB _) hC
      (norm_nonneg _) (pow_nonneg hb _)
    _ = _ := (pow_succ b k).symm

theorem word_factorization (R S C U : Matrix n n ℂ) (hU : U = S * C * S) (k : ℕ) :
    word R U (k + 1) = (R * S) * middle C (S * R * S) k * (S * R) := by
  induction k with
  | zero => simp only [word, middle, pow_zero, Matrix.one_mul, hU, Matrix.mul_assoc]
  | succ k ih =>
    rw [word, ih, middle_succ, hU]
    simp only [Matrix.mul_assoc]

theorem word_relative_of_factorization
    {R S C U K : Matrix n n ℂ} (hR : R.IsHermitian) (hS : S.IsHermitian)
    (hC : C.IsHermitian) (hU : U = S * C * S) {b t : ℝ}
    (hb : 0 ≤ b) (ht : 0 ≤ t) (hCn : ‖C‖ ≤ b) (hBn : ‖S * R * S‖ ≤ 1)
    (hbase : t • (R * (S * S) * R) ≤ K) (k : ℕ) :
    -(b ^ (k + 1)) • K ≤ t • word R U (k + 1) ∧
      t • word R U (k + 1) ≤ b ^ (k + 1) • K := by
  have hB : (S * R * S).IsHermitian := by
    simpa only [hS.eq] using Matrix.isHermitian_mul_mul_conjTranspose S hR
  have hm := middle_isHermitian hC hB k
  have hn := middle_norm hCn hBn k
  have hu : middle C (S * R * S) k ≤ b ^ (k + 1) • (1 : Matrix n n ℂ) := by
    have h := (show IsSelfAdjoint _ from hm).le_algebraMap_norm_self
    rw [Algebra.algebraMap_eq_smul_one] at h
    exact h.trans (smul_le_smul_of_nonneg_right hn zero_le_one)
  have hl : -(b ^ (k + 1)) • (1 : Matrix n n ℂ) ≤ middle C (S * R * S) k := by
    have h := (show IsSelfAdjoint _ from hm).neg_algebraMap_norm_le_self
    rw [Algebra.algebraMap_eq_smul_one, ← neg_smul] at h
    exact (smul_le_smul_of_nonneg_right (neg_le_neg hn) zero_le_one).trans h
  have hconj : (S * R)ᴴ = R * S := by simp only [Matrix.conjTranspose_mul, hS.eq, hR.eq]
  have hup := KSFidelityUpper.compression_mono (S * R) hu
  have hlo := KSFidelityUpper.compression_mono (S * R) hl
  rw [hconj, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    ← word_factorization R S C U hU k] at hup hlo
  have he : R * S * (S * R) = R * (S * S) * R := by simp only [Matrix.mul_assoc]
  rw [he] at hup hlo
  have hup' := smul_le_smul_of_nonneg_left hup ht
  have hlo' := smul_le_smul_of_nonneg_left hlo ht
  have hbu := smul_le_smul_of_nonneg_left hbase (pow_nonneg hb (k + 1))
  have hbl := neg_le_neg hbu
  have hlo'' : -(b ^ (k + 1) • t • (R * (S * S) * R)) ≤
      t • word R U (k + 1) := by
    convert hlo' using 1 <;> module
  have hup'' : t • word R U (k + 1) ≤
      b ^ (k + 1) • t • (R * (S * S) * R) := by
    convert hup' using 1 <;> module
  constructor
  · simpa only [neg_smul] using hbl.trans hlo''
  · exact hup''.trans hbu

theorem normalized_direction {M U : Matrix n n ℂ}
    (hM : M.PosDef) (hU : U.IsHermitian) {b : ℝ} (hb : 0 ≤ b)
    (hlo : (-b) • M ≤ U) (hhi : U ≤ b • M) :
    let S := CFC.sqrt M
    let C := S⁻¹ * U * S⁻¹
    C.IsHermitian ∧ ‖C‖ ≤ b ∧ U = S * C * S := by
  dsimp only
  let S := CFC.sqrt M
  have hS : S.IsHermitian := hM.posDef_sqrt.isHermitian
  letI : Invertible S := hM.posDef_sqrt.isUnit.invertible
  have hSi : S⁻¹ * S = 1 := Matrix.inv_mul_of_invertible S
  have hSi' : S * S⁻¹ = 1 := Matrix.mul_inv_of_invertible S
  have hSS : S * S = M := CFC.sqrt_mul_sqrt_self M hM.posSemidef.nonneg
  have hnorm : S⁻¹ * M * S⁻¹ = 1 := by
    rw [← hSS]
    simp only [← Matrix.mul_assoc, hSi, Matrix.one_mul, hSi']
  have hC : (S⁻¹ * U * S⁻¹).IsHermitian := by
    simpa only [hS.inv.eq] using Matrix.isHermitian_mul_mul_conjTranspose S⁻¹ hU
  refine ⟨hC, ?_, ?_⟩
  · apply KrausContraction.norm_le_of_order_interval hC hb
    · have h := KrausContraction.congruence_mono hlo S⁻¹ hS.inv
      simpa only [Matrix.mul_smul, Matrix.smul_mul, hnorm] using h
    · have h := KrausContraction.congruence_mono hhi S⁻¹ hS.inv
      simpa only [Matrix.mul_smul, Matrix.smul_mul, hnorm] using h
  · change U = S * (S⁻¹ * U * S⁻¹) * S
    simp only [← Matrix.mul_assoc, hSi', Matrix.one_mul]
    rw [Matrix.mul_assoc, hSi, Matrix.mul_one]

theorem normalized_resolvent_norm {M : Matrix n n ℂ} (hM : M.PosDef)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖CFC.sqrt M * HigherRankKS.resolvent M t * CFC.sqrt M‖ ≤ 1 := by
  have hR := HigherRankKS.resolvent_posDef hM ht
  have hS := hM.posDef_sqrt.isHermitian
  have hB : (CFC.sqrt M * HigherRankKS.resolvent M t * CFC.sqrt M).PosSemidef := by
    simpa only [hS.eq] using hR.posSemidef.mul_mul_conjTranspose_same (CFC.sqrt M)
  have hi : HigherRankKS.resolvent M t ≤ M⁻¹ := by
    apply KSOptimizerFloor.inverse_order hM
      (hM.add_posSemidef (smul_nonneg ht (Matrix.PosDef.one.posSemidef.nonneg)).posSemidef)
    exact le_add_of_nonneg_right (smul_nonneg ht zero_le_one)
  have hc := KrausContraction.congruence_mono hi (CFC.sqrt M) hS
  rw [KSBalancedSpin.sqrt_mul_inverse_mul_sqrt hM] at hc
  exact (CStarAlgebra.norm_le_iff_le_algebraMap _ zero_le_one hB.nonneg).mpr (by simpa using hc)

theorem resolvent_base_bound {M : Matrix n n ℂ} (hM : M.PosDef)
    {t : ℝ} (ht : 0 ≤ t) :
    t • (HigherRankKS.resolvent M t * M * HigherRankKS.resolvent M t) ≤
      HigherRankKS.resolventKernel M t := by
  let R := HigherRankKS.resolvent M t
  let K := HigherRankKS.resolventKernel M t
  have hR : R.IsHermitian := (HigherRankKS.resolvent_posDef hM ht).isHermitian
  have hK : K.IsHermitian := by
    change (1 - t • R)ᴴ = 1 - t • R
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
      Matrix.conjTranspose_smul, star_trivial, hR.eq]
  have hmul : K = M * R := HigherRankKS.resolventKernel_eq_mul hM ht
  have hid : K * K = K - t • (R * M * R) := by
    calc
      K * K = (1 - t • R) * (M * R) := by rw [← hmul]; rfl
      _ = M * R - t • (R * M * R) := by
        simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_assoc]
      _ = K - t • (R * M * R) := by rw [hmul]
  have hp := Matrix.posSemidef_conjTranspose_mul_self K
  rw [hK.eq, hid] at hp
  exact sub_nonneg.mp hp.nonneg

theorem resolvent_word_relative {M U : Matrix n n ℂ}
    (hM : M.PosDef) (hU : U.IsHermitian) {b t : ℝ} (hb : 0 ≤ b) (ht : 0 ≤ t)
    (hlo : (-b) • M ≤ U) (hhi : U ≤ b • M) (k : ℕ) :
    -(b ^ (k + 1)) • HigherRankKS.resolventKernel M t ≤
        t • word (HigherRankKS.resolvent M t) U (k + 1) ∧
      t • word (HigherRankKS.resolvent M t) U (k + 1) ≤
        b ^ (k + 1) • HigherRankKS.resolventKernel M t := by
  obtain ⟨hC, hCn, hUeq⟩ := normalized_direction hM hU hb hlo hhi
  exact word_relative_of_factorization (HigherRankKS.resolvent_posDef hM ht).isHermitian
    hM.posDef_sqrt.isHermitian hC hUeq hb ht hCn (normalized_resolvent_norm hM ht)
    (by simpa only [CFC.sqrt_mul_sqrt_self M hM.posSemidef.nonneg] using
      resolvent_base_bound hM ht) k

end HigherRankKSRuntime.RelativeResolventWords
