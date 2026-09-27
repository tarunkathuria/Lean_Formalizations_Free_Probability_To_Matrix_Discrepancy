import AugmentedHigherRankKS.RuntimeRegularity.RelativeResolventWords

/-! Uniform relative derivatives of the actual fractional matrix power,
obtained by differentiating its proved resolvent integral. -/

open Matrix MatrixSpencer HigherRankKS Filter MeasureTheory Set
open scoped Topology BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

noncomputable section
namespace HigherRankKSRuntime.RelativePowerDerivatives
open ResolventHigherDerivatives RelativeResolventWords
open HigherRankKS.PowerIntegralRepresentation HigherRankKS.PowerIntegralDerivatives

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
local instance : CStarAlgebra (Matrix n n ℂ) := {}

theorem kernel_derivative_relative {M U : Matrix n n ℂ}
    (hM : M.PosDef) (hU : U.IsHermitian) {b t : ℝ} (hb : 0 ≤ b) (ht : 0 ≤ t)
    (hlo : (-b) • M ≤ U) (hhi : U ≤ b • M) (k : ℕ) (hk : 0 < k) :
    -((k.factorial : ℝ) * b ^ k) • resolventKernel M t ≤
        iteratedDeriv k (fun s : ℝ => resolventKernel (M + s • U) t) 0 ∧
      iteratedDeriv k (fun s : ℝ => resolventKernel (M + s • U) t) 0 ≤
        ((k.factorial : ℝ) * b ^ k) • resolventKernel M t := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  simp only [Nat.succ_eq_add_one] at hk ⊢
  have hword := resolvent_word_relative hM hU hb ht hlo hhi j
  have hl := smul_le_smul_of_nonneg_left hword.1
    (Nat.cast_nonneg (j + 1).factorial : (0 : ℝ) ≤ _)
  have hu := smul_le_smul_of_nonneg_left hword.2
    (Nat.cast_nonneg (j + 1).factorial : (0 : ℝ) ≤ _)
  rw [iteratedDeriv_resolventKernel M U (j + 1) hM ht (Nat.succ_pos _)]
  rcases neg_one_pow_eq_or ℝ (j + 1 + 1) with hs | hs
  · rw [hs]
    constructor
    · convert hl using 1 <;> module
    · convert hu using 1 <;> module
  · rw [hs]
    constructor
    · convert neg_le_neg hu using 1 <;> module
    · convert neg_le_neg hl using 1 <;> module

theorem power_derivative_relative {α : ℝ} (hα : α ∈ Ioo 0 1)
    {M U : Matrix n n ℂ} (hM : M.PosDef) (hU : U.IsHermitian)
    {b : ℝ} (hb : 0 ≤ b) (hlo : (-b) • M ≤ U) (hhi : U ≤ b • M)
    (k : ℕ) (hk : 0 < k) :
    -((k.factorial : ℝ) * b ^ k) • CFC.rpow M α ≤
        iteratedDeriv k (fun s : ℝ => CFC.rpow (M + s • U) α) 0 ∧
      iteratedDeriv k (fun s : ℝ => CFC.rpow (M + s • U) α) 0 ≤
        ((k.factorial : ℝ) * b ^ k) • CFC.rpow M α := by
  obtain ⟨μ, hμ⟩ := exists_scalarRepresentation hα
  obtain ⟨hbase, hbaseEq⟩ := resolvent_representation hα μ hμ M hM.posSemidef
  obtain ⟨hderiv, hderivEq⟩ := iteratedDeriv_power_integral hα μ hμ hM hU k
  let c : ℝ := (k.factorial : ℝ) * b ^ k
  let f := fun t : ℝ => t ^ (α - 1) •
    (M * (M + t • (1 : Matrix n n ℂ))⁻¹)
  let g := fun t : ℝ => t ^ (α - 1) •
    iteratedDeriv k (fun s : ℝ => resolventKernel (M + s • U) t) 0
  have hupper : (∫ t in Ioi 0, g t ∂μ) ≤ ∫ t in Ioi 0, c • f t ∂μ := by
    apply integral_mono_ae hderiv (hbase.smul c)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hu := smul_le_smul_of_nonneg_left
      (kernel_derivative_relative hM hU hb ht.le hlo hhi k hk).2
      (Real.rpow_nonneg ht.le (α - 1))
    rw [resolventKernel_eq_mul hM ht.le] at hu
    convert hu using 1 <;> dsimp [f, g, c, HigherRankKS.resolvent] <;> module
  have hlower : (∫ t in Ioi 0, (-c) • f t ∂μ) ≤ ∫ t in Ioi 0, g t ∂μ := by
    apply integral_mono_ae (hbase.smul (-c)) hderiv
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hl := smul_le_smul_of_nonneg_left
      (kernel_derivative_relative hM hU hb ht.le hlo hhi k hk).1
      (Real.rpow_nonneg ht.le (α - 1))
    rw [resolventKernel_eq_mul hM ht.le] at hl
    convert hl using 1 <;> dsimp [f, g, c, HigherRankKS.resolvent] <;> module
  rw [integral_smul] at hupper hlower
  rw [hbaseEq, hderivEq]
  exact ⟨hlower, hupper⟩

end HigherRankKSRuntime.RelativePowerDerivatives
