import AugmentedHigherRankKS.RuntimeRegularity.RelativePowerDerivatives
import HigherRankKS.CarrierConcavity

/-! Scalar affine power bounds obtained as the one-dimensional instance of
the actual resolvent-integral theorem. -/

open Matrix MatrixSpencer HigherRankKS Filter Set
open scoped Topology MatrixOrder ComplexOrder Matrix.Norms.L2Operator

noncomputable section
namespace HigherRankKSRuntime.RelativeScalarPower

local instance : CStarAlgebra (Matrix Unit Unit ℂ) := {}

theorem scalar_power_identity {p α : ℝ} (hp : 0 ≤ p) (hα : 0 ≤ α) :
    realTrace (CFC.rpow (p • (1 : Matrix Unit Unit ℂ)) α) = p ^ α := by
  rw [matrix_rpow_smul Matrix.PosDef.one.posSemidef hp hα]
  simp only [CFC.rpow_eq_pow, CFC.one_rpow, realTrace_smul]
  simp [realTrace, Matrix.trace]

theorem affine_power_relative {p u b α : ℝ} (hp : 0 < p) (hb : 0 ≤ b)
    (hu : |u| ≤ b * p) (hα : α ∈ Ioo 0 1) (k : ℕ) (hk : 0 < k) :
    |iteratedDeriv k (fun s : ℝ => (p + s * u) ^ α) 0| ≤
      (k.factorial : ℝ) * b ^ k * p ^ α := by
  let M : Matrix Unit Unit ℂ := p • 1
  let U : Matrix Unit Unit ℂ := u • 1
  have hM : M.PosDef := Matrix.PosDef.one.smul hp
  have hU : U.IsHermitian := by
    change (u • (1 : Matrix Unit Unit ℂ))ᴴ = u • (1 : Matrix Unit Unit ℂ)
    simp only [Matrix.conjTranspose_smul, star_trivial, Matrix.conjTranspose_one]
  have hlo : (-b) • M ≤ U := by
    change (-b) • (p • (1 : Matrix Unit Unit ℂ)) ≤ u • (1 : Matrix Unit Unit ℂ)
    rw [smul_smul]
    exact smul_le_smul_of_nonneg_right (by linarith [(abs_le.mp hu).1]) zero_le_one
  have hhi : U ≤ b • M := by
    change u • (1 : Matrix Unit Unit ℂ) ≤ b • (p • (1 : Matrix Unit Unit ℂ))
    rw [smul_smul]
    exact smul_le_smul_of_nonneg_right (abs_le.mp hu).2 zero_le_one
  have hbnd := RelativePowerDerivatives.power_derivative_relative hα hM hU hb hlo hhi k hk
  have hl := realTrace_mul_mono (Matrix.PosDef.one.posSemidef :
    (1 : Matrix Unit Unit ℂ).PosSemidef) hbnd.1
  have hh := realTrace_mul_mono (Matrix.PosDef.one.posSemidef :
    (1 : Matrix Unit Unit ℂ).PosSemidef) hbnd.2
  simp only [Matrix.one_mul, realTrace_smul] at hl hh
  have hs : ContDiffAt ℝ k (fun s : ℝ => CFC.rpow (M + s • U) α) 0 :=
    HigherRankKS.PowerIntegralDerivatives.contDiffAt_power_curve hα hM hU k
  have ht := HigherRankKS.WeightedCompactIntegral.iteratedDeriv_clm
    (realTraceCLM (n := Unit)) hs
  simp only [realTraceCLM_apply] at ht
  have hevent : ∀ᶠ s in 𝓝 (0 : ℝ), 0 < p + s * u := by
    have hc : Continuous (fun s : ℝ => p + s * u) := by fun_prop
    exact hc.continuousAt.eventually (Ioi_mem_nhds (by simpa using hp))
  have heq : (fun s : ℝ => realTrace (CFC.rpow (M + s • U) α)) =ᶠ[𝓝 0]
      (fun s : ℝ => (p + s * u) ^ α) := by
    filter_upwards [hevent] with s hsp
    have he : M + s • U = (p + s * u) • (1 : Matrix Unit Unit ℂ) := by
      dsimp [M, U]
      rw [smul_smul, add_smul]
    rw [he, scalar_power_identity hsp.le hα.1.le]
  have hd : realTrace (iteratedDeriv k (fun s : ℝ => CFC.rpow (M + s • U) α) 0) =
      iteratedDeriv k (fun s : ℝ => (p + s * u) ^ α) 0 := by
    rw [← ht]
    exact heq.iteratedDeriv_eq k
  have hbase : realTrace (CFC.rpow M α) = p ^ α := scalar_power_identity hp.le hα.1.le
  rw [hd, hbase] at hl hh
  exact abs_le.mpr ⟨by linarith, hh⟩

end HigherRankKSRuntime.RelativeScalarPower
