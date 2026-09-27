import MatrixSpencer.KSSylvesterOrder
import MatrixSpencer.SingularDensityCalculus

/-!
# Relative upper curvature for the actual Kraus fidelity

The generalized transport equation preserves matrix positivity. Its actual
derivative obeys relative order and energy bounds, yielding a Hessian bound
with no source spectral gap. The final theorem includes singular sources
through the existing exact support-compression identity.
-/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSFidelityUpper
variable {n : Type*} [Fintype n] [DecidableEq n]
local instance : CStarAlgebra (Matrix n n ℂ) := {}

/-- Positivity for the actual generalized transport Sylvester equation. -/
theorem transport_solution_posSemidef {M T U : Matrix n n ℂ}
    (hM : M.PosDef) (hT : T.PosDef) (hU : U.IsHermitian)
    (hB : (T * M * U + U * M * T).PosSemidef) : U.PosSemidef := by
  let P := CFC.sqrt M
  have hP : P.PosDef := hM.posDef_sqrt
  have hPP : P * P = M := CFC.sqrt_mul_sqrt_self M hM.posSemidef.nonneg
  have hPiP : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P (P.isUnit_iff_isUnit_det.mp hP.isUnit)
  have hPPi : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P (P.isUnit_iff_isUnit_det.mp hP.isUnit)
  have hW : (P * U * P).IsHermitian := by
    simpa only [hP.isHermitian.eq] using Matrix.isHermitian_mul_mul_conjTranspose P hU
  have hQ : (P * T * P).PosDef := transportSylvesterCore_posDef M T hM hT
  have hB' : ((P * T * P) * (P * U * P) + (P * U * P) * (P * T * P)).PosSemidef := by
    have heq : (P * T * P) * (P * U * P) + (P * U * P) * (P * T * P) =
        P * (T * M * U + U * M * T) * P := by
      rw [← hPP]
      noncomm_ring
    rw [heq]
    simpa only [hP.isHermitian.eq] using hB.mul_mul_conjTranspose_same P
  have hp := KSSylvesterOrder.posSemidef_of_sylvester_posSemidef hQ hW hB'
  have hh := hp.mul_mul_conjTranspose_same P⁻¹
  have heq : P⁻¹ * (P * U * P) * (P⁻¹)ᴴ = U := by
    rw [Matrix.conjTranspose_nonsing_inv, hP.isHermitian.eq]
    calc P⁻¹ * (P * U * P) * P⁻¹ = (P⁻¹ * P) * U * (P * P⁻¹) := by noncomm_ring
      _ = _ := by rw [hPiP, hPPi, Matrix.one_mul, Matrix.mul_one]
  rwa [heq] at hh

/-- Relative control for the generalized transport equation. -/
theorem transport_solution_relative_bounds {M T U : Matrix n n ℂ}
    (hM : M.PosDef) (hT : T.PosDef) (hU : U.IsHermitian) (δ : ℝ)
    (hlo : -(2 * δ) • (T * M * T) ≤ T * M * U + U * M * T)
    (hhi : T * M * U + U * M * T ≤ (2 * δ) • (T * M * T)) :
    -δ • T ≤ U ∧ U ≤ δ • T := by
  have hδ : (δ • T).IsHermitian := by
    change (δ • T)ᴴ = δ • T
    simp only [Matrix.conjTranspose_smul, star_trivial, hT.isHermitian.eq]
  constructor
  · have h := transport_solution_posSemidef hM hT (hU.add hδ) (show
        (T * M * (U + δ • T) + (U + δ • T) * M * T).PosSemidef from ?_)
    · have hn := h.nonneg
      rw [← neg_le_iff_add_nonneg'] at hn
      simpa only [neg_smul, neg_neg] using neg_le_neg hn
    · apply Matrix.nonneg_iff_posSemidef.mp
      have heq : T * M * (U + δ • T) + (U + δ • T) * M * T =
          (T * M * U + U * M * T) - (-(2 * δ) • (T * M * T)) := by
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
          Matrix.smul_mul, neg_smul, sub_neg_eq_add]
        module
      rw [heq]
      exact sub_nonneg.mpr hlo
  · have h := transport_solution_posSemidef hM hT (hδ.sub hU) (show
        (T * M * (δ • T - U) + (δ • T - U) * M * T).PosSemidef from ?_)
    · exact sub_nonneg.mp h.nonneg
    · apply Matrix.nonneg_iff_posSemidef.mp
      have heq : T * M * (δ • T - U) + (δ • T - U) * M * T =
          (2 * δ) • (T * M * T) - (T * M * U + U * M * T) := by
        simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]
        module
      rw [heq]
      exact sub_nonneg.mpr hhi

/-- The transport response energy has a relative upper bound. -/
theorem transport_trace_energy_le {M T U : Matrix n n ℂ}
    (hM : M.PosDef) (hT : T.PosDef) (hU : U.IsHermitian) {δ : ℝ} (hδ : 0 ≤ δ)
    (hlo : -(2 * δ) • (T * M * T) ≤ T * M * U + U * M * T)
    (hhi : T * M * U + U * M * T ≤ (2 * δ) • (T * M * T)) :
    realTrace (T⁻¹ * U * M * U) ≤ δ ^ 2 * realTrace (M * T) := by
  obtain ⟨hl, hu⟩ := transport_solution_relative_bounds hM hT hU δ hlo hhi
  have h := realTrace_mul_mono hM.posSemidef
    (KSSylvesterOrder.weighted_square_le hT hU hδ hl hu)
  have heq : realTrace (M * (U * T⁻¹ * U)) = realTrace (T⁻¹ * U * M * U) := by
    calc realTrace (M * (U * T⁻¹ * U)) = realTrace ((M * U) * (T⁻¹ * U)) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [realTrace_mul_comm]; simp only [Matrix.mul_assoc]
  simpa only [Matrix.mul_smul, realTrace_smul, heq] using h

/-- Actual doubled fidelity has a source-gap-independent relative Hessian
bound when both inputs and both tangent directions are varied. -/
theorem doubleFidelity_negativeHessian_le (S M X Y : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) (hM : (M : Matrix n n ℂ).PosDef)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hXlo : -δ • (S : Matrix n n ℂ) ≤ (X : Matrix n n ℂ))
    (hXhi : (X : Matrix n n ℂ) ≤ δ • (S : Matrix n n ℂ))
    (hYlo : -δ • (M : Matrix n n ℂ) ≤ (Y : Matrix n n ℂ))
    (hYhi : (Y : Matrix n n ℂ) ≤ δ • (M : Matrix n n ℂ)) :
    -fderiv ℝ (fun P => fderiv ℝ (doubleFidelity (n := n)) P)
      (S, M) (X, Y) (X, Y) ≤ 2 * δ ^ 2 * fidelity (S : Matrix n n ℂ) (M : Matrix n n ℂ) := by
  let T := transportOptimizer (S : Matrix n n ℂ) (M : Matrix n n ℂ)
  let U := fderiv ℝ jointTransportOptimizer (S, M) (X, Y)
  have hT : T.PosDef := transportOptimizer_posDef hS hM
  have hU : U.IsHermitian := by
    dsimp [U]
    rw [← fderiv_jointHermitianTransport_coe S M X Y hS hM]
    exact (fderiv ℝ jointHermitianTransport (S, M) (X, Y)).property
  have heq : T * (M : Matrix n n ℂ) * T = (S : Matrix n n ℂ) := transportOptimizer_solve hS hM
  have hres : T * (M : Matrix n n ℂ) * U + U * (M : Matrix n n ℂ) * T =
      (X : Matrix n n ℂ) - T * (Y : Matrix n n ℂ) * T := by
    rw [add_comm]
    exact fderiv_jointTransportOptimizer_solve S M X Y hS hM
  have hTl : -δ • (S : Matrix n n ℂ) ≤ T * (Y : Matrix n n ℂ) * T := by
    simpa only [Matrix.mul_smul, Matrix.smul_mul, heq] using
      KrausContraction.congruence_mono hYlo T hT.isHermitian
  have hTu : T * (Y : Matrix n n ℂ) * T ≤ δ • (S : Matrix n n ℂ) := by
    simpa only [Matrix.mul_smul, Matrix.smul_mul, heq] using
      KrausContraction.congruence_mono hYhi T hT.isHermitian
  have hlo : -(2 * δ) • (T * (M : Matrix n n ℂ) * T) ≤
      T * (M : Matrix n n ℂ) * U + U * (M : Matrix n n ℂ) * T := by
    rw [heq, hres]
    have hh := sub_le_sub hXlo hTu
    convert hh using 1; module
  have hhi : T * (M : Matrix n n ℂ) * U + U * (M : Matrix n n ℂ) * T ≤
      (2 * δ) • (T * (M : Matrix n n ℂ) * T) := by
    rw [heq, hres]
    have hh := sub_le_sub hXhi hTl
    convert hh using 1; module
  have hb := transport_trace_energy_le hM hT hU hδ hlo hhi
  rw [trace_transportOptimizer_eq_fidelity hS hM] at hb
  rw [fderiv_fderiv_doubleFidelity_quadratic S M X Y hS hM]
  change -(-2 * realTrace (T⁻¹ * U * (M : Matrix n n ℂ) * U)) ≤ _
  linarith

variable {m ι : Type*} [Fintype m] [Fintype ι]

omit [DecidableEq n] in
/-- Compression by a rectangular matrix preserves the actual matrix order. -/
theorem compression_mono (V : Matrix n m ℂ) {A B : Matrix n n ℂ} (hAB : A ≤ B) :
    Vᴴ * A * V ≤ Vᴴ * B * V := by
  apply Matrix.le_iff.mpr
  simpa only [Matrix.mul_sub, Matrix.sub_mul] using
    (Matrix.le_iff.mp hAB).conjTranspose_mul_mul_same V

/-- The actual Kraus-source fidelity satisfies the relative curvature bound,
including sources with nontrivial kernel. -/
theorem kraus_negativeHessian_relative_le (B : ι → Matrix n n ℂ)
    (S X : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hlo : -δ • (S : Matrix n n ℂ) ≤ (X : Matrix n n ℂ))
    (hhi : (X : Matrix n n ℂ) ≤ δ • (S : Matrix n n ℂ)) :
    -fderiv ℝ (fun A => fderiv ℝ (krausSourceFidelity B) A) S X X ≤
      2 * δ ^ 2 * fidelity S (krausChannel B S) := by
  rw [fderiv_fderiv_krausSourceFidelity_apply_source_unrestricted B S X X hS]
  have hd := krausCompressedDensity_posDef B hS
  have hm : (krausReducedSourceCLM B S : Matrix (Fin (Module.finrank ℂ (krausSupport B))) (Fin (Module.finrank ℂ (krausSupport B))) ℂ).PosDef := by
    simpa only [krausReducedSourceCLM_coe] using krausCompressedSource_posDef B hS
  have hdl : -δ • (krausReducedDensityCLM B S : Matrix (Fin (Module.finrank ℂ (krausSupport B))) (Fin (Module.finrank ℂ (krausSupport B))) ℂ) ≤
      (krausReducedDensityCLM B X : Matrix (Fin (Module.finrank ℂ (krausSupport B))) (Fin (Module.finrank ℂ (krausSupport B))) ℂ) := by
    simpa only [krausReducedDensityCLM_coe, krausCompressedDensity,
      Matrix.mul_smul, Matrix.smul_mul] using compression_mono (krausSupportEmbedding B) hlo
  have hdu : (krausReducedDensityCLM B X : Matrix (Fin (Module.finrank ℂ (krausSupport B))) (Fin (Module.finrank ℂ (krausSupport B))) ℂ) ≤
      δ • (krausReducedDensityCLM B S : Matrix (Fin (Module.finrank ℂ (krausSupport B))) (Fin (Module.finrank ℂ (krausSupport B))) ℂ) := by
    simpa only [krausReducedDensityCLM_coe, krausCompressedDensity,
      Matrix.mul_smul, Matrix.smul_mul] using compression_mono (krausSupportEmbedding B) hhi
  have hml : -δ • (krausReducedSourceCLM B S : Matrix (Fin (Module.finrank ℂ (krausSupport B))) (Fin (Module.finrank ℂ (krausSupport B))) ℂ) ≤
      (krausReducedSourceCLM B X : Matrix (Fin (Module.finrank ℂ (krausSupport B))) (Fin (Module.finrank ℂ (krausSupport B))) ℂ) := by
    have hh := compression_mono (krausSupportEmbedding B) (KrausContraction.channel_mono B hlo)
    simpa only [krausReducedSourceCLM_coe, krausCompressedSource_eq_compression,
      KrausContraction.channel_real_smul, Matrix.mul_smul, Matrix.smul_mul] using hh
  have hmu : (krausReducedSourceCLM B X : Matrix (Fin (Module.finrank ℂ (krausSupport B))) (Fin (Module.finrank ℂ (krausSupport B))) ℂ) ≤
      δ • (krausReducedSourceCLM B S : Matrix (Fin (Module.finrank ℂ (krausSupport B))) (Fin (Module.finrank ℂ (krausSupport B))) ℂ) := by
    have hh := compression_mono (krausSupportEmbedding B) (KrausContraction.channel_mono B hhi)
    simpa only [krausReducedSourceCLM_coe, krausCompressedSource_eq_compression,
      KrausContraction.channel_real_smul, Matrix.mul_smul, Matrix.smul_mul] using hh
  have hh := doubleFidelity_negativeHessian_le (krausReducedDensityCLM B S)
    (krausReducedSourceCLM B S) (krausReducedDensityCLM B X) (krausReducedSourceCLM B X)
    hd hm hδ hdl hdu hml hmu
  rw [fidelity_kraus_support_compression B hS.posSemidef]
  simpa only [krausReducedDensityCLM_coe, krausReducedSourceCLM_coe] using hh

end MatrixSpencer.KSFidelityUpper
