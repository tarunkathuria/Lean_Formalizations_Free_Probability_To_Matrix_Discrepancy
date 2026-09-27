import MatrixSpencer.KSEighthManuscriptLDL
import MatrixSpencer.MSManuscriptPaidStep


open Matrix
open scoped BigOperators MatrixOrder
noncomputable section
namespace MatrixSpencer.MSManuscriptNumericalShort
open InverseComparison
variable {d : ℕ}

def short (C : Matrix (Fin d) (Fin d) ℝ) (u : Fin d → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  if quadratic C u=0 then C else C-(quadratic C u)⁻¹ • realRankOne (C*ᵥu)

/-- The guarded data implement the usual totalized scalar formula exactly. -/
theorem short_eq (C : Matrix (Fin d) (Fin d) ℝ) (u : Fin d → ℝ) :
    short C u=C-(quadratic C u)⁻¹ • realRankOne (C*ᵥu) := by
  unfold short
  split_ifs with hq
  · simp [hq]
  · rfl

theorem short_quadratic (C : Matrix (Fin d) (Fin d) ℝ) (u x : Fin d → ℝ) :
    quadratic (short C u) x=quadratic C x-(quadratic C u)⁻¹*(x⬝ᵥ(C*ᵥu))^2 := by
  simp only [short_eq,quadratic,Matrix.sub_mulVec,Matrix.smul_mulVec,dotProduct_sub,
    dotProduct_smul,realRankOne,Matrix.vecMulVec_mulVec,op_smul_eq_smul]
  rw [dotProduct_comm (C*ᵥu) x]
  simp only [smul_eq_mul]
  ring

theorem mulVec_zero_of_quadratic_zero (C : Matrix (Fin d) (Fin d) ℝ) (hC : C.PosSemidef)
    (u : Fin d → ℝ) (hq : quadratic C u=0) : C*ᵥu=0 := by
  exact (hC.dotProduct_mulVec_zero_iff u).mp hq

theorem short_posSemidef (C : Matrix (Fin d) (Fin d) ℝ) (hC : C.PosSemidef) (u : Fin d → ℝ) :
    (short C u).PosSemidef := by
  by_cases hz : quadratic C u=0
  · simpa [short_eq,hz] using hC
  have hq : 0<quadratic C u := lt_of_le_of_ne (quadratic_nonneg hC u) (Ne.symm hz)
  refine ⟨?_,?_⟩
  · rw [short_eq]
    exact hC.isHermitian.sub ((realRankOne_posSemidef (C*ᵥu)).smul (inv_nonneg.mpr hq.le)).isHermitian
  intro x
  change 0≤quadratic (short C u) x
  rw [short_quadratic]
  have h := quadratic_nonneg hC (x-((x⬝ᵥ(C*ᵥu))/quadratic C u) • u)
  rw [quadratic_sub hC.isHermitian] at h
  simp only [quadratic,Matrix.mulVec_smul,dotProduct_smul,smul_dotProduct,smul_eq_mul] at h
  convert h using 1
  dsimp [quadratic]
  field_simp
  ring

theorem short_le (C : Matrix (Fin d) (Fin d) ℝ) (hC : C.PosSemidef) (u : Fin d → ℝ) :
    short C u≤C := by
  rw [short_eq]
  exact sub_le_self _ (((realRankOne_posSemidef (C*ᵥu)).smul (inv_nonneg.mpr (quadratic_nonneg hC u))).nonneg)

theorem short_annihilates (C : Matrix (Fin d) (Fin d) ℝ) (hC : C.PosSemidef) (u : Fin d → ℝ) :
    short C u*ᵥu=0 := by
  by_cases hz : quadratic C u=0
  · simpa only [short_eq,hz,_root_.inv_zero,zero_smul,sub_zero] using mulVec_zero_of_quadratic_zero C hC u hz
  simp only [short_eq,Matrix.sub_mulVec,Matrix.smul_mulVec,realRankOne,Matrix.vecMulVec_mulVec,op_smul_eq_smul]
  rw [dotProduct_comm (C*ᵥu) u]
  change C*ᵥu-(quadratic C u)⁻¹ • (quadratic C u • (C*ᵥu))=0
  rw [smul_smul,inv_mul_cancel₀ hz,one_smul,sub_self]

theorem short_preserves_annihilator (C : Matrix (Fin d) (Fin d) ℝ) (hC : C.IsHermitian)
    (u v : Fin d → ℝ) (hv : C*ᵥv=0) : short C u*ᵥv=0 := by
  simp only [short_eq,Matrix.sub_mulVec,Matrix.smul_mulVec,realRankOne,Matrix.vecMulVec_mulVec,hv,op_smul_eq_smul]
  have he : (C*ᵥu)⬝ᵥv=0 := by
    rw [dotProduct_comm,symmetric_pairing hC v u,hv,dotProduct_zero]
  rw [he,zero_smul,smul_zero,sub_zero]

theorem short_trace_loss (C : Matrix (Fin d) (Fin d) ℝ) (hC : C.PosSemidef)
    (hC1 : C≤1) (u : Fin d → ℝ) : realTrace C-realTrace (short C u)≤1 := by
  let v := C*ᵥu
  let E : ℝ := ∑ i,(v i)^2
  have htrace : realTrace C-realTrace (short C u)=(quadratic C u)⁻¹*E := by
    simp only [short_eq,realTrace_sub,realTrace_smul]
    have he : realTrace (realRankOne (C*ᵥu))=E := by
      simp only [realTrace,realRankOne,Matrix.trace,Matrix.diag,Matrix.vecMulVec_apply,E,v,pow_two]
      rfl
    rw [he]
    ring
  rw [htrace]
  by_cases hE : E=0
  · simp [hE]
  have hEpos : 0<E := lt_of_le_of_ne (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (Ne.symm hE)
  have hD : (quadratic C u)⁻¹ • realRankOne v≤C := by
    apply Matrix.le_iff.mpr
    simpa only [short_eq,v] using short_posSemidef C hC u
  have h := quadratic_mono (hD.trans hC1) v
  simp only [quadratic,Matrix.smul_mulVec,realRankOne,Matrix.vecMulVec_mulVec,
    dotProduct_smul,Matrix.one_mulVec,op_smul_eq_smul,smul_eq_mul] at h
  have he : v⬝ᵥv=E := by simp only [dotProduct,E,pow_two]
  rw [he] at h
  apply (mul_le_mul_iff_left₀ hEpos).mp
  simpa only [mul_assoc,one_mul,quadratic] using h

/-- This is the greatest PSD matrix below C annihilating the supplied constraint. -/
theorem short_maximal (C B : Matrix (Fin d) (Fin d) ℝ) (hC : C.PosSemidef)
    (hB : B.PosSemidef) (hBC : B≤C) (u : Fin d → ℝ) (hBu : B*ᵥu=0) : B≤short C u := by
  by_cases hz : quadratic C u=0
  · simpa [short_eq,hz] using hBC
  apply le_of_quadratic_le hB.isHermitian (short_posSemidef C hC u).isHermitian
  intro x
  let t := (x⬝ᵥ(C*ᵥu))/quadratic C u
  have hb : quadratic B (x-t • u)=quadratic B x := by
    rw [quadratic_sub hB.isHermitian]
    simp only [quadratic,Matrix.mulVec_smul,hBu,smul_zero,dotProduct_zero,mul_zero,sub_zero,add_zero]
  have h := quadratic_mono hBC (x-t • u)
  rw [hb,quadratic_sub hC.isHermitian] at h
  rw [short_quadratic]
  convert h using 1
  simp only [quadratic,Matrix.mulVec_smul,dotProduct_smul,smul_dotProduct,smul_eq_mul]
  dsimp [t,quadratic]
  field_simp
  ring

end MatrixSpencer.MSManuscriptNumericalShort
