import MatrixSpencer.KSFullManuscriptBlockBounds
import MatrixSpencer.KSComplexNorm
import MatrixSpencer.KSNumericalFidelity

/-! An entry-arithmetic source bound for every feasible SDP density. -/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSFullManuscriptSourceCap
variable {d : ℕ} {ι : Type*} [Fintype ι]
local instance : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}

def atomBound (B : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  KSNumericalFidelity.matrixBound (KSComplexTraceSqrt.realificationFin B)

def cap (B : ι → Matrix (Fin d) (Fin d) ℂ) : ℝ := 1+∑i, (atomBound (B i))^2

theorem atomBound_pos (B : Matrix (Fin d) (Fin d) ℂ) : 0 < atomBound B :=
  KSNumericalFidelity.matrixBound_pos _

theorem norm_le_atomBound (B : Matrix (Fin d) (Fin d) ℂ) : ‖B‖ ≤ atomBound B := by
  rw [← KSComplexNorm.realificationFin_norm B]
  exact KSNumericalFidelity.norm_le_matrixBound _

theorem cap_pos (B : ι → Matrix (Fin d) (Fin d) ℂ) : 0 < cap B := by
  unfold cap
  positivity

theorem source_norm_le (B : ι → Matrix (Fin d) (Fin d) ℂ)
    {S : Matrix (Fin d) (Fin d) ℂ} (hS : S ∈ densitySet) : ‖krausChannel B S‖ ≤ cap B := by
  have hs := density_norm_le_one hS
  have ht (i : ι) : ‖B i*S*(B i)ᴴ‖ ≤ (atomBound (B i))^2 := by
    have hn := norm_le_atomBound (B i)
    have hp := (atomBound_pos (B i)).le
    calc
      _ ≤ ‖B i‖*‖S‖*‖(B i)ᴴ‖ := (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ atomBound (B i)*1*atomBound (B i) := by
        apply mul_le_mul (mul_le_mul hn hs (norm_nonneg _) hp)
        · change ‖star (B i)‖ ≤ atomBound (B i)
          simpa only [norm_star] using hn
        · exact norm_nonneg _
        · positivity
      _ = _ := by ring
  calc
    _ ≤ ∑i, ‖B i*S*(B i)ᴴ‖ := norm_sum_le _ _
    _ ≤ ∑i, (atomBound (B i))^2 := Finset.sum_le_sum (fun i _ => ht i)
    _ ≤ cap B := by unfold cap; linarith

theorem source_le (B : ι → Matrix (Fin d) (Fin d) ℂ)
    {S : Matrix (Fin d) (Fin d) ℂ} (hS : S ∈ densitySet) :
    krausChannel B S ≤ cap B • (1 : Matrix (Fin d) (Fin d) ℂ) := by
  have hh := (CStarAlgebra.norm_le_iff_le_algebraMap _ (cap_pos B).le
    (krausChannel_posSemidef B hS.1).nonneg).mp (source_norm_le B hS)
  simpa only [Algebra.algebraMap_eq_smul_one] using hh

theorem regularized_source_le (B : ι → Matrix (Fin d) (Fin d) ℂ)
    {S : Matrix (Fin d) (Fin d) ℂ} (hS : S ∈ densitySet) (lam : ℝ) :
    krausChannel B S+lam • 1 ≤ (cap B+lam) • (1 : Matrix (Fin d) (Fin d) ℂ) := by
  simpa only [add_smul] using add_le_add_right (source_le B hS) (lam • 1)

end MatrixSpencer.KSFullManuscriptSourceCap
