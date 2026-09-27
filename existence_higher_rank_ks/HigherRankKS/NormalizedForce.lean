import HigherRankKS.LegalResponse

/-! Exact coefficient identities for the normalized force and source variation. -/

open Matrix MatrixSpencer MatrixSpencer.KSFisher
open scoped BigOperators MatrixOrder ComplexOrder

noncomputable section
namespace HigherRankKS.NormalizedForce

variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]

def measurementFrame (V : ι → Matrix n n ℂ) (c : ι → ℝ) : ι → Matrix n n ℂ :=
  fun i => Real.sqrt (c i) • V i
def preparationFrame (O : ι → Matrix n n ℂ) (c p : ι → ℝ) : ι → Matrix n n ℂ :=
  fun i => (Real.sqrt (c i) / p i) • O i

omit [DecidableEq n] in
theorem force_identity (V : ι → Matrix n n ℂ) (J : Matrix n n ℂ)
    (c dc q y : ι → ℝ) (a : ℝ) :
    (∑ i, (a * Real.sqrt (c i) * y i) • (J * V i + (dc i * q i) • V i)) =
      a • (J * synthesis (measurementFrame V c) y -
        synthesis (measurementFrame V c)
          (Matrix.diagonal (fun i => -dc i * q i) *ᵥ y)) := by
  simp only [synthesis, measurementFrame, Matrix.mul_sum, Matrix.mul_smul, smul_add,
    smul_sub, smul_smul, Matrix.mulVec_diagonal, Finset.sum_add_distrib,
    Finset.smul_sum, ← Finset.sum_sub_distrib]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  module

omit [DecidableEq ι] [Fintype n] [DecidableEq n] in
theorem source_identity (O : ι → Matrix n n ℂ) (c dc p q y : ι → ℝ)
    (hp : ∀ i, p i ≠ 0) (hq : ∀ i, q i ≠ 0) (a : ℝ) :
    (∑ i, (dc i * (a * Real.sqrt (c i) * y i)) • O i) =
      (-a) • synthesis (preparationFrame O c p)
        (fun i => (p i / q i) * (-dc i * q i) * y i) := by
  simp only [synthesis, preparationFrame, Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  field_simp [hp i, hq i]

omit [DecidableEq ι] [DecidableEq n] in
theorem channel_identity (V O : ι → Matrix n n ℂ) (c p : ι → ℝ)
    (hc : ∀ i, 0 ≤ c i) (Y : Matrix n n ℂ) :
    TwoFrames.frameChannel (measurementFrame V c) (preparationFrame O c p) Y =
      ∑ i, (c i / p i * realTrace (V i * Y)) • O i := by
  simp only [TwoFrames.frameChannel, TwoFrames.measurement, synthesis,
    measurementFrame, preparationFrame, Matrix.smul_mul, realTrace_smul, smul_smul]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  calc
    _ = (Real.sqrt (c i) * Real.sqrt (c i)) / p i * realTrace (V i * Y) := by ring
    _ = _ := by rw [Real.mul_self_sqrt (hc i)]

end HigherRankKS.NormalizedForce
