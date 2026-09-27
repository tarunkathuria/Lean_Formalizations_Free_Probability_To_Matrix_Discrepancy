import MatrixSpencer.SpectralHighForcing

/-!
# The actual high Jordan frame trace budget

The high-high block decreases each force's weighted trace energy. Summation
and the actual fixed point give the frame trace budget without a separate
frame-budget premise or commutation with the Jordan square root.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder
open Matrix

noncomputable section
namespace MatrixSpencer
namespace HighFrameBudget

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n]

/-- Projection onto the physical high block decreases weighted Hermitian force energy. -/
lemma highForce_weighted_energy_le {P D : Matrix n n ℂ} (hP : P.PosSemidef)
    (hD : D.IsHermitian) (ε : ℝ) :
    realTrace (P * SpectralHighForcing.highForce hP.isHermitian ε D *
      SpectralHighForcing.highForce hP.isHermitian ε D) ≤ realTrace (P * D * D) := by
  let H := SpectralCutoff.high hP.isHermitian ε
  have hH : H.IsHermitian := SpectralCutoff.high_hermitian hP.isHermitian ε
  have hHH : H * H = H := SpectralCutoff.high_idempotent hP.isHermitian ε
  have hHP : (H * P * H).PosSemidef := by
    simpa only [hH.eq] using hP.mul_mul_conjTranspose_same H
  have hHPle : H * P * H ≤ P := by
    rw [SpectralCutoff.high_mul_P_mul_high]
    exact sub_le_self _ (SpectralCutoff.lowPart_posSemidef hP ε).nonneg
  have hDHD : D * H * D ≤ D * D := by
    simpa only [Matrix.mul_one] using KrausContraction.congruence_mono
      (SpectralCutoff.high_le_one hP.isHermitian ε) D hD
  have h₁ := realTrace_mul_mono hHP hDHD
  have hDD : (D * D).PosSemidef := by
    simpa only [hD.eq] using Matrix.posSemidef_conjTranspose_mul_self D
  have h₂ := realTrace_mul_mono hDD hHPle
  rw [realTrace_mul_comm (D * D) (H * P * H), realTrace_mul_comm (D * D) P] at h₂
  have he : realTrace (P * SpectralHighForcing.highForce hP.isHermitian ε D *
      SpectralHighForcing.highForce hP.isHermitian ε D) = realTrace ((H * P * H) * (D * H * D)) := by
    change realTrace (P * (H * D * H) * (H * D * H)) = _
    calc
      _ = realTrace ((P * H * D) * (H * H) * (D * H)) := by simp only [Matrix.mul_assoc]
      _ = realTrace ((P * H * D * H * D) * H) := by rw [hHH]; simp only [Matrix.mul_assoc]
      _ = _ := by
        simpa only [Matrix.mul_assoc] using realTrace_mul_comm (P * H * D * H * D) H
  rw [he]
  simpa only [Matrix.mul_assoc] using h₁.trans h₂

/-- The actual Jordan high frame has no more trace than the full actual force frame. -/
theorem high_frame_trace_le_full {P : Matrix n n ℂ} (hP : P.PosDef)
    (D : ι → Matrix n n ℂ) (hD : ∀ a, (D a).IsHermitian) (ε : ℝ) :
    realTrace (jordanForceFrame P (fun a => SpectralHighForcing.highForce hP.isHermitian ε (D a))) ≤
      realTrace (jordanForceFrame P D) := by
  rw [jordanForceFrame_trace hP _ (fun a => SpectralHighForcing.highForce_hermitian hP.isHermitian (hD a) ε),
    jordanForceFrame_trace hP D hD]
  change (∑ a, realTrace (P * SpectralHighForcing.highForce hP.isHermitian ε (D a) *
    SpectralHighForcing.highForce hP.isHermitian ε (D a))) ≤ ∑ a, realTrace (P * D a * D a)
  exact Finset.sum_le_sum (fun a _ => highForce_weighted_energy_le hP.posSemidef (hD a) ε)

/-- The high frame trace budget is discharged by the actual fixed-point equation. -/
theorem high_frame_trace_le {P : Matrix n n ℂ} (hP : P.PosDef)
    (D : ι → Matrix n n ℂ) (hD : ∀ a, (D a).IsHermitian)
    (hfix : krausChannel D P = P) (ε : ℝ) :
    realTrace (jordanForceFrame P (fun a => SpectralHighForcing.highForce hP.isHermitian ε (D a))) ≤
      realTrace P := by
  exact (high_frame_trace_le_full hP D hD ε).trans_eq (jordanForceFrame_trace_of_fixedPoint hP D hD hfix)

end HighFrameBudget
end MatrixSpencer
