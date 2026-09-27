import MatrixSpencer.MSManuscriptSupportedPreparation
import MatrixSpencer.MSManuscriptSupportedCap
import MatrixSpencer.OwnerCapResponse

/-! The actual returned numerical preparation supplies the physical center
response bound. This uses the original N contraction count, not the reduced
frame dimension or its weaker mixed-family norm bound. -/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.MSManuscriptPreparedResponse
open MSManuscriptSupportedOwner MSManuscriptSupportedGamma MSManuscriptSupportedPreparation
variable {N d : ℕ}
local instance : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}

def responseCap (P : Parameters N d) : ℝ :=
  (2+12*Real.sqrt (P.threshold*Real.sqrt (N:ℝ))/P.regularizer)*Real.sqrt (N:ℝ)

theorem prepared_response_le (P : Parameters N d) (hP : P.Valid) (hN : 0<N)
    (O : Owner N) (hO : State P O) (hcap : Cap P O) :
    realTrace (O.physical*ownerCoefficientResponse P.atoms hP.1 O.physical P.regularizer P.center)
      ≤responseCap P := by
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp P.physicalDimension_pos
  have hs : 0<Real.sqrt (N:ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)
  have hL : 0<P.threshold*Real.sqrt (N:ℝ) := mul_pos hP.2.2.2.2.2.1 hs
  have he : P.threshold*Real.sqrt (N:ℝ)/Real.sqrt (N:ℝ)=P.threshold :=
    mul_div_cancel_right₀ _ hs.ne'
  have hphysical : ∀u : EuclideanSpace ℝ (Fin N),
      u ∈ LinearMap.range (Matrix.toEuclideanCLM (𝕜:=ℝ) O.physical).toLinearMap →
      WithLp.ofLp u ⬝ᵥ (observedOwnedGram P.center P.atoms O.physical P.regularizer *ᵥ WithLp.ofLp u) ≤
        (P.threshold*Real.sqrt (N:ℝ)/Real.sqrt (Fintype.card (Fin N):ℝ)) *
          (WithLp.ofLp u ⬝ᵥ WithLp.ofLp u) := by
    intro u hu
    simpa only [Fintype.card_fin,he] using
      MSManuscriptSupportedCap.stored_supported_cap P.center P.atoms hP.1 O
        hP.2.2.2.1 hO.1 hP.2.2.1 hcap u hu
  simpa only [responseCap,Fintype.card_fin] using
    owner_response_le_of_ownedGram_cap P.center P.atoms hP.1 hP.2.1
      (hO.1.physical_posSemidef O hP.2.2.2.1.le) hO.2.1 hP.2.2.1 hL
      (by simpa only [Fintype.card_fin] using hN) hphysical

theorem output_response_le (P : Parameters N d) (hP : P.Valid) (hN : 0<N)
    (O : Owner N) (hO : State P O) {y : Owner N × ℕ} (ho : output P O=some y) :
    realTrace (y.1.physical*ownerCoefficientResponse P.atoms hP.1 y.1.physical P.regularizer P.center)
      ≤responseCap P := by
  have hc := output_sound P hP O hO ho
  exact prepared_response_le P hP hN y.1 (hc.state P hP hO) hc.cap

theorem responseCap_of_threshold (P : Parameters N d) {L : ℝ} (hN : 0<N)
    (ht : P.threshold=L/Real.sqrt (N:ℝ)) :
    responseCap P=(2+12*Real.sqrt L/P.regularizer)*Real.sqrt (N:ℝ) := by
  have hs : Real.sqrt (N:ℝ)≠0 := (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)).ne'
  simp only [responseCap,ht,div_mul_cancel₀ _ hs]

end MatrixSpencer.MSManuscriptPreparedResponse
