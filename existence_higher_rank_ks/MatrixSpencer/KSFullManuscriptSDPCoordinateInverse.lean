import MatrixSpencer.KSFullManuscriptAffineObjective

/-! The explicit entry inverse for every numerical SDP coordinate. -/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSFullManuscriptSDPCoordinateInverse

open KSFullManuscriptSDPCoordinates KSFullManuscriptHermitianCoordinates
variable {n : Type*} [Fintype n] [LinearOrder n]

theorem encode_decode (a : n) (S₀ Y₀ : selfAdjoint (Matrix n n ℂ)) (x : Index a → ℝ) :
    KSFullManuscriptSDPCoordinates.encode a S₀ Y₀ (density a S₀ x) (regularizer a Y₀ x)
      (fidelityLinear a x) = x := by
  have hs : density a S₀ x - S₀ = densityLinear a x := by unfold density; abel
  have hy : regularizer a Y₀ x - Y₀ = regularizerLinear a x := by unfold regularizer; abel
  funext p
  rcases p with ((p | p) | (p | p))
  · change KSFullManuscriptHermitianCoordinates.encode ((density a S₀ x - S₀ : selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ) p.val = _
    rw [hs]
    change KSFullManuscriptHermitianCoordinates.encode (decode
      (KSFullManuscriptTraceCoordinates.complete a (fun q => x (.inl (.inl q))))) p.val = _
    rw [KSFullManuscriptHermitianCoordinates.encode_decode]
    simp only [KSFullManuscriptTraceCoordinates.complete, if_neg p.property, sub_zero,
      KSFullManuscriptTraceCoordinates.embed, dif_pos p.property]
  · change KSFullManuscriptHermitianCoordinates.encode ((regularizer a Y₀ x - Y₀ : selfAdjoint (Matrix n n ℂ)) : Matrix n n ℂ) p = _
    rw [hy]
    change KSFullManuscriptHermitianCoordinates.encode (decode (fun q => x (.inl (.inr q)))) p = _
    rw [KSFullManuscriptHermitianCoordinates.encode_decode]
  · change ((x (.inr (.inl p)) : ℂ) + (x (.inr (.inr p)) : ℂ) * Complex.I).re = _
    simp
  · change ((x (.inr (.inl p)) : ℂ) + (x (.inr (.inr p)) : ℂ) * Complex.I).im = _
    simp

theorem decode_injective (a : n) (S₀ Y₀ : selfAdjoint (Matrix n n ℂ)) {x y : Index a → ℝ}
    (hS : density a S₀ x = density a S₀ y) (hY : regularizer a Y₀ x = regularizer a Y₀ y)
    (hZ : fidelityLinear a x = fidelityLinear a y) : x = y := by
  rw [← encode_decode a S₀ Y₀ x, hS, hY, hZ, encode_decode]

end MatrixSpencer.KSFullManuscriptSDPCoordinateInverse
