import MatrixSpencer.OwnerSDPProgramSize
import MatrixSpencer.MSManuscriptCertificateReport

/-!
# Polynomial-size convex program for the square MS owner-value query

The variable covariance is an input to each query, not an optimization
variable in this density SDP. The direct pencil represents the actual
`ownerPotential` evaluated in the numerical epoch and its acceptance tests.
The empty-family specialization also represents the saved base value.

For physical dimension `d` there are `4d²-1` real variables, one real PSD
constraint of order `10d`, and `400d⁴` dense pencil entries. The final signing
algorithm uses physical dimension `2d`. A value threshold adds one scalar
affine inequality; the trace equality is already eliminated by the chart.
The theorem below connects the existing finite report to this exact maximum.
It does not assert a new runtime bound for that report implementation.
-/

open Matrix
open scoped BigOperators InnerProductSpace MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.MSManuscriptOwnerProgramSize

open KSFullManuscriptAffineData KSFullManuscriptAffineObjective
variable {N d : ℕ}

abbrev program (a : Fin d) (A : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀ i, (A i).IsHermitian) (C : Matrix (Fin N) (Fin N) ℝ) (hC : C.PosSemidef)
    (S₀ Y₀ : selfAdjoint (Matrix (Fin d) (Fin d) ℂ)) :=
  OwnerSDPProgramSize.data a A hA C hC S₀ Y₀ 0

theorem value_query_exact (a : Fin d) (H : Matrix (Fin d) (Fin d) ℂ)
    (hH : H.IsHermitian) (A : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀ i, (A i).IsHermitian) (C : Matrix (Fin N) (Fin N) ℝ) (hC : C.PosSemidef)
    (S₀ Y₀ : selfAdjoint (Matrix (Fin d) (Fin d) ℂ))
    (htr : realTrace (S₀ : Matrix (Fin d) (Fin d) ℂ) = 1)
    {θ ν : ℝ} (hθ : 0 < θ) (hν : 0 < ν) (hd : 0 < d) :
    ∃ x : Space a, x ∈ KSFullManuscriptAffinePSD.target (program a A hA C hC S₀ Y₀) ∧
      offset H θ S₀ Y₀ + ⟪coefficient a H θ, x⟫_ℝ = ownerPotential H A C θ ∧
      |KSNumericalOwnerPotential.report H A C θ hd ν -
        (offset H θ S₀ Y₀ + ⟪coefficient a H θ, x⟫_ℝ)| ≤ ν ∧
      ∀ y ∈ KSFullManuscriptAffinePSD.target (program a A hA C hC S₀ Y₀),
        offset H θ S₀ Y₀ + ⟪coefficient a H θ, y⟫_ℝ ≤
        offset H θ S₀ Y₀ + ⟪coefficient a H θ, x⟫_ℝ := by
  obtain ⟨x,hx,hv,hm⟩ := OwnerSDPProgramSize.exists_maximizer a H A hA C hC S₀ Y₀ htr hθ
  refine ⟨x,hx,hv,?_,hm⟩
  rw [hv]
  exact KSNumericalOwnerPotential.report_accuracy H hH A hA hC hθ hν hd

theorem variableCount (a : Fin d) : dimension a = 4*d^2-1 :=
  KSFullManuscriptProgramSize.variableCount a

theorem pencilOrder : matrixSize (Fin d) = 10*d :=
  KSFullManuscriptProgramSize.pencilOrder

theorem pencilEntries (a : Fin d) :
    (dimension a+1) * matrixSize (Fin d)^2 = 400*d^4 :=
  KSFullManuscriptProgramSize.pencilEntries a

theorem objectiveEntries (a : Fin d) : dimension a+1 = 4*d^2 :=
  KSFullManuscriptProgramSize.objectiveEntries a

theorem signingVariableCount (a : Fin (d+d)) : dimension a = 16*d^2-1 :=
  KSFullManuscriptProgramSize.doubledVariableCount a

theorem signingPencilOrder : matrixSize (Fin (d+d)) = 20*d :=
  KSFullManuscriptProgramSize.doubledPencilOrder

theorem signingPencilEntries (a : Fin (d+d)) :
    (dimension a+1) * matrixSize (Fin (d+d))^2 = 6400*d^4 :=
  KSFullManuscriptProgramSize.doubledPencilEntries a

end MatrixSpencer.MSManuscriptOwnerProgramSize
