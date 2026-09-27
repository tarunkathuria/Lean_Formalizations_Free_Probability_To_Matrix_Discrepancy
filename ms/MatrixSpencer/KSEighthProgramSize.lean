import MatrixSpencer.OwnerSDPProgramSize
import MatrixSpencer.KSEighthNumericalValue

/-!
# Polynomial-size convex program for the actual eighth-cube value query

The program uses exactly the two independent sign-block source families of
`KSEighthNumericalValue`, with `2N` source labels and physical dimension `2d`.
It has `16d²-1` real variables and one real PSD block of order `20d`, hence
`6400d⁴` dense pencil entries. Source labels remain tied to the original
owner weights; they are not separate sign variables. Masked and truncated
owner reports are instances of the arbitrary nonnegative weights below.

The unchanged finite projected-gradient report is proved accurate against
this exact SDP maximum. Polynomial size of an equivalent value problem does
not by itself count all calls or prove a runtime bound for that implementation.
-/

open Matrix
open scoped BigOperators InnerProductSpace MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSEighthProgramSize

open KSFullManuscriptAffineData KSFullManuscriptAffineObjective
open KSEighthNumericalValue KSPotentialModels
variable {N d : ℕ}

abbrev program (a : Fin (d+d)) (v : Fin N → Fin d → ℂ)
    (c : Fin N → ℝ) (hc : ∀ i, 0 ≤ c i)
    (S₀ Y₀ : selfAdjoint (Matrix (Fin (d+d)) (Fin (d+d)) ℂ)) :=
  OwnerSDPProgramSize.data a (physicalFamily v) (physicalFamily_isHermitian v)
    (KSIndependentSource.coefficientCovariance c)
    (KSIndependentSource.coefficientCovariance_posSemidef hc) S₀ Y₀ 0

theorem physical_owner_eq (v : Fin N → Fin d → ℂ) (c : Fin N → ℝ)
    (hc : ∀ i, 0 ≤ c i) (x : Fin N → ℝ) {θ : ℝ} (hθ : 0 < θ) (hd : 0 < d) :
    ownerPotential (physicalCenter v x) (physicalFamily v)
      (KSIndependentSource.coefficientCovariance c) θ =
      commonPotential (fun i => KSRankOne.atom (v i)) θ x c := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  have he := KSOwnerReindex.ownerPotential_reindex
    (signedLift (center (fun i => KSRankOne.atom (v i)) x))
    (KSIndependentSource.family (fun i => KSRankOne.atom (v i)))
    (KSIndependentSource.family_isHermitian _ (fun i => KSRankOne.atom_isHermitian (v i)))
    (KSIndependentSource.coefficientCovariance_posSemidef hc) θ (blockIndex d)
  change ownerPotential (physicalCenter v x) (physicalFamily v)
    (KSIndependentSource.coefficientCovariance c) θ = _ at he
  rw [he, commonPotential, KSCommonSource.potential_eq_independent _ _
    (fun i => KSRankOne.atom_isHermitian (v i)) hc hθ]

theorem value_query_exact (a : Fin (d+d)) (v : Fin N → Fin d → ℂ)
    (c : Fin N → ℝ) (hc : ∀ i, 0 ≤ c i) (x : Fin N → ℝ)
    (S₀ Y₀ : selfAdjoint (Matrix (Fin (d+d)) (Fin (d+d)) ℂ))
    (htr : realTrace (S₀ : Matrix (Fin (d+d)) (Fin (d+d)) ℂ) = 1)
    {θ ν : ℝ} (hθ : 0 < θ) (hν : 0 < ν) (hd : 0 < d) :
    ∃ z : Space a, z ∈ KSFullManuscriptAffinePSD.target (program a v c hc S₀ Y₀) ∧
      offset (physicalCenter v x) θ S₀ Y₀ + ⟪coefficient a (physicalCenter v x) θ,z⟫_ℝ =
        commonPotential (fun i => KSRankOne.atom (v i)) θ x c ∧
      |ownerReport v θ hd c ν x -
        (offset (physicalCenter v x) θ S₀ Y₀ + ⟪coefficient a (physicalCenter v x) θ,z⟫_ℝ)| ≤ ν ∧
      ∀ y ∈ KSFullManuscriptAffinePSD.target (program a v c hc S₀ Y₀),
        offset (physicalCenter v x) θ S₀ Y₀ + ⟪coefficient a (physicalCenter v x) θ,y⟫_ℝ ≤
        offset (physicalCenter v x) θ S₀ Y₀ + ⟪coefficient a (physicalCenter v x) θ,z⟫_ℝ := by
  obtain ⟨z,hz,hv,hm⟩ := OwnerSDPProgramSize.exists_maximizer a (physicalCenter v x)
    (physicalFamily v) (physicalFamily_isHermitian v)
    (KSIndependentSource.coefficientCovariance c)
    (KSIndependentSource.coefficientCovariance_posSemidef hc) S₀ Y₀ htr hθ
  rw [physical_owner_eq v c hc x hθ hd] at hv
  refine ⟨z,hz,hv,?_,hm⟩
  rw [hv]
  exact ownerReport_accuracy v hθ hν hd c hc x

theorem variableCount (a : Fin (d+d)) : dimension a = 16*d^2-1 :=
  KSFullManuscriptProgramSize.doubledVariableCount a

theorem pencilOrder : matrixSize (Fin (d+d)) = 20*d :=
  KSFullManuscriptProgramSize.doubledPencilOrder

theorem pencilEntries (a : Fin (d+d)) :
    (dimension a+1) * matrixSize (Fin (d+d))^2 = 6400*d^4 :=
  KSFullManuscriptProgramSize.doubledPencilEntries a

theorem objectiveEntries (a : Fin (d+d)) : dimension a+1 = 16*d^2 := by
  rw [KSFullManuscriptProgramSize.objectiveEntries]
  ring

theorem sourceLabelCount (N : ℕ) : Fintype.card (Fin N × Bool) = 2*N := by
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  omega

end MatrixSpencer.KSEighthProgramSize
