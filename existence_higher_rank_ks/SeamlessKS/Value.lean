import SeamlessKS.StatePotential
import MatrixSpencer.KSPolynomialConvexSolver

/-! Materialized SDP value queries for the actual smooth-source potential.
The only external accuracy contract is the general affine SDP solver. -/
open Matrix Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace SeamlessKS.Value
open MatrixSpencer SeamlessKS.StatePotential

variable {N : ℕ} {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
local instance {k : Type*} [Fintype k] [DecidableEq k] : CStarAlgebra (Matrix k k ℂ) := {}

def origin : Fin (Fintype.card (n ⊕ n)) := ⟨0,Fintype.card_pos⟩

/-- Canonical physical block order: the left copy precedes the right copy.
This uses only a comparison and subtraction on natural indices. -/
def blockIndex (d : ℕ) : Fin (Fintype.card (Fin d ⊕ Fin d)) ≃ (Fin d ⊕ Fin d) :=
  (finCongr (by simp : Fintype.card (Fin d ⊕ Fin d)=d+d)).trans finSumFinEquiv.symm

variable {d : ℕ} [Nonempty (Fin d)]

def report (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ)
    (B : Matrix (Fin d) (Fin d) ℂ) (θ ζ ν : ℝ) (x : Fin N → ℝ) : ℝ := by
  classical
  exact if hx : x ∈ ksCube 1 then
    KSConvexValueOracle.reindexedOwnerReport O (origin (n:=Fin d)) (blockIndex d)
      (KSDebitCenter.center (signedSum v x) B)
      (KSSpinSource.family (fun i => KSRankOne.atom (v i)))
      (KSSpinSource.family_isHermitian _ (fun i => KSRankOne.atom_isHermitian (v i)))
      (KSSpinSource.coefficientCovariance (SourceTransport.smoothWeights ζ x))
      (KSSpinSource.coefficientCovariance_posSemidef
        (fun i => Source.weight_nonneg (by norm_num) (abs_le.mpr ⟨hx.1 i,hx.2 i⟩)))
      Fintype.card_pos θ ν
    else 0

theorem report_accuracy (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ)
    (B : Matrix (Fin d) (Fin d) ℂ) {θ ζ ν : ℝ} (hθ : 0 < θ) (hν : 0 < ν)
    (x : Fin N → ℝ) (hx : x ∈ ksCube 1) :
    |report O v B θ ζ ν x-
      KSDebitPotential.potential (signedSum v x) B v (SourceTransport.smoothWeights ζ x) θ|≤ν := by
  classical
  rw [report,dif_pos hx]
  exact KSConvexValueOracle.reindexedOwnerReport_accuracy O (origin (n:=Fin d))
    (blockIndex d) _ _ _ _ _ Fintype.card_pos hθ hν

theorem state_report_accuracy (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ)
    {ρ θ ζ ν : ℝ} (hθ : 0 < θ) (hν : 0 < ν) (s : State.CubeState N ρ) :
    |report O v 0 θ ζ ν s.coeff-potential v θ ζ s|≤ν :=
  report_accuracy O v 0 hθ hν s.coeff s.cube

/-- Numerical acceptance can charge its proved error to the allowed local drift. -/
theorem accepted_local_increase {old candidate oldReport candidateReport ν : ℝ}
    (hold : |oldReport-old|≤ν) (hnew : |candidateReport-candidate|≤ν)
    (haccept : candidateReport-oldReport≤2*ν) : candidate≤old+4*ν := by
  rcases abs_le.mp hold with ⟨hol,hou⟩
  rcases abs_le.mp hnew with ⟨hnl,hnu⟩
  linarith

/-- A rejected nearby test implies a strict increase of the true potential. -/
theorem rejected_local_increases {old candidate oldReport candidateReport ν : ℝ}
    (hold : |oldReport-old|≤ν) (hnew : |candidateReport-candidate|≤ν)
    (hreject : 2*ν<candidateReport-oldReport) : old<candidate := by
  rcases abs_le.mp hold with ⟨hol,hou⟩
  rcases abs_le.mp hnew with ⟨hnl,hnu⟩
  linarith

end SeamlessKS.Value
