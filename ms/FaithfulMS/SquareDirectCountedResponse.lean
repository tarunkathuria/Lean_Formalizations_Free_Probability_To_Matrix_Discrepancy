import FaithfulMS.SquareDirectCountedPreparation
import FaithfulMS.DirectSDPArithmetic
import FaithfulMS.DirectGammaArithmetic
import MatrixSpencer.RealRAMMSOwnerReport

/-! The response evaluator is an actual affine SDP solve followed by the
verified transport and Gram calculation. The density returned by the SDP
is the only optimizer information consumed by preparation. -/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace FaithfulMS.SquareDirectCountedResponse
open MatrixSpencer RealRAM
open RealRAM.JacobiIteration (Counted)
open MSManuscriptSupportedGamma MSManuscriptSupportedOwner MSManuscriptSupportedPreparation
variable {N d : ℕ}
local instance : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1800000
set_option maxRecDepth 5000

variable (P : DirectSDP.PolynomialService)

def compute (p : Parameters N d) (O : Owner N) : Counted (Matrix (Fin O.dim) (Fin O.dim) ℝ) :=
  if h : p.Valid ∧ O.Valid p.floor then
    letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp p.physicalDimension_pos
    let f := MSOwnerReport.family p.atoms O.frame
    have hf : ∀i,(f.value i).IsHermitian := by
      rw [MSOwnerReport.family_value]
      exact family_isHermitian p h.1 O
    have hc := h.2.matrix_posSemidef O h.1.2.2.2.1.le
    let s := DirectSDPArithmetic.square P p.center f.value hf O.matrix hc
      p.physicalDimension_pos p.regularizer
    have hs : s.value.density.PosDef := by
      dsimp only [s]
      rw [DirectSDPArithmetic.square_density _ _ _ _ _ _ _ _ h.1.2.2.1,
        DirectDensity.SquareSolution.density_eq_optimizer _ h.1.2.2.1]
      exact densityOptimizer_posDef _ _ h.1.2.2.1
    let g := DirectGammaArithmetic.compute f.value hf O.matrix hc s.value.density hs
    ⟨g.value,f.cost+s.cost+g.cost+2⟩
  else ⟨0,1⟩

theorem compute_value (p : Parameters N d) (O : Owner N) :
    (compute P p O).value = @SquareDirectGamma.response ⟨P.service⟩ N d p O := by
  unfold compute SquareDirectGamma.response
  split_ifs with h
  · simp only [DirectGammaArithmetic.compute_value,DirectSDPArithmetic.square_density _ _ _ _ _ _ _ _ h.1.2.2.1,
      MSOwnerReport.family_value]
    rfl
  · rfl

def evaluator (p : Parameters N d) : @SquareDirectCountedPreparation.Evaluator ⟨P.service⟩ N d p := by
  letI : SquareDirectOracle.Oracle := ⟨P.service⟩
  exact ⟨compute P p,fun O _ => compute_value P p O⟩

def work (P : DirectSDP.PolynomialService) (N d : ℕ) : ℕ :=
  N*d*d*(8*N+4)+1+DirectSDPArithmetic.squareCost P N d+20000*(N+d+1)^6+2

theorem compute_cost (p : Parameters N d) (O : Owner N) (hO : O.dim ≤ N) :
    (compute P p O).cost ≤ work P N d := by
  unfold compute
  split_ifs with h
  · letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp p.physicalDimension_pos
    let f := MSOwnerReport.family p.atoms O.frame
    have hfA : ∀i,(f.value i).IsHermitian := by
      rw [MSOwnerReport.family_value]
      exact family_isHermitian p h.1 O
    have hc := h.2.matrix_posSemidef O h.1.2.2.2.1.le
    let q := DirectSDPArithmetic.square P p.center f.value hfA O.matrix hc
      p.physicalDimension_pos p.regularizer
    have hq : q.value.density.PosDef := by
      dsimp only [q]
      rw [DirectSDPArithmetic.square_density _ _ _ _ _ _ _ _ h.1.2.2.1,
        DirectDensity.SquareSolution.density_eq_optimizer _ h.1.2.2.1]
      exact densityOptimizer_posDef _ _ h.1.2.2.1
    let g := DirectGammaArithmetic.compute f.value hfA O.matrix hc q.value.density hq
    change f.cost+q.cost+g.cost+2 ≤ _
    have hf := MSOwnerReport.family_cost p.atoms O.frame
    change f.cost = _ at hf
    have hs := DirectSDPArithmetic.square_cost_le P p.center f.value hfA O.matrix hc
      p.physicalDimension_pos p.regularizer
    change q.cost ≤ _ at hs
    have hg := (DirectGammaArithmetic.compute_cost f.value hfA O.matrix hc q.value.density hq).trans
      (DirectGammaArithmetic.arithmeticBudget_polynomial O.dim d)
    change g.cost ≤ _ at hg
    simp only [Fintype.card_fin] at hs
    have hsmono : DirectSDPArithmetic.squareCost P O.dim d ≤
        DirectSDPArithmetic.squareCost P N d := by
      unfold DirectSDPArithmetic.squareCost
      gcongr
    have hfm : O.dim*d*d*(8*N+4) ≤ N*d*d*(8*N+4) := by gcongr
    have hgm : 20000*(O.dim+d+1)^6 ≤ 20000*(N+d+1)^6 := by gcongr
    unfold work
    omega
  · dsimp only
    unfold work
    omega

theorem evaluator_cost (p : Parameters N d) (O : Owner N) (hO : State p O) :
    letI : SquareDirectOracle.Oracle := ⟨P.service⟩
    ((evaluator P p).response O).cost ≤ work P N d := by
  letI : SquareDirectOracle.Oracle := ⟨P.service⟩
  exact compute_cost P p O hO.2.2

theorem work_mono {m N d : ℕ} (h : m ≤ N) : work P m d ≤ work P N d := by
  unfold work DirectSDPArithmetic.squareCost
  gcongr

end FaithfulMS.SquareDirectCountedResponse
