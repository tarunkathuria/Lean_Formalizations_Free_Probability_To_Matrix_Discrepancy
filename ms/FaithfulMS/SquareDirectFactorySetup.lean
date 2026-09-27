import FaithfulMS.SquareDirectCountedFactory
import MatrixSpencer.RealRAMMSEpochFactorySetup

/-! Reuse the same entrywise configuration and ordered-label restoration
circuits for the direct-density epoch. The only change is their target
factory's mathematical record. -/
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace FaithfulMS.SquareDirectFactorySetup
open MatrixSpencer RealRAM MSEpochFactorySetup MSPoint MSLabelTable PhaseRestriction MSManuscriptPhase
variable {ι : Type*} [Fintype ι] [LinearOrder ι] {d : ℕ} [Nonempty (Fin d)]
local instance : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
variable (L : Table ι) (hL : Ordered L)
  (H : selfAdjoint (Matrix (Fin d) (Fin d) ℂ)) (A : ι→Matrix (Fin d) (Fin d) ℂ)
  (hA : ∀i,(A i).IsHermitian) (hN : ∀i,‖A i‖≤1)
  (ε : ℝ) (hε : 0<ε) (hsmall : (Fintype.card ι:ℝ)*ε≤1/1000) (hd : 0<d)

def routines (x : Point (ι:=ι) ε) (hl : 32≤Fintype.card (Live x.val)) :
    SquareDirectCountedFactory.Routines H A hA hN ε hε hsmall hd x hl where
  config:=config L hL H A hA hN ε hε hsmall x hl
  config_value:=config_value L hL H A hA hN ε hε hsmall x hl
  restore:=restore L hL H A hA hN ε hε hsmall hd x hl
  restore_value:=restore_value L hL H A hA hN ε hε hsmall hd x hl

end FaithfulMS.SquareDirectFactorySetup
